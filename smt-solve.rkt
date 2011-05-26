#lang racket

(require "bcp.rkt"
	 "data-structures.rkt"
	 "learned-clauses.rkt"
	 "statistics.rkt"
	 "sat-heuristics.rkt"
         "heuristic-constants.rkt"
	 "smt-interface.rkt"
	 "dimacs.rkt"
	 "debug.rkt")
(require rackunit)

(provide smt-solve
	 smt-assign
	 smt-decide
	 sat-solve
	 sat-assign
	 sat-decide)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initialization method(s)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; precondition: (dimacscnf? cnf) = #t
(define (initialize cnf t-state strength [seed #f])
  (match cnf
   ;; dimacs-style:
   [`(,var-count ,clause-count ((,lit ...) ...))
    (let ((vars (make-n-vars var-count)))
      (SMT (SAT (dimacs-cnf->clauses clause-count vars lit)
		(empty-learned-clauses)
		vars
		'(())
		(init-stats))
	   t-state
	   strength
	   seed))]))

;; kill all assignments and start again. Only works if we have randomness in our
;; variable choice
(define (restart smt)
  (obliterate-partial-assignment! (SMT-partial-assignment smt))
  (SMT (SAT (SMT-clauses smt)
	    (SMT-learned-clauses smt)
	    (SMT-variables smt)
	    '(())
	    (reset-stats (SMT-statistics smt)))
       ((T-Restart) (SMT-T-State smt))
       (SMT-strength smt)
       (SMT-seed smt)))

(define (obliterate-partial-assignment! pa)
  (cond [(empty? pa) (void)]
	[else (for-each restart-lit! (first pa))
	      (obliterate-partial-assignment! (rest pa))]))

(define (restart-lit! lit)
  (let ((var (literal-var lit)))
    (begin (obliterate-lit! lit)
	   (set-var-pos-activation! var 0.0)
	   (set-var-neg-activation! var 0.0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Learning from the T-solver
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-T-solver-blessing smt)
  (let*-values ([(t-state consistent) ((T-Consistent?) (SMT-T-State smt) +inf.0)]
                [(smt) (new-T-State smt t-state)]
                ;; continue past this and we have a true satisfying assignment
                [(smt) (resolve!-or-continue smt t-state consistent)])
    (raise (sat-exn smt))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Literal choice functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; choose-in-order : Vector<Var> -> Literal
; XXX: Not amenable to random restarts!
(define (choose-in-order smt)
  (let ((vars (SMT-variables smt)))
    (let keep-looking ((idx 0))
      (if (= idx (vector-length vars))
	  (get-T-solver-blessing smt)
	  (let ((var (vector-ref vars idx)))
	    (if (var-unassigned? var)
		(literal var #t)
		(keep-looking (+ 1 idx))))))))

; vsids : SMT -> Literal
(define (vsids smt)
  (let ([vars (SMT-variables smt)])
    (if ((random) . < . RANDOM_DECISION_COEFFICIENT)
        (choose-random-unassigned-literal smt vars)
        (vsids-search smt vars 0 #f -1))))

(define (choose-random-unassigned-literal smt vars)
  (let ((unassigned (vector-filter var-unassigned? vars)))
    (if (zero? (vector-length unassigned))
        (get-T-solver-blessing smt)
        (literal (vector-ref unassigned (random (vector-length unassigned)))
             (= 0 (random 2))))))

;; vsids-search : Index * Option var * Integer -> Literal
(define (vsids-search smt vars idx candidate best)
  (if (idx . < . (vector-length vars))
      (let* ([var (vector-ref vars idx)]
             [score (+ (var-pos-activation var)
                       (var-neg-activation var))])
        (if (var-unassigned? var)
            (cond [(score . > .  best)
                   (vsids-search smt vars (add1 idx) var score)]
                  [else (vsids-search smt  vars (add1 idx) candidate best)])
            (vsids-search smt vars (add1 idx) candidate best)))
      (if (not candidate)
          ;; no candidates for assigning. We're done if T-solver says so.
          (get-T-solver-blessing smt)
          ;; Found the best candidate!
          (cond [((var-pos-activation candidate)
                  . > . 
                  (var-neg-activation candidate))
                 (literal candidate #t)]
                [else (literal candidate #f)]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Solver core
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (decide smt literal)
  ;; if interacting at the REPL, here is where we should check 
  ;; that ~literal isn't already assigned.
  (let* ((smt (SMT-set-decision-level smt (+ 1 (SMT-decision-level smt))))
	 (smt (SMT-set-partial-assignment smt (cons '() (SMT-partial-assignment smt)))))
    (propagate-assignment smt literal #f)))

;; do the decision loop
(define (smt-search smt [choose-literal vsids])
  (let keep-solving ([smt smt #;(initial-bcp smt)])
    (keep-solving 
     (with-handlers
      ;; if propagate-assignment backjumps, we do nothing. 
      ;; Just control to stop propagation.
      ([bail-exn? (lambda (x) (bail-exn-smt x))]
       [restart-exn? (lambda (x) (restart (restart-exn-smt x)))])
      (decide smt (choose-literal smt))))))

;; start a SMT instance and return the final state
(define (smt-solve cnf t-state strength [seed #f] [choose-literal vsids])
  (if seed
      (random-seed seed)
      (with-handlers 
       ([sat-exn? (lambda (x) (debug "SAT" (SMT-partial-assignment (sat-exn-smt x))) x)]
	[unsat-exn? (lambda (x) (debug "UNSAT" (SMT-partial-assignment (unsat-exn-smt x))) x)])
       (smt-search (initialize cnf t-state strength) choose-literal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Derived, useful interfaces for SMT and SAT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (extract-public-partial-assignment smt)
  (filter-map (λ (v) (and (not (var-unassigned? v))
			  (var->dimacs v)))
	      (vector->list (SMT-variables (sat-exn-smt smt)))))

(define (smt-assign cnf t-state strength [seed #f] [choose-literal vsids])
  (match (smt-solve cnf t-state strength seed choose-literal)
    [(? sat-exn? smt) (extract-public-partial-assignment smt)]
    [(? unsat-exn? smt) 'UNSAT]))

;; start an SMT instance and simply say yes/no
(define (smt-decide cnf t-state strength [seed #f] [choose-literal vsids])
  (match (smt-solve cnf t-state strength seed choose-literal)
    [(? sat-exn? smt) 'SAT]
    [(? unsat-exn? smt) 'UNSAT]))

;; For propositional logic, the T-Solver is trivial
(define (sat-solve cnf [seed #f] [choose-literal vsids])
  (parameterize ([T-Satisfy sat-satisfy]
                 [T-Propagate sat-propagate]
                 [T-Explain sat-explain]
                 [T-Consistent? sat-consistent?]
                 [T-Backjump sat-backjump])
    (smt-solve cnf #f 0 seed choose-literal)))

(define (sat-decide cnf [seed #f] [choose-literal vsids])
  (match (sat-solve cnf seed choose-literal)
    [(? sat-exn? smt) 'SAT]
    [(? unsat-exn? smt) 'UNSAT]))

(define (sat-assign cnf [seed #f] [choose-literal vsids])
  (match (sat-solve cnf seed choose-literal)
    [(? sat-exn? smt) (extract-public-partial-assignment smt)]
    [(? unsat-exn? smt) 'UNSAT]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A few sanity checks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check equal?
       (sat-decide '(1 2 ((1) (-1))))
       'UNSAT)

(check equal? 
       (sat-decide '(5 5 ((-1 2) (-1 3) (-2 4) (-3 -4) (1 -3 5))))
       'SAT)

(check equal?
       (sat-decide '(6 7 ((1 2) (2 3) (-1 -4 5) (-1 4 6) (-1 -5 6) (-1 4 -6) (-1 -5 -6))))
       'SAT)
