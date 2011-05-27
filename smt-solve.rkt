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
    (let ([vars (make-n-vars var-count)])
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
  (kill-vars-activation! (SMT-variables smt))
  (SMT (SAT (SMT-clauses smt)
            (SMT-learned-clauses smt)
            (bthash-backtrack-to (SMT-variables smt) 0)
            '(0)
            (reset-stats (SMT-statistics smt)))
       ((T-Restart) (SMT-T-State smt))
       (SMT-strength smt)
       (SMT-seed smt)))

(define (kill-vars-activation! vars)
  (for ([(vid var) (bthash-iterate-first vars)])
    (set-var-heuristic-pos-activation! (var-heuristic var) 0.0)
    (set-var-heuristic-neg-activation! (var-heuristic var) 0.0)))
        

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Learning from the T-solver
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-T-solver-blessing smt)
  (let*-values ([(t-state consistent) ((T-Consistent?) (SMT-T-State smt) +inf.0)]
                [(smt) (set-SMT-T-State smt t-state)]
                ;; continue past this and we have a true satisfying assignment
                [(smt) (resolve-or-continue smt t-state consistent)])
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
  (let ([unassigned (vector-filter var-unassigned? vars)])
    (if (zero? (vector-length unassigned))
        (get-T-solver-blessing smt)
        (literal (vector-ref unassigned (random (vector-length unassigned)))
                 (= 0 (random 2))))))

;; vsids-search : Index * Option var * Integer -> Literal
(define (vsids-search smt vars idx candidate best)
  (cond [(idx . < . (vector-length vars))
         (let* ([var (vector-ref vars idx)]
                [score (+ (var-pos-activation var)
                          (var-neg-activation var))])
           (if (var-unassigned? var)
               (cond [(score . > .  best)
                      (vsids-search smt vars (add1 idx) var score)]
                     [else (vsids-search smt vars (add1 idx) candidate best)])
               (vsids-search smt vars (add1 idx) candidate best)))]
        [(not candidate)
          ;; no candidates for assigning. We're done if T-solver says so.
         (get-T-solver-blessing smt)]
        ;; Found the best candidate!
        [else
         (literal candidate
                  ;; literal polarity depends on activation levels
                  ((var-pos-activation candidate)
                   . > . 
                   (var-neg-activation candidate)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Solver core
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (decide smt literal)
  ;; if interacting at the REPL, here is where we should check 
  ;; that ~literal isn't already assigned.
  (let* ([dec-lev (add1 (SMT-decision-level smt))]
         [smt (set-SMT-decision-level smt dec-lev)]
	 [smt (set-SMT-sats-per-dec-lev smt (cons 0 (SMT-sats-per-dec-lev smt)))]
         [smt (set-SMT-variables smt (bthash-new-age (SMT-variables smt) dec-lev))])
    (propagate-assignment smt literal #f)))

;; do the decision loop
(define (smt-search smt [choose-literal vsids])
  (with-handlers
   ;; if propagate-assignment backjumps, we do nothing. 
   ;; Just control to stop propagation.
   ([bail-exn? (lambda (x) (bail-exn-smt x))]
    [restart-exn? (lambda (x) (restart (restart-exn-smt x)))])
   (let keep-solving ([smt smt]) ;; loop until raise
     (keep-solving (decide smt (choose-literal smt))))))

;; start a SMT instance and return the final state
(define (smt-solve cnf t-state strength [seed #f] [choose-literal vsids])
  (when seed
        (random-seed seed))
  (with-handlers 
   ([sat-exn? (lambda (x) x)]
    [unsat-exn? (lambda (x) x)])
   (smt-search (initialize cnf t-state strength) choose-literal)))

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
