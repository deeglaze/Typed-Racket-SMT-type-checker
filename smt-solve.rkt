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
      (SMT (SAT (list->vector (map (dimacs-lits->clause vars) lit)) ;; XXX: Could use clause-count for no intermediate list
		(empty-learned-clauses)
		vars
		'(())
		(SAT-Stats 0 ;; decision level
			   0 ;; assigned order
			   FORGET_THRESHOLD_INITIAL_PERCENTAGE
			   RESTART_INITIAL_THRESHOLD
			   0)) ;; conflicts since last restart
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
	    (SAT-Stats 0 ;; decision level
		       0 ;; assigned order
		       (SMT-forget-threshold smt)
		       (SMT-restart-threshold smt)
		       0)) ;; conflicts since last restart
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
(define (vars->clause-of-not-and vars)
  (let* ((negate-assigned
	  (map (lambda (v)
		 (literal v (not (var-value v))))
		 vars))
	 (clause-list (list->vector negate-assigned)))
  (clause clause-list
	  (vector-ref clause-list 0)
	  (vector-ref clause-list (+ -1 (vector-length clause-list))))))

(define (not-partial-assignment smt)
  (vars->clause-of-not-and (filter-not var-unassigned? 
				       (vector->list (SMT-variables smt)))))

(define (get-T-solver-blessing smt)
  (let ((consistent ((T-Consistent?) (SMT-T-State smt) +inf.0)))
    (match consistent
      [#t (raise (sat-exn smt))] ;; got the blessing
      [#f ;; most unhelpful. We have to learn the negation of the current PA
       (debug "inconsistent" (not-partial-assignment smt))
       (resolve-conflict! smt (not-partial-assignment smt))]
      [explanation ;; Have an explanation of inconsistency.
       (resolve-conflict! smt (vars->clause-of-not-and explanation))])))

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
  (let ((vars (SMT-variables smt)))
    (let keep-looking ((idx 0) (candidate #f) (best -1))
      (if (idx . < . (vector-length vars))
	  (let* ((var (vector-ref vars idx))
		 (score (+ (var-pos-activation var)
			   (var-neg-activation var))))
	    (if (var-unassigned? var)
		(cond [(score . > .  best)
		       (keep-looking (+ 1 idx) var score)]
		      [(= score best)
		       (if (= 0 (random 2))
			   (keep-looking (+ 1 idx) var score)
			   (keep-looking (+ 1 idx) candidate score))]
		      [else (keep-looking (+ 1 idx) candidate best)])
		(keep-looking (+ 1 idx) candidate best)))
	  (if (not candidate)
	      ;; no candidates for assigning. We're done if T-solver says so.
	      (get-T-solver-blessing smt)
	      ;; Found the best candidate!
	      (cond [((var-pos-activation candidate)
		      . > . 
		      (var-neg-activation candidate))
		     (literal candidate #t)]
		    [(= (var-pos-activation candidate) 
			(var-neg-activation candidate))
		     (literal candidate (= 0 (random 2)))]
		    [else (literal candidate #f)]))))))

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
  (let keep-solving ((smt (initial-bcp smt)))
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
