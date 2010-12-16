#lang racket

(require "bcp.rkt")
(require "data-structures.rkt")
(require "smt-interface.rkt")
(require "dimacs.rkt")
(require "debug.rkt")
(require rackunit)

(provide smt-solve
	 smt-assign
	 smt-decide
	 sat-solve
	 sat-assign
	 sat-decide)

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

(define (decide smt literal)
  ;; if interacting at the REPL, here is where we should check 
  ;; that ~literal isn't already assigned.
  (let* ((smt (SMT-set-decision-level smt (+ 1 (SMT-decision-level smt))))
	 (smt (SMT-set-partial-assignment smt (cons '() (SMT-partial-assignment smt)))))
    (propagate-assignment smt literal #f)))


; choose-in-order : Vector<Var> -> Literal
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
	    (if (and (var-unassigned? var)
		     (score . > .  best))
		(keep-looking (+ 1 idx) var score)
		(keep-looking (+ 1 idx) candidate best)))
	  (if (not candidate)
	      ;; no candidates for assigning. We're done if T-solver says so.
	      (get-T-solver-blessing smt)
	      ;; Found the best candidate!
	      (literal candidate
		       ((var-pos-activation candidate) . >= . (var-neg-activation candidate))))))))

;; do the decision loop
(define (smt-search smt [choose-literal vsids])
  (let keep-solving ((smt (initial-bcp smt)))
    (keep-solving 
     (with-handlers
      ;; if propagate-assignment backjumps, we do nothing. 
      ;; Just control to stop propagation.
      ([bail-exn? (lambda (x) (bail-exn-smt x))])
      (decide smt (choose-literal smt))))))

;; start a SMT instance and return the final state
(define (smt-solve cnf t-state strength [choose-literal vsids])
  (with-handlers 
   ([sat-exn? (lambda (x) (debug "SAT" (SMT-partial-assignment (sat-exn-smt x))) x)]
    [unsat-exn? (lambda (x) (debug "UNSAT" (SMT-partial-assignment (unsat-exn-smt x))) x)])
   (smt-search (initialize cnf t-state strength) choose-literal)))

;; For propositional logic, the T-Solver is trivial
(define (sat-solve cnf [choose-literal vsids])
  (parameterize ([T-Satisfy sat-satisfy]
                 [T-Propagate sat-propagate]
                 [T-Explain sat-explain]
                 [T-Consistent? sat-consistent?]
                 [T-Backjump sat-backjump])
    (smt-solve cnf #f choose-literal)))

;; start a SAT instance and simply say yes/no
(define (smt-decide cnf t-state strength [choose-literal vsids])
  (match (smt-solve cnf t-state choose-literal)
    [(? sat-exn? smt) 'SAT]
    [(? unsat-exn? smt) 'UNSAT]))

(define (sat-decide cnf [choose-literal vsids])
  (match (sat-solve cnf choose-literal)
    [(? sat-exn? smt) 'SAT]
    [(? unsat-exn? smt) 'UNSAT]))

(define (extract-public-partial-assignment smt)
  (filter-map (λ (v) (and (not (var-unassigned? v))
			  (var->dimacs v)))
	      (vector->list (SMT-variables (sat-exn-smt smt)))))

(define (smt-assign cnf t-state strength [choose-literal vsids])
  (match (smt-solve cnf t-state strength choose-literal)
    [(? sat-exn? smt) (extract-public-partial-assignment smt)]
    [(? unsat-exn? smt) 'UNSAT]))

(define (sat-assign cnf [choose-literal vsids])
  (match (sat-solve cnf choose-literal)
    [(? sat-exn? smt) (extract-public-partial-assignment smt)]
    [(? unsat-exn? smt) 'UNSAT]))



(check equal?
       (sat-decide '(1 2 ((1) (-1))))
       'UNSAT)

(check equal? 
       (sat-decide '(5 5 ((-1 2) (-1 3) (-2 4) (-3 -4) (1 -3 5))))
       'SAT)

(check equal?
       (sat-decide '(6 7 ((1 2) (2 3) (-1 -4 5) (-1 4 6) (-1 -5 6) (-1 4 -6) (-1 -5 -6))))
       'SAT)
#|
(check equal? 
       (with-handlers ([(lambda (x) (eqv? x 'bail)) (lambda (x) 'bailed)]
		       [(lambda (x) (eqv? x 'unsat)) (lambda (x) 'unsat)])
		      (initialize! (list 5 ; A B C D E
					 5 ; -A B ^ -A C ^ -B D ^ -C -D ^ A -C E
					 '((-1 2)
					   (-1 3)
					   (-2 4)
					   (-3 -4)
					   (1 -3 5))))
		      (initial-bcp)
		      (decide (literal (vector-ref variables 0) #t)))
       'bailed)
|#

;; Actual entry-point

(time (sat-decide (read-dimacs)))
