#lang racket

(provide (all-defined-out))

(struct unsat-exn (smt))
(struct sat-exn (smt))

;; The interface for describing variables will be their dimacs-lit.
(define (strength? x)
  (or (exact-nonnegative-integer? x)
      (eqv? x +inf.0)))

(define sat-satisfy (lambda (t-state literal) t-state))
;; T-Satisfy: T-state * Literal -> T-state
;; a literal has been satisfied
(define T-Satisfy (make-parameter sat-satisfy))

(define sat-propagate (lambda (t-state strength dimacslit) (values t-state empty)))
;; what literals can be satisfied?
(define T-Propagate (make-parameter sat-propagate))

(define sat-explain (lambda (t-state strength lit) (error "[internal error] T-propogation shouldn't have happened")))
;; why was this able to be satisfied?
(define T-Explain (make-parameter sat-explain))

(define sat-consistent? (lambda (t-state strength) #t))
;; Is the current assignment consistent? If not, why not?
(define T-Consistent? (make-parameter sat-consistent?))

(define sat-backjump (lambda (t-state backjump-by-sats) #f))
;; What is the starting state for the T-solver with this problem?
(define T-Backjump (make-parameter sat-backjump))

(define sat-restart (lambda (t-state) t-state))
;; The solver has reset its assignment. T-solver should as well.
(define T-Restart (make-parameter sat-restart))