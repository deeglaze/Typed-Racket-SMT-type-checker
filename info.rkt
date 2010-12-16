#lang setup/infotab
(define name "SMT-solver")
(define blurb
  (list "An implementation of the DPLL(T) framework."))
(define scribblings '(["scribblings/smt-solver.scrbl" (multi-page)]))
(define categories '(devtools misc))
(define primary-file "smt-solve.rkt")
(define compile-omit-paths '())
(define repositories '("4.x"))

(define release-notes
  '((p "0.1 (1 0) - first release")))

(define required-core-version "4.0")
(define version "0.1")
