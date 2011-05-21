#lang racket

(require (planet "smt-solve.rkt" ("ianj" "smt-solver.plt" 1 3))
         (planet "dimacs.rkt"  ("ianj" "smt-solver.plt" 1 3))
         (planet "smt-interface.rkt"  ("ianj" "smt-solver.plt" 1 3))
         "mergeprop.rkt")         

(define (qfeuf-satisfy t-state literal)
  ...)

(define (qfeuf-propagate t-state strength dimacslit)
  ...)

(define (qfeuf-explain t-state strength lit)
  ...)

(define (qfeuf-consistent? t-state strength)
  ...)

(define (qfeuf-backjump t-state backjump-by-sats)
  ...)

(define (qfeuf-restart t-state)
  ...)