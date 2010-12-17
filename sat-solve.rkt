#lang racket

(require "dimacs.rkt")
(require "smt-solve.rkt")

;; For users that want only DIMACS CNF solving from stdin.
(time (sat-decide (read-dimacs)))
