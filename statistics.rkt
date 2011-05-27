#lang racket

(require "heuristic-constants.rkt"
         "struct-with-set.rkt")

(provide (all-defined-out))

(struct-with-set SAT-Stats (decision-level 
                            assigned-order 
                            conflicts-since-last-restart
                            forget-threshold restart-threshold
                            #;satisfied-clauses))

(define (inc-assigned-order stats)
  (set-SAT-Stats-assigned-order stats (add1 (SAT-Stats-assigned-order stats))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Specialized setters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (init-stats)
  (SAT-Stats 0 
	     0
	     0
	     FORGET_THRESHOLD_INITIAL_PERCENTAGE
             RESTART_INITIAL_THRESHOLD))

(define (reset-stats stats)
  (SAT-Stats 0 
	     0
	     0
	     (SAT-Stats-forget-threshold stats)
             (SAT-Stats-restart-threshold stats)))