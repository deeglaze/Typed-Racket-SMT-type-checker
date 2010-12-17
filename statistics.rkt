#lang racket

(require "heuristic-constants.rkt")

(provide (all-defined-out))

(struct SAT-Stats (decision-level 
		   assigned-order 
		   conflicts-since-last-restart
		   forget-threshold restart-threshold
		   #;satisfied-clauses))
#;(SAT-Stats (SAT-Stats-decision-level stats)
  	     (SAT-Stats-assigned-order stats)
             (SAT-Stats-forget-threshold sat)
             (SAT-Stats-restart-threshold sat)
	     (SAT-Stats-conflicts-since-last-restart sat))

(define (set-decision-level stats val)
  (SAT-Stats val
  	     (SAT-Stats-assigned-order stats)
             (SAT-Stats-conflicts-since-last-restart stats)
             (SAT-Stats-forget-threshold stats)
	     (SAT-Stats-restart-threshold stats)))
(define (set-assigned-order stats val)
  (SAT-Stats (SAT-Stats-decision-level stats)
  	     val
             (SAT-Stats-conflicts-since-last-restart stats)
             (SAT-Stats-forget-threshold stats)
	     (SAT-Stats-restart-threshold stats)))
(define (set-forget-threshold stats val)
  (SAT-Stats (SAT-Stats-decision-level stats)
  	     (SAT-Stats-assigned-order stats)
             (SAT-Stats-conflicts-since-last-restart stats)
             val
	     (SAT-Stats-restart-threshold stats)))
(define (set-restart-threshold stats val)
  (SAT-Stats (SAT-Stats-decision-level stats)
  	     (SAT-Stats-assigned-order stats)
             (SAT-Stats-conflicts-since-last-restart stats)
             (SAT-Stats-forget-threshold stats)
	     val))
(define (set-conflicts-since-last-restart stats val)
  (SAT-Stats (SAT-Stats-decision-level stats)
  	     (SAT-Stats-assigned-order stats)
             val 
             (SAT-Stats-forget-threshold stats)
	     (SAT-Stats-restart-threshold stats)))

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