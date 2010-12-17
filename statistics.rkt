#lang racket

(provide (all-defined-out))

(struct SAT-Stats (decision-level 
		   assigned-order 
		   forget-threshold restart-threshold
		   conflicts-since-last-restart
		   #;satisfied-clauses))
#;(SAT-Stats (SAT-Stats-decision-level stats)
  	     (SAT-Stats-assigned-order stats)
             (SAT-Stats-forget-threshold sat)
             (SAT-Stats-restart-threshold sat)
	     (SAT-Stats-conflicts-since-last-restart sat))

(define (set-decision-level stats val)
  (SAT-Stats val
  	     (SAT-Stats-assigned-order stats)
             (SAT-Stats-forget-threshold stats)
             (SAT-Stats-restart-threshold stats)
	     (SAT-Stats-conflicts-since-last-restart stats)))
(define (set-assigned-order stats val)
  (SAT-Stats (SAT-Stats-decision-level stats)
  	     val
             (SAT-Stats-forget-threshold stats)
             (SAT-Stats-restart-threshold stats)
	     (SAT-Stats-conflicts-since-last-restart stats)))
(define (set-forget-threshold stats val)
  (SAT-Stats (SAT-Stats-decision-level stats)
  	     (SAT-Stats-assigned-order stats)
             val
             (SAT-Stats-restart-threshold stats)
	     (SAT-Stats-conflicts-since-last-restart stats)))
(define (set-restart-threshold stats val)
  (SAT-Stats (SAT-Stats-decision-level stats)
  	     (SAT-Stats-assigned-order stats)
             (SAT-Stats-forget-threshold stats)
             val
	     (SAT-Stats-conflicts-since-last-restart stats)))
(define (set-conflicts-since-last-restart stats val)
  (SAT-Stats (SAT-Stats-decision-level stats)
  	     (SAT-Stats-assigned-order stats)
             (SAT-Stats-forget-threshold stats)
             (SAT-Stats-restart-threshold stats)
	     val))
