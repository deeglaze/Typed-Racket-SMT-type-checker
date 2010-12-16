#lang racket

(provide (all-defined-out))

(define INITIAL_ACTIVITY 0.0)
(define ACTIVITY_INC 1.0)
(define ACTIVITY_DROPOFF 2.0)

;;;;;; Minisat forget policy ;;;;;
;; at what percentage of the original problem should we start forgetting clauses?
(define FORGET_THRESHOLD_INITIAL_PERCENTAGE 1.333333)
;; How fast should the forget threshold geometrically grow?
(define FORGET_THRESHOLD_COEFFICIENT (/ 1.0 0.99))
;; what percentage of the original problem should we enforce must live?
(define FORGET_THRESHOLD_RETAIN_PERCENTAGE 0.5) 

;;;;;; Picosat restart policy ;;;;;
;; how many conflicts until the first restart?
(define RESTART_INITIAL_THRESHOLD 100)
;; Coefficient for its two geometric sequences
(define RESTART_COEFFICIENT 1.5)
