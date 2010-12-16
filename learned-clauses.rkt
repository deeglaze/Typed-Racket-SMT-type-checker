#lang racket

(require data/order)
(require data/splay-tree)
(require "heuristic-constants.rkt")

(provide (all-defined-out))

;; a learned clause must have an activation like literals do
;; so that we can forget low activation clauses
;; forgotten? is a way to make a weak reference so that
;; when doing BCP, broken links can be collected.
(struct learned-clause (clause activation forgotten?) #:mutable)

(define learned-clauses-count splay-tree-count)
(define (empty-learned-clauses) 
  (make-splay-tree (order 'inexact-real-order inexact-real? = < >)))

(define (clause-forgotten? clause)
  (and (learned-clause? clause)
       (learned-clause-forgotten? clause)))


(define (add-learned-clause! lcs c)
  (splay-tree-set! lcs (learned-clause-activation c) c))

(define (inc-learned-clause-activation! lcs c)
  (let ((key (learned-clause-activation c)))
    (splay-tree-remove! lcs key)
    (splay-tree-set! lcs (+ key ACTIVITY_INC))))

(define (slash-all-learned-clauses lcs)
  (let ((new-lcs (empty-learned-clauses)))
    (let recur ((itr (splay-tree-iterate-least lcs)))
      (if itr
	  (begin (splay-tree-set! new-lcs 
				  (/ (splay-tree-iterate-key itr)
				     ACTIVITY_DROPOFF)
				  (splay-tree-iterate-value itr))
		 (recur (splay-tree-iterate-next lcs itr)))
	  new-lcs))))

(define (forget-up-to-bound! lcs bound)
  (let ((activation-at-bound 
	 (let recur ((itr (splay-tree-iterate-least lcs))
		     (count 0)
		     (last-activation #f))
	   (if (and itr
		    (< count bound))
	       (begin (set-learned-clause-forgotten?! 
		       (splay-tree-iterate-value itr) #t)
		      (recur (splay-tree-iterate-next lcs itr)
			     (+ 1 count)
			     (splay-tree-iterate-key itr)))
	       last-activation))))
    (splay-tree-remove-range! lcs 0 activation-at-bound)))