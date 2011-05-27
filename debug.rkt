#lang racket

(require "data-structures.rkt")
(require "learned-clauses.rkt")

(provide debug)

; for reporting the decision level of a literal. Reports U if unassigned.
; This function should NOT be used outside of debugging.
(define (safe-literal-dec-lev literal)
  (let ((node (var-igraph-node (literal-var literal))))
    (if node
	(node-dec-lev node)
	'U)))

(define (pretty-print item)
   (cond
    [(clause? item) (vector (pretty-print (clause-watched1 item))
			    (pretty-print (clause-watched2 item))
			    (vector-map (lambda (lit) (pretty-print lit)) (clause-literals item)))]
    [(learned-clause? item) (vector (pretty-print (learned-clause-clause item))
				    (pretty-print (learned-clause-forgotten? item)))]
    [(vector? item) (vector-map (lambda (lit) (pretty-print lit)) item)]
    [(literal? item) (if (literal-polarity item) 
                         (format "~s[~s]" (var-name (literal-var item)) (safe-literal-dec-lev item))
                         (format "-~s[~s]" (var-name (literal-var item)) (safe-literal-dec-lev item)))]
    [(pair? item)
     (cons (pretty-print (car item))
	   (pretty-print (cdr item)))]
    [(node? item)
     (format "~a >> "
             (pretty-print (node-antecedent item)))]
    [else item]))

(define (debug msg . items)
  (begin (printf "~a: ~a~%" msg (string-join (map (λ (i) (format "~a" i)) (map pretty-print items)) "\n          "))
	 items))

#;(define-syntax debug
  (syntax-rules ()
    [(_ x . y) '*void*]))
