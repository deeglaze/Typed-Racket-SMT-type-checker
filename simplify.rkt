#lang racket

(require rackunit)
(require "ts-data-structures.rkt")

(provide (all-defined-out))

(define (flatten-union u)
  (union
   (let recur ((t (union-types u)))
     (cond 
      [(empty? t) '()]
      [(union? (car t))
       (recur (append (union-types (car t)) (cdr t)))]
      [else 
       (cons (car t) (recur (cdr t)))]))))

(define (dedup-union u)
  (union
   (remove-duplicates (union-types u))))

(define (dedegenerate-union u)
  (cond
   [(= 1 (length (union-types u))) (car (union-types u))] ; no singleton unions
   [(member 'top (union-types u)) 'top] ; union with top and get top
   [else u]))

(define (simplify-union u)
  (dedegenerate-union (dedup-union (flatten-union u))))

(define (or-list props)
  (match props
    ['() #f]
    [`(,p) p]
    [`(,p ...) `(or ,@p)]))

;; props are under an or
;; assuming no true/false constants
(define (flatten-or props)
  (or-list
   (let recur ((props props) (acc '()))
     (if (empty? props)
	 acc
	 (match (car props)
           [`(or ,p ...)
	    (recur (cdr props) (recur p acc))]
	   [other
	    (recur (cdr props) (cons other acc))])))))

(check equal?
       (flatten-or '( (or (or (and X Y)) (and X)) Y (or Y) Y (or X Y Z)))
       `(or ,@(reverse '((and X Y) (and X) Y Y Y X Y Z))))

(define (and-list props)
  (match props
    ['() #t]
    [`(,p) p]
    [`(,p ...) `(and ,@p)]))

;; props are under an and
;; assuming no true/false constants
(define (flatten-and props)
  (and-list
   (let recur ((props props) (acc '()))
     (if (empty? props)
	 acc
	 (match (car props)
           [`(and ,p ...)
	    (recur (cdr props) (recur p acc))]
	   [other
	    (recur (cdr props) (cons other acc))])))))

;; monads to simplify or/and maps
(define (<<=-or prop acc acc->prop)
  (match prop
    [#t #t]
    [#f (acc->prop acc)]
    [prop (acc->prop (cons prop acc))]))

(define (<<=-and prop acc acc->prop)
  (match prop
    [#f #f]
    [#t (acc->prop acc)]
    [prop (acc->prop (cons prop acc))]))

(define-syntax op-seq-acc
  (syntax-rules ()
    [(_ acc op-ret op) (op-ret acc)]
    [(_ acc op-ret op prop . props)
     (op prop acc
	 (lambda (acc) (op-seq-acc acc op-ret op . props)))]))


(define-for-syntax (string-append* s) (foldr string-append "" s))
(define-for-syntax (symbol-append . syms)
  (string->symbol (string-append* (map symbol->string syms))))

;; break hygiene for convenience
(define-syntax (op-seq stx)
  (syntax-case stx (or and)
    [(_ or . props)
     (with-syntax ((op-ret (datum->syntax stx 'flatten-or))
                   (op     (datum->syntax stx '<<=-or)))
       (syntax (let ((acc '()))
                 (op-seq-acc acc op-ret op . props))))]
    [(_ and . props)
     (with-syntax ((op-ret (datum->syntax stx 'flatten-and))
                   (op     (datum->syntax stx '<<=-and)))
       (syntax (let ((acc '()))
                 (op-seq-acc acc op-ret op . props))))]))
(define-syntax-rule (or-seq . props) (op-seq or . props))
(define-syntax-rule (and-seq . props) (op-seq and . props))

(define (implies-seq ante concl)
  (match ante
    [#f #t]
    [#t concl]
    [`(not ,ante*)
     (match concl
       [#t #t]
       [#f ante*]
       [`(not ,concl*)
	(implies-seq concl* ante*)]
       [r-nontriv
	`(implies (not ,ante*) ,r-nontriv)])]
    [l-nontriv
     (match concl
       [#t #t]
       [#f `(not ,l-nontriv)]
       [r-nontriv `(implies ,l-nontriv ,r-nontriv)])]))

(define (prop-or-map props prop->prop)
  (let recur ((props props) (acc '()))
    (if (empty? props)
        (flatten-or acc)
        (<<=-or (prop->prop (car props)) acc
		(lambda (acc) (recur (cdr props) acc))))))

(define (prop-and-map props prop->prop)
  (let recur ((props props) (acc '()))
    (if (empty? props)
        (flatten-and acc)
        (<<=-and (prop->prop (car props)) acc
		 (lambda (acc) (recur (cdr props) acc))))))

(define (simplify-type τ)
  (match τ
    [(abs sym σ τ* φ+ φ- o)
     (abs sym (simplify-type σ) (simplify-type τ*) (simplify-prop φ+) (simplify-prop φ-) o)]
    [(union lst)
     (let ((fixed-union (simplify-union τ)))
       (if (union? fixed-union) ;it might've been turned into 'top
           (union (map simplify-type (union-types fixed-union)))
           fixed-union))]
    [simple simple]))

(define (simplify-prop p)
  (match p
   [`(or ,p ...)
    (prop-or-map p simplify-prop)]
   [`(and ,p ...)
    (prop-and-map p simplify-prop)]
   [`(not (implies ,ante ,concl))
    (and-seq (simplify-prop ante) (simplify-prop `(not ,concl)))]
   [`(not ,p)
    (implies-seq (simplify-prop p) #f)]
   [`(implies ,l ,r)
    (implies-seq (simplify-prop l) (simplify-prop r))]
   [`(: ,sym ,τ)
    `(: ,sym ,(simplify-type τ))]
   [something something]))

(check equal?
       (simplify-prop '(and (and (: x true) #t) #t #t #t))
       '(: x true))

(check equal?
       (simplify-prop '(and (and (: x true) #t) #t #t
			    (or (or #f (and #t (and (: y false) (: y number)))) #f)
			    #t))
       '(and (: x true)
	     (: y false)
	     (: y number)))