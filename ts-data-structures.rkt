#lang racket

(provide (all-defined-out))

; An Expr is one of
; - `(var ,Symbol)
; - `(app ,Expr ,Expr)
; - `(abs ,Symbol ,Type ,Expr)
; - `(if ,Expr ,Expr ,Expr)
; - `(builtin ,Symbol)
; - `true
; - `false
; - `(num ,Integer)

;A Type is one of 'top, 'number, 'true, 'false, Union, Abs

;A Union is (make-union List<Type>)
(struct union (types) #:transparent)

;An Abs is (make-abs Symbol Type Type Prop Prop Any)
(struct abs (var param return latent-pos latent-neg obj) #:transparent)

(define (type? x)
  (or (memv x '(top number true false))
      (union? x)
      (abs? x)))

;A Prop is one of
; - `(: ,Symbol ,Type)
; - `(not ,Prop)
; - `(implies ,Prop ,Prop)
; - `(or ,Prop ...)
; - `(and ,Prop ...)
; - #f
; - #t

; this doesn't thoroughly test for Prop-hood; it just checks what the intention of the thing is.
(define (prop? x)
  (or (boolean? x)
      (and (pair? x)
           (memv (car x) '(: not: implies or and))))) 



; An Obj is one of Symbol or #f

;; When we find a type error, we raise a type-exn with a 
;; [helpful] error message along. 
(struct type-exn (message) #:transparent)

