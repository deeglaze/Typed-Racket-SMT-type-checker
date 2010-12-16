#lang typed/racket

(define-syntax-rule (iff a b) (if a b (not b)))
(define-syntax-rule (xor a b) (if a (not b) b))
;a&b v ~a&~b
(define-syntax-rule (iff2 a b) (if (if a b #f)
				   #t
				   (if (not a) (not b) #f)))

(define-syntax-rule (xor2 a b) (if (if a (not b) #f)
				   #t
				   (if b (not a) #f)))


(define: (example [a : Boolean] [b : Boolean]) : Number
   (if (not (iff2 (iff2 a b)
		  (not (xor2 a b))))
      #t
      0))


(define: (example2 [a : Boolean] [b : Boolean]) : Number
  (if (not (iff (iff2 a b)
		(not (xor2 a b))))
      #t
      0))


