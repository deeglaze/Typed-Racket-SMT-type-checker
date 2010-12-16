#lang racket

(require srfi/13)

(provide read-dimacs 
	 dimacs-polarity 
	 dimacs-lit->dimacs-var
	 dimacscnf?)

(define (read-dimacs)
  (let ((line (string-tokenize (read-line))))
    (cond 
     [(string=? "c" (substring (car line) 0 1)) ; skip all comments
      (read-dimacs)]
     [(string=? "p" (car line)) ; defines the problem. Expect "p cnf #vars #clauses"
      (list (string->number (caddr line))
            (string->number (cadddr line))
            (read-some-dimacs-clauses (string->number (cadddr line))))])))

(define (read-some-dimacs-clauses n)
  (if (= n 0)
      '()
      (cons 
       ;; DIMACS has a 0 at the end of each clause. Drop it.
       (remove-duplicates (map string->number (drop-right (string-tokenize (read-line)) 1)))
       (read-some-dimacs-clauses (+ -1 n)))))
  
(define (dimacs-polarity lit)
  (lit . > . 0))

(define (dimacs-lit->dimacs-var lit)
  (if (dimacs-polarity lit)
      lit
      (- lit)))

(define (dimacscnf? x)
  (match x
    [`(,var-count ,clause-count ((,lit ...) ...))
     (let* ((dimacs-lit? 
	     (lambda (l)
	       (and (exact-integer? l)
		    (not (zero? l))
		    (<= (dimacs-lit->dimacs-var l) var-count))))
	    (dimacs-clause? (lambda (C) (andmap dimacs-lit? C)))
	    (get-vars (lambda (CNF)
			(remove-duplicates (append* CNF) 
					   (lambda (x y)
					     (eqv? (dimacs-lit->dimacs-var x)
						   (dimacs-lit->dimacs-var y)))))))
       (and (exact-positive-integer? var-count)
	    (exact-positive-integer? clause-count)
	    (andmap dimacs-clause? lit)
	    (eqv? (length lit) clause-count)
	    (eqv? (length (get-vars lit)) var-count)))]
    [else #f]))
