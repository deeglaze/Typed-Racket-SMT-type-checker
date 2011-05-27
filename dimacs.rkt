#lang racket

(require srfi/13 ;; for string-tokenize
	 "data-structures.rkt"
	 (only-in "sat-heuristics.rkt"
		  add-literal-watched!))

(provide read-dimacs
	 dimacs-polarity
	 dimacs-lit->dimacs-var
	 dimacs-lit->literal
	 dimacs-lits->clause
	 dimacs-cnf->clauses
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
       (read-some-dimacs-clauses (sub1 n)))))

(define (dimacs-polarity lit)
  (lit . > . 0))

(define (dimacs-lit->dimacs-var lit)
  (if (dimacs-polarity lit)
      lit
      (- lit)))

; DimacsLit -> Literal
(define ((dimacs-lit->literal variables) dimacs-lit)
  (literal
   (vector-ref variables (- (dimacs-lit->dimacs-var dimacs-lit) 1)) ; -1 is variable 0
   (dimacs-polarity dimacs-lit))) ; -1 is negated. False polarity

; list of DimacsLit -> Clause
(define ((dimacs-lits->clause variables) dimacs-lits)
  (cond
   [(empty? dimacs-lits) ;; can't represent "false" in CNF
    (error 'dimacs-lits->clause
           "There is an empty clause.  I don't think you will be satisfied.")]
   [else
    (let* ((literals (list->vector dimacs-lits))
	   (w1 (vector-ref literals 0))
	   (w2 (vector-ref literals (- (vector-length literals) 1)))
	   (C (clause literals w1 w2)))
      (add-literal-watched! C w1) ;it's safe for a clause to appear twice watched lists
      (add-literal-watched! C w2)
      C)]))

;; num-clauses is not used, but exists for the interface.
(define (dimacs-cnf->clauses num-clauses vars clauses)
  (let ([idx (box 0)])
    (make-immutable-hash
     (filter-map
      (λ (clause)
         (and (not (trivial-clause? clause))
              (begin0 (cons (unbox idx) ((dimacs-lits->clause vars) clause))
                      (set-box! idx (add1 (unbox idx))))))
      clauses))))

;; ... ∨ a ∨ ... ∨ ¬a ∨ ... = T
(define (trivial-clause? C)
  (ormap (lambda (l)
	   (ormap (lambda (l*)
		    (equal? l (- l*)))
		  C))
	 C))

;; for removing trivial clauses
(define (filter-not-count pred lst [count 0])
  (cond [(empty? lst) (values '() count)]
	[(pred (car lst))
	 (filter-not-count pred (cdr lst) (add1 count))]
	[else
	 (let-values ([(rec count) (filter-not-count pred (cdr lst)
						     count)])
	   (values (cons (car lst) rec) count))]))

(define (dimacscnf? x)
  (match x
    [`(,var-count ,clause-count ((,lit ...) ...))
     (let* ([dimacs-lit?
	     (lambda (l)
	       (and (exact-integer? l)
		    (not (zero? l))
		    (<= (dimacs-lit->dimacs-var l) var-count)))]
	    [dimacs-clause? (lambda (C) (and (andmap dimacs-lit? C) ;; all lits, and
					     ;; no lits appear positive and negative
					     (not (trivial-clause? C))))]
	    [get-vars (lambda (CNF)
			(remove-duplicates (append* CNF)
					   (lambda (x y)
					     (eqv? (dimacs-lit->dimacs-var x)
						   (dimacs-lit->dimacs-var y)))))])
       (and (exact-positive-integer? var-count)
	    (exact-positive-integer? clause-count)
	    (andmap dimacs-clause? lit)
	    (eqv? (length lit) clause-count)
	    (eqv? (length (get-vars lit)) var-count)))]
    [else #f]))
