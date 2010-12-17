#lang racket
(require rackunit)
(require srfi/1)
(require "ts-data-structures.rkt")
(require "simplify.rkt")
(require "dimacs.rkt")

(provide (all-defined-out))

;A Prop is one of
; - `(: ,Symbol ,Type)      ;;; this is the only proposition to interpret
; - `(not ,Prop)
; - `(implies ,Prop ,Prop)
; - `(or ,Prop ,Prop)
; - `(and ,Prop ,Prop)
; - #f
; - #t


;A Literal is one of
; - Symbol
; - `(not Symbol)

;A Depth1Prop is one of
; - `(: ,Symbol ,Type)           ;this Symbol is from a different namespace than the one above
; - `(not ,Literal)
; - `(implies ,Literal ,Literal)
; - `(or ,Literal ...)
; - `(and ,Literal ...)
; - #f
; - #t


(struct T-Lit (sym τ dimacs-lit level) #:transparent)

; Assoc<variable Sym to List<T-Lit>> * Assoc<DimacsVar to T-Lit> * Assoc<satisfaction level Nat to variable Pos> * Nat 
(struct T-State (type-info atomic-propositions backjump-table satisfaction-level) #:transparent)

(define (initial-t-state atomic-propositions) (T-State '() atomic-propositions '() 0))

(define (T-Lit-invert t-lit)
  (T-Lit (T-Lit-sym t-lit)
         (T-Lit-τ t-lit)
         (- (T-Lit-dimacs-lit t-lit))
         (T-Lit-level t-lit)))

(define (T-Lit-unassign t-lit)
  (T-Lit (T-Lit-sym t-lit)
         (T-Lit-τ t-lit)
         (dimacs-lit->dimacs-var (T-Lit-dimacs-lit t-lit))
         #f))

(define (T-Lit-unassigned? t-lit)
  (false? (T-Lit-level t-lit)))
(define (T-Lit-polarity t-lit)
  (dimacs-polarity (T-Lit-dimacs-lit t-lit)))
(define (T-Lit-function? t-lit)
  (abs? (T-Lit-τ t-lit)))

(define (T-Lit-dimacs-var t-lit)
  (dimacs-lit->dimacs-var (T-Lit-dimacs-lit t-lit)))

(define (T-Lit-and-±->prop t-lit ±)
  (if ±
      `(: ,(T-Lit-sym t-lit) ,(T-Lit-τ t-lit))
      `(not (: ,(T-Lit-sym t-lit) ,(T-Lit-τ t-lit)))))

(define (T-Lit->prop t-lit)
  (T-Lit-and-±->prop t-lit (T-Lit-polarity t-lit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Given a list, value to thread, and binary function returning 2 values, 
;; thread through the second of the two values while accumulating the first
(define (map-threading binary-2value-fn thread lst)
  (if (empty? lst)
      (values '() thread)
      (let*-values ([(val thread) (binary-2value-fn (car lst) thread)]
		    [(acc thread) (map-threading binary-2value-fn thread (cdr lst))])
	  (values (cons val acc)
		  thread))))


(define (hash-foldr fn base hash)
  (let recur ((i (hash-iterate-first hash)))
    (if (not i)
        base
        (fn (hash-iterate-key hash i)
            (hash-iterate-value hash i)
            (recur (hash-iterate-next hash i))))))

(define (hash-reduce-threading fn acc base thread hash)
  (let recur ((i (hash-iterate-first hash))
	      (thread thread))
    (if (not i)
        (values base thread)
	(let*-values ([(val thread) (fn (hash-iterate-key hash i)
					(hash-iterate-value hash i)
					thread)]
		      [(rest thread) (recur (hash-iterate-next hash i) thread)])
	  (values (acc val rest)
		  thread)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tseitin transform functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; shred : Prop -> Literal * Env
; where Env is a Hash<Depth1Prop to DimacsLit>
; We do an initial structural hashing in order to spot
; sharing. 
; XXX: For finding more sharing, we should normalize associations
; and order literal by some total order.
(define (shred prop)
  (let*-values ([(env) (make-hash)] ; env is a mutable hash
		[(top-sym total-vars)
		 ;; shredrec : Prop -> Sym
		 (let shredrec ((p prop)
				(varnum 1)) ;; use numbers instead of gensym
		   (match p
			  [`(: ,sym ,type)
			   (values (hash-ref! env p varnum) (+ 1 varnum))]
			  [`(not ,p)
			   (let-values ([(d1prop varnum) (shredrec p varnum)])
			     (values (- d1prop) varnum))]
			  [`(,op ,ps ...)
			   (let-values ([(d1props varnum) 
					 (map-threading shredrec varnum ps)])
			     (values (hash-ref! env (cons op d1props) varnum)
				     (+ 1 varnum)))]
			  [t-or-f
			   (error "[Internal error] Literal false or true found!")]))])
    (values top-sym total-vars env)))


(define-values (test-top-sym total-vars test-env)
  (shred '(or (not (: s1 τ1))
              (and (: s2 τ2)
                   (: s3 τ3)
                   (: s4 τ4))
              (: s5 τ5))))

;flip the hash
(define test-back-env (make-hash (map (λ (v) (cons (cdr v) (car v))) (hash->list test-env))))

(define test-p1 (hash-ref test-back-env test-top-sym))
(check equal? (car test-p1) 'or)

(define test-p2 (hash-ref test-back-env (caddr test-p1))) ;second element
(check equal? (car test-p2) 'and)

(define test-p3 (hash-ref test-back-env (cadddr test-p2))) ;third element
(check equal? test-p3 '(: s4 τ4))

;; Tseitin transform depth1props to Dimacs format.
;; This means counting the number of clauses created.
(define (wff-hash->cnf env)
  ;; some shorthand for easy reading
  (define (implies p . q) (list* (- p) q))
  (define (implies* p q) (list* (- p) q))
  (define (or . ps) ps)
  (define (not p) (- p))
  (hash-reduce-threading 
   (lambda (prop dimacsvar num-clauses)
     (match prop
       [`(: ,sym ,τ) ;; ground proposition. Not in clause.
        (values '() num-clauses)]
       [`(not ,sym) 
        (error "[Internal error] Naked NOT should not survive shredding.")]
       [`(implies ,p ,q)
        (values (list (implies dimacsvar (not p) q)
                      (implies q dimacsvar)
                      (or dimacsvar p))
                (+ 3 num-clauses))]
       [`(and ,ps ...)
        ;; and gate is true iff all of ps are true
        (let-values ([(andlits) (map - ps)]
                      [(impclauses num-clauses)
                       (map-threading (lambda (p num-clauses)
                                        (values (implies dimacsvar p)
                                                (+ 1 num-clauses)))
                                      (+ 1 num-clauses)
                                      ps)])
          (values (cons (cons dimacsvar andlits) ; ~andgate => (not (and ,@ps))
                        impclauses) ; for all p in ps, andgate => p
                  num-clauses))]
       [`(or ,ps ...) 
        ;; or gate is true iff one of ps is true.
        (let-values ([(impclauses num-clauses)
                       (map-threading (lambda (p num-clauses)
                                        (values (implies p dimacsvar)
                                                (+ 1 num-clauses)))
                                      (+ 1 num-clauses)
                                      ps)])
          (values (list* (implies* dimacsvar ps) ; orgate => p1 or p2 or ... 
                         impclauses) ; for all p in ps, p => orgate
                  num-clauses))]))
   append '() 0 env))


; prop->cnf : Prop -> CNF * Assoc<Pos to atomic Prop> * Hash<Prop, Pos>
(define (prop->cnf prop)
  (let ((simp-prop (simplify-prop prop)))
    (match simp-prop
      [#t (values #t (make-hash) (λ (d) '()))]
      [#f (values #f (make-hash) (λ (d) '()))]
      [non-trivial
       (let*-values ([(top-sym total-vars env) (shred non-trivial)]
                     [(cnf total-clauses) (wff-hash->cnf env)]
		     [(atomic-propositions)
		      ;; collect all theory literals in a dictionary keyed 
		      ;; by their propositional variable.
		      ;; OT-theory specific!
		      (hash-foldr
		       (λ (prop dimacs-lit atomic-assoc)
			  (match prop
				 [`(: ,var ,type)
				  (dict-set atomic-assoc dimacs-lit (T-Lit var type dimacs-lit #f))]
				 [else atomic-assoc]))
		       '()
		       env)])
	 (values (list (+ -1 total-vars) ; one too many due to needing fresh names
                       (+ 1 total-clauses) ; add 1 for top level assertion
                       (cons (list top-sym) ; assert the top level
                             cnf))
                 (initial-t-state atomic-propositions)
		 (cnf-partial-assignment->prop-partial-assignment atomic-propositions)))])))

(define ((cnf-partial-assignment->prop-partial-assignment atomic-propositions) pa)
  (map (lambda (dimacs-lit)
	 (T-Lit-and-±->prop (dict-ref atomic-propositions (dimacs-lit->dimacs-var dimacs-lit))
			    (dimacs-polarity (first pa))))
       pa))
  

; Not only do we need to convert our propositions to CNF, we need to convert
; our CNF's SAT assignment back to a prop SAT assignment.
; This is important because we want to have informative error messages.
; TODO: Good error messages from satisfying assignment  


#;
(define (set-of-sets=? l1 l2)
  (let* ((list->set (λ (l) (apply set l)))
         (list-list->set-set (λ (ll) (list->set (map list->set ll))))
         (set=? (λ (s1 s2) (and (subset s1 s2) (subset s2 s1)))))
    (set=? (list-list->set-set l1) (list-list->set-set l2))))

(prop->cnf '(and (: s1 τ1) (not (: s2 τ2)) (: s3 τ3)))
(prop->cnf '(or (: s1 τ1) (not (: s2 τ2)) (: s3 τ3)))
