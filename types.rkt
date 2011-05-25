#lang racket
(require rackunit)
(require "ts-data-structures.rkt")
(require "prop2cnf.rkt")
(require "sat-solve.rkt")
(require "simplify.rkt")
(require "debug.rkt")

(provide (all-defined-out))

(define (nodup-cons a lst)
  (if (member a lst)
      lst
      (cons a lst)))

(define (nodup-append X Y)
  (cond [(empty? X) Y]
	[(member (car X) Y) 
	 (nodup-append (cdr X) Y)]
	[else (cons (car X) (nodup-append (cdr X) Y))]))

(define (o-top? o)
  (eqv? o '∅))

; obj-<: Obj * Obj -> Bool
(define (obj-<: l r)
  (or (o-top? r)
      (eqv? l r)))

(define (obj-join o1 o2)
  (cond
   [(eqv? o1 o2) o1]
   [(or (o-top? o1) (o-top? o2)) '∅]
   [else (raise (type-exn (format "Unable to join objects: ~s and ~s" o1 o2)))]))

; list union under union struct
(define (type-join Γ-prop τ1 τ2 strength)
  (if ((approx-overlap? #t τ1) τ2)
      (if (sure-that-implies Γ-prop (τ1 . <:-when . τ2) strength)
          τ2
          (if (sure-that-implies Γ-prop (τ2 . <:-when . τ1) strength)
              τ1
              (simplify-union (union (list τ1 τ2)))))
      (simplify-union (union (list τ1 τ2)))))

(define bottom (union '()))
(define bool (union '(false true)))
(define procedure (abs 'x bottom 'top #t #t '∅))

; when is t a subtype of u?
; when the proposition returned is true.
; TODO: use subtyping cache when it exists
; <:-when : Type * Type -> Prop
(define (t . <:-when . u)
  (cond
   [(eqv? u 'top) #t]
   [(union? t) ; union on left - all are subtypes of u
    (prop-and-map (union-types t) (lambda (t-part) (t-part . <:-when . u)))]
   [(union? u) ; union on right - t is a subtype of some type in u
    (prop-or-map (union-types u) (lambda (u-part) (t . <:-when . u-part)))]
   [(equal? t u) #t] ;optimization 
   [(and (abs? u) (abs? t))
    (if ((abs-obj u) . obj-<: . (abs-obj t))
	(op-seq and
		((abs-param u) . <:-when . (abs-param t))
		((abs-return t) . <:-when . (abs-return u))
		(implies-seq (abs-latent-pos t) (abs-latent-pos u))
		(implies-seq (abs-latent-neg t) (abs-latent-neg u)))
        #f)]
   ;one of them is an atomic type, and they're not equal, so they can't be compatible.
   [else #f]))

; approx-overlap? : Bool * Type * Type -> Bool
; err-towards is the value that should be returned for "I don't know"
; commutative for τ and σ
(define ((approx-overlap? err-towards τ) σ)
  (cond
   [(union? τ)
    (ormap (approx-overlap? err-towards σ) (union-types τ))]
   [(union? σ)
    (ormap (approx-overlap? err-towards τ) (union-types σ))]
   ; if both abs, then give err-towards (functions can't be compared exactly).
   ; if not both abs, then we know they don't overlap.
   [(abs? τ) (and err-towards (abs? σ))]
   [else (or (eqv? τ σ)
	     (eqv? 'top τ)
	     (eqv? 'top σ))]))


(check equal? ('number . <:-when . 'false) #f)
(check equal? ('number . <:-when . 'number) #t)
(check equal? ('number . <:-when . 'top) #t)
(check equal? ('number . <:-when . 'top) #t)

(define (s<:w t u)
  (simplify-prop (t . <:-when . u)))

(define (s<:w? t u)
  (equal? (t . s<:w . u) #t))

(define (not-s<:w? t u)
  (equal? (t . s<:w . u) #f))

(check s<:w?     'number                 (union '(false number)))
(check not-s<:w? 'number                 bool)
(check not-s<:w? bool   'false)
(check not-s<:w? bool   (union '(false number)))
(check s<:w?     bool   (union '(true false)))

(define (simple-abs param return)
  (abs 'x param return #t #t '∅))


(check not-s<:w? (simple-abs 'number 'number)    'number)
(check s<:w?     (simple-abs 'number 'number)    'top)
(check not-s<:w? 'number                         (simple-abs 'number 'number))
(check s<:w?     (simple-abs 'number 'number)    (simple-abs 'number 'number))

;co-/contra- variance
(check s<:w?     (simple-abs 'number 'false)     (simple-abs 'number bool))
(check not-s<:w? (simple-abs 'number bool)       (simple-abs 'number 'false))
(check not-s<:w? (simple-abs 'false 'number)     (simple-abs bool 'number))
(check s<:w?     (simple-abs bool 'number)       (simple-abs 'false 'number))

(check s<:w?     (abs 'x bool bool `(: x true) `(: x false) 'x)
                 (abs 'x bool bool #t #t 'x))

(define op1 ;opaque predicates
  (abs 'x bool bool `(: x O1)  `(not (: x O1)) 'x))
(define op2
  (abs 'x bool bool `(: x O2)  `(not (: x O2)) 'x))
(define op1=2 ;the predicates are the same
  '(and (implies (: x O1) (: x O2))
        (implies (: x O2) (: x O1))))

(check equal?
       (op1 . s<:w . op2)
       op1=2)

(check equal?
       (op1 . s<:w . (union `(number ,op2)))
       op1=2)

(check s<:w  (union `(,op1 ,op2)) (union`(,op2 ,op1)))
;is this right?  Should there be some kind of binding for x?
       (         (abs 'x bool bool #t       #t 'x)
        . s<:w . (abs 'x bool bool `(: x true) `(: x false) 'x))
       
(define ((is-prop-fv? v) p)
  (match p
    [`(: ,sym ,τ)
     (or (eqv? v sym)
	 ((is-type-fv? v) τ))]
    [`(,op ,props ...)
     (ormap (is-prop-fv? v) props)]
    [simple #f]))

(define ((is-type-fv? v) τ)
  (match τ
    [(union types)
     (ormap (is-type-fv? v) types)]
    [(abs sym σ τ* φ+ φ- o)
     (and (not (eqv? v sym))
	  (or ((is-type-fv? v) σ)
	      ((is-type-fv? v) τ*)
	      ((is-prop-fv? v) φ+)
	      ((is-prop-fv? v) φ-)
	      (eqv? v o)))]
    [simple #f]))

(define (type-free-vars-with-types τ)
  (match τ
    [(union types)
     (append* (map type-free-vars-with-types types))]
    [(abs sym σ τ φ+ φ- o)
     (filter-not
      (λ (var-with-type)
         (eqv? (cadr var-with-type) sym))
      (append
       (prop-free-vars-with-types φ+)
       (prop-free-vars-with-types φ-)
       (type-free-vars-with-types σ)
       (type-free-vars-with-types τ)))]
    [simple '()]))

(define (prop-free-vars-with-types p)
  (match p
    [`(: ,sym ,τ)
     (list p)]
    [`(,op ,props ...)
     (append* (map prop-free-vars-with-types props))]
    [simple '()]))

(define (free-type-vars p)
  (remove-duplicates (prop-free-vars-with-types p)))
    
             
(define (polarity->prop ±) ±)
(define (polarity->type ±) (if ± 'true 'false))

(define ((type-sub-on-free v subst-type ±) τ)
  (if ((is-type-fv? v) τ)
      (polarity->type ±)
      ((type-sub v subst-type ±) τ)))

(define ((prop-sub-on-free v subst-prop ±) p)
  (if ((is-prop-fv? v) p)
      (polarity->type ±)
      ((prop-sub v subst-prop ±) p)))

(define ((type-sub from to ±) τ)
  (if (o-top? to)
      (polarity->type ±)
      (match τ
        [(union types)
         (union (map (type-sub from to ±) types))]
        [(abs sym σ τ* φ+ φ- o)
         (if (eqv? sym from)
             τ               ; no change; from was shadowed
             (abs sym
                  ((type-sub-on-free from to ±) σ)
		  ((type-sub-on-free from to ±) τ)
		  ((prop-sub-on-free from to ±) φ+)
		  ((prop-sub-on-free from to ±) φ-)
                  (o-sub o from to)))]
        [simple simple])))

; proposition : Obj * Obj * Bool -> Prop -> Prop
(define ((prop-sub from to ±) prop)
  (match prop
    [`(: ,sym ,τ)
     (if (o-top? to)
         (polarity->prop ±)
         (if ((is-prop-fv? from) prop)
             (if (eqv? sym from)
                 `(: ,to ,((type-sub from to ±) τ))
                 (polarity->prop ±))
             (if (eqv? sym from)
                 prop
                 `(: ,to ,((type-sub from to ±) τ)))))]
    [`(implies ,p1 ,p2)
     `(implies ,((prop-sub from to (not ±)) p1)
               ,((prop-sub from to ±) p2))]
    [`(not ,p1)
     `(not ,((prop-sub from to (not ±)) p1))]
    [`(,op ,prop ...)
     `(,op ,@(map (prop-sub from to ±) prop))]
    [#t #t]
    [#f #f]))

(define (o-sub from to o)
  (if (eqv? o from)
      to
      o))

;; restrict τ to σ
(define ((type-restrict Γ-prop strength σ) τ)
  (if ((approx-overlap? #t τ) σ)
      (cond [(union? τ)
	     (simplify-union (union (map (type-restrict Γ-prop strength σ) 
					 (union-types τ))))]
	    [(sure-that-± (implies-seq Γ-prop (τ . <:-when . σ)) strength #t)
	     τ]
	    [else σ])
      '⊥))


;; remove σ from τ
(define ((type-remove Γ-prop strength σ) τ)
  (cond [(sure-that-± (implies-seq Γ-prop (τ . <:-when . σ)) strength #t)
	 '⊥]
	[(union? τ)
	 (simplify-union (union (map (type-remove Γ-prop strength σ) (union-types τ))))]
	[else τ]))

(define (extend-type-env Γ-type sym type)
  (hash-set Γ-type sym (cons type (type-env-lookup Γ-type sym))))

(define (type-env-lookup Γ-type sym)
  (hash-ref Γ-type sym '()))

(define empty-type-env (hasheqv))

 ;; if ± then prove valid. if (not ±) then prove invalid.
(define (prove-± prop strength ±)
  (let-values (((cnf initial-t-state _) (prop->cnf `(not ,prop))))
    (match cnf ; make sure simplification didn't solve for us
      [#f ±] ; not prop is unsat => prop is valid
      [#t (not ±)] ; not prop is sat => prop is invalid
      [non-trivial
       (match (smt-assign non-trivial initial-t-state strength)
         ['UNSAT ±] 
         [assignment assignment])])))

(define (sure-that-± prop strength ±)
  (match (prove-± prop strength ±)
     [#f #f]
     [#t #t]
     [assignment #f]))


; assert-valid : Prop * Nat * T-State -> 
; the negation of prop should be unsatisfiable, i.e. prop is always true
(define (assert-valid prop strength)
  (let-values (((cnf initial-t-state cnf-pa->prop-pa) (prop->cnf `(not ,prop))))
    (match cnf ; make sure simplification didn't solve for us
      [#t ; prop is unsatisfiable
       (raise (type-exn (format "~a is unsatisfiable." prop)))] 
      [#f #t]                  ; prop is valid
      [non-trivial
         (match (smt-assign non-trivial initial-t-state strength)
           ['UNSAT ; there's no way to go wrong. prop is valid
            #t]
           [assignment 
            (raise (type-exn 
                    (format "Found a counterexample to ~s:~%~s" 
                            prop (cnf-pa->prop-pa assignment))))])])))

(define (first-type Γ-type sym)
  (let ((ret (type-env-lookup Γ-type sym)))
    (if (empty? ret)
        (raise (type-exn (format "unbound identifier error: ~a" sym)))
        (car ret))))

(define (assert-eqv expr x y)
  (if (eqv? x y)
      '*void*
      (raise (type-exn (format "~a is ~a, not ~a" expr x y)))))

(define (has-type expr τ Γ-prop Γ-type strength)
  (with-handlers ([type-exn? (lambda (e) #f)])
    (assert-has-type expr τ Γ-prop Γ-type strength)
    #t))

;; If an if branch does not type-check, try to prove that branch
;; is not reachable
(define (if-branch-has-type-under-guard guard guard-φ expr branch τ Γ-prop Γ-type strength)
  (define (iff x y) (or (and x y) (not (or x y))))
  (if (has-type expr τ (and-seq Γ-prop guard-φ) Γ-type strength)
      #t
      ;; try to prove branch not reachable. 
      ;; Then => guard : #f. Else => guard : not #f.
      (begin 
	(if (iff (has-type guard 'false Γ-prop Γ-type strength)
		 branch)
	    #t
	    (raise (type-exn (format "~a should have type ~a" expr τ)))))))

; ... -> ⊥
(define (assert-has-type expr τ Γ-prop Γ-type strength)
  ;(printf "~a {~a} asserted type ~a~%~%" expr Γ-prop τ)
  (or (eqv? 'top τ)
      (match expr
        [`(var ,sym)
	 (cond [(member τ (type-env-lookup Γ-type sym))
		(values #t Γ-type)]
	       [(assert-valid (implies-seq Γ-prop `(: ,sym ,τ)) strength)
		 (values #t (extend-type-env Γ-type sym τ))]
	       [else (values #f Γ-type)])]
	[`(abs ,sym ,σ ,body)
	 (match τ
		[(abs x σ* τ* φ+ φ- o*)
		 (let ((new-Γ-prop (and-seq Γ-prop `(: ,sym ,σ*)))
		       (new-Γ-type (extend-type-env Γ-type x σ*)))
		   (if (not (eqv? x sym))
		       (raise (type-exn (format "~a: symbol mismatch: ~a/~a" expr x sym)))
		       (begin
			 (assert-has-type body τ* new-Γ-prop new-Γ-type strength)
			 (let-values ([(_ ψ+ ψ- o) (type-of body new-Γ-prop new-Γ-type strength)])
			   (assert-valid (implies-seq Γ-prop (and-seq (implies-seq ψ+ φ+)
								      (implies-seq ψ- φ-)
								      (σ* . <:-when . σ))) strength)))))]
		[σ (raise (type-exn (format "~a should not be a function, expected ~a" expr τ)))])]
	[`(app ,e ,e*)
	 (let-values ([(σ*→τ* _+ _- _o) (type-of e Γ-prop Γ-type strength)])
	   (match σ*→τ*
		  [(abs sym σ* τ* φ+ φ- o*)
		   (let*-values ([(σ ψ+ ψ- o) (type-of e* Γ-prop Γ-type strength)]
				 [(τ*) ((type-sub sym o #t) τ*)])
		     (assert-valid (implies-seq Γ-prop
						(and-seq (σ* . <:-when . σ)
							 (τ* . <:-when . τ)))
				   strength))]
		  [σ (raise (type-exn (format "~a should be a function to type ~a, not ~a" e τ σ)))]))]
	[`(if ,guard ,then ,else)
	 (let-values ([(_τ φ+ φ- _o) (type-of guard Γ-prop Γ-type strength)])
	   (if-branch-has-type-under-guard guard φ+ then #t τ Γ-prop Γ-type strength)
	   (if-branch-has-type-under-guard guard φ- else #f τ Γ-prop Γ-type strength))]
	[`(let (,x ,e) ,body)
	 (let*-values ([(τ ψ0+ ψ0- o0) (type-of e Γ-prop Γ-type strength)])
	   (assert-has-type body τ 
		     (and-seq `(: ,x ,τ)
			      (implies-seq `(not (: ,x false)) ψ0+)
			      (implies-seq `(: ,x false) ψ0-)
			      Γ-prop)
		     (extend-type-env Γ-type x τ) strength))]
	[primitive
	 (let-values ([(τ* _+ _- _o) (type-of primitive  Γ-prop Γ-type strength)])
	   (assert-valid (implies-seq Γ-prop
				      (τ* . <:-when . τ)) strength))])))

(define (find-relevant-atomic-props Γ-prop sym)
  (match Γ-prop
    [`(not (: ,x ,τ))
     (if (eqv? x sym)
         (list Γ-prop)
         '())]
    [`(: ,x ,τ)
     (if (eqv? x sym)
         (list Γ-prop)
         '())]
    [`(,op ,ps ...)
     (append* (map (λ (p) (find-relevant-atomic-props p sym)) ps))]
    [literal '()]))

(define (sure-that-implies Γ-prop atomic-prop strength)
  (sure-that-± (implies-seq Γ-prop atomic-prop) strength #t))
    
     


; Expr * Prop * TypeEnv -> Type * Prop * Prop * Obj
(define (type-of expr Γ-prop Γ-type [strength 0])
  (with-handlers ([type-exn? (lambda (e) 
			       (printf "Type error in expression~%~%~a~%~a~%" expr (type-exn-message e))
                               (raise 'fail))])
    (match expr
      [`(var ,sym) ; T-Var
       (let ((best-type (foldr
                         (λ (prop σ)    ; gather up all the information
                            (debug "Fold in" prop σ)
                            (match prop
                                   [`(: ,sym ,τ)
                                    ((type-restrict Γ-prop strength τ) σ)]
                                   [`(not (: ,sym ,τ))
                                    ((type-remove Γ-prop strength τ) σ)]))
                         'top
                         (filter (λ (prop) (sure-that-implies Γ-prop prop strength)) ; pick out the true ones
                                 (find-relevant-atomic-props Γ-prop sym)))))
         (debug "Done:" sym best-type )
         (values best-type `(not (: ,sym false)) `(: ,sym false) sym))]
      ['true ; T-True
       (values 'true #t #f '∅)]
      ['false ; T-False
       (values 'false #f #t '∅)]
      [`(num ,n) ; T-Num
       (values 'number #t #f '∅)]
      [`(abs ,sym ,σ ,body) ; T-Abs
       (let-values ([(τ ψ+ ψ- o)
                     (type-of body (and-seq Γ-prop `(: ,sym ,σ)) 
			      (extend-type-env Γ-type sym σ) strength)])
	 (values (abs sym σ τ ψ+ ψ- o) #t #f '∅))]
      [`(app ,e ,e*) ; T-App
       (let*-values ([(fn-type ψ+ ψ- o) (type-of e  Γ-prop Γ-type strength)]
		     [(σ* ψ+* ψ-* o*)   (type-of e* Γ-prop Γ-type strength)]
		     [(x)   (abs-var fn-type)]
		     [(σ)   (abs-param fn-type)]
		     [(τ)   (abs-return fn-type)]
		     [(ψf+) (abs-latent-pos fn-type)]
		     [(ψf-) (abs-latent-neg fn-type)]
		     [(of)  (abs-obj fn-type)])
         (assert-has-type e* σ Γ-prop Γ-type strength)
	 (values ((type-sub x o* #t) τ)
		 ((prop-sub x o* #t) ψf+)
		 ((prop-sub x o* #f) ψf-)
		 (o-sub x o* of)))]
      [`(if ,guard ,then ,else) ; T-If
       (let*-values ([(τ1 ψ1+ ψ1- o1) (type-of guard Γ-prop Γ-type strength)]
		     [(τ2 ψ2+ ψ2- o2) (type-of then (and-seq ψ1+ Γ-prop) Γ-type strength)]
		     [(τ3 ψ3+ ψ3- o3) (type-of else (and-seq ψ1- Γ-prop) Γ-type strength)])
         (debug "If" expr τ2 τ3 (type-join Γ-prop τ2 τ3 strength))
	 (values (type-join Γ-prop τ2 τ3 strength)
                 (or-seq (and-seq ψ1+ ψ2+)
                         (and-seq ψ1- ψ3+))
                 (or-seq (and-seq ψ1+ ψ2-)
                         (and-seq ψ1- ψ3-))
		 (obj-join o2 o3)))]
      ;; T-Const
      [`(builtin number?) 
       (values (abs 'x 'top bool `(: x number) `(not (: x number)) '∅) #t #f '∅)]
      [`(builtin procedure?)
       (values (abs 'x 'top bool `(: x ,procedure) `(not (: x ,procedure)) '∅) #t #f '∅)]
      [`(builtin boolean?)
       (values (abs 'x 'top bool `(: x ,bool) `(not (: x ,bool)) '∅) #t #f '∅)]
      #;[`(builtin cons?)
      (values (abs 'x 'top bool `(: x ,bool) `(not (: x ,bool)) '∅) #t #f '∅)]
      [`(builtin add1)
       (values (abs 'x 'number 'number #t #f '∅) #t #f '∅)]
      [`(builtin zero?)
       (values (abs 'x 'number bool #t #t '∅) #t #f '∅)]
      ;; XXX: Remove when done debugging
      [`(example-fn ,τ ,σ)
       (values (abs 'x τ σ #t #t '∅) #t #f '∅)]

      [`(let (,x ,e) ,body)
       (let*-values ([(τ ψ0+ ψ0- o0) (type-of e Γ-prop Γ-type strength)]
                     [(σ ψ1+ ψ1- o1) (type-of body (and-seq `(: ,x ,τ)
                                                            (implies-seq `(not (: ,x false))
                                                                         ψ0+)
                                                            (implies-seq `(: ,x false)
                                                                         ψ0-)
                                                            Γ-prop)
                                              (extend-type-env Γ-type x τ) strength)])
         (values
          ((type-sub x o0 #t) σ)
          ((prop-sub x o0 #t) ψ1+)
          ((prop-sub x o0 #f) ψ1-)
          (o-sub x o0 o1)))])))

(define (type-of-test expr)
  (let-values ([(τ φ+ φ- o) (type-of expr #t empty-type-env)])
    (simplify-type τ)))

(check equal?
       (type-of-test '(num 6))
       'number)

(check equal?
       (type-of-test '(abs x top (if (app (builtin number?) (var x)) true (var x))))
       (abs 'x 'top 'top
            '(or (: x number) (and (not (: x number)) (not (: x false)))) 
            '(and (not (: x number)) (: x false)) '∅))
