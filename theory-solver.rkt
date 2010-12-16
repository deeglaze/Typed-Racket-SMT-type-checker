#lang racket
(require "sat-solve.rkt")
(require "prop2cnf.rkt")
(require "dimacs.rkt")
(require "ts-data-structures.rkt")
(require (rename-in "types.rkt" [type-of base-type-of]))
(require "simplify.rkt")
(require "debug.rkt")
(require "smt-interface.rkt")

(require rackunit)
(require srfi/26)

(provide (all-defined-out))

(define (approx prop err-towards)
  (let ((res (simplify-prop prop)))
    (if (boolean? res)
        res
        err-towards)))

(define (approx-<: τ σ err-towards)
  (approx (τ . <:-when . σ) err-towards))

; XXX: I think it would be useful to look up the current valuation 
;      of the different <:-when clauses. Must be careful to avoid circular reasoning.
(define (consistent-update? t-state t-lit)
  (let ((τ (T-Lit-τ t-lit))
        (τ± (T-Lit-polarity t-lit)))
    (and
     ;; a variable can never not have type top
     (or (not (eqv? 'top τ)) τ±)
     (andmap
      (λ (other-lit)
	 (let ((σ (T-Lit-τ other-lit))
	       (σ± (T-Lit-polarity other-lit)))
	   (cond 
	    [(and τ± σ±) ((approx-overlap? #t τ) σ)] ; type compatibility
	    [(and (not τ±) (not σ±)) #t] ; who can say?  Not a closed universe
            [(and τ± (not σ±)) (not (τ . approx-<: . σ #f))]
            [(and (not τ±) σ±) (not (σ . approx-<: . τ #f))])))
      (dict-ref (T-State-type-info t-state) (T-Lit-sym t-lit))))))


(define (strong-<: τ σ err-towards strength t-state)
  (not (not (explain-strong-<: τ σ err-towards strength t-state))))

(define (relevant-prop-from-type-info flat-type-info prop)
  (let ((free-vars (free-type-vars prop)))
    (filter 
     (λ (t-lit)
        (member `(: ,(T-Lit-sym t-lit) (T-Lit-τ t-lit)) free-vars))
     flat-type-info)))

(define (true-to-empty-list prop)
  (if (eqv? #t prop)
      '()
      prop))
  
; explain-strong-<: ... -> #f + List<DimacsLit>
(define (explain-strong-<: τ σ err-towards strength t-state)
  (let* ((flat-type-info (T-State-flat-type-info t-state))
         (subtype-prop (τ . <:-when . σ))
         (relevant-type-info (relevant-prop-from-type-info flat-type-info subtype-prop)))
    (true-to-empty-list
     (if (= 0 strength)
         (approx subtype-prop err-towards)
         (match (prove-± `(implies
                            ,(recover-Γ-prop-from-lits relevant-type-info)
                            ,subtype-prop) 
                         (+ -1 strength) #t)
           [#f #f]
           [#t #t]
           [explanation (map - explanation)])))))


(define (explain-not-<: τ σ err-towards strength t-state)
  (let* ((flat-type-info (T-State-flat-type-info t-state))
         (subtype-prop (τ . <:-when . σ))
         (relevant-type-info (relevant-prop-from-type-info flat-type-info subtype-prop)))
    (true-to-empty-list
     (if (= 0 strength)
         (not (approx subtype-prop (not err-towards)))
         (match (prove-± `(implies
                           ,(recover-Γ-prop-from-lits relevant-type-info)
                           ,subtype-prop) 
                         (+ -1 strength) #f)
           [#f #f]
           [explanation (map - explanation)])))))

(define (type-of expr)
  (parameterize ([T-Satisfy ot-satisfy]
                 [T-Propagate ot-propagate]
                 [T-Explain ot-explain]
                 [T-Consistent? ot-consistent?]
                 [T-Backjump ot-backjump])
    (base-type-of expr #t empty-type-env)))


; Assoc<Sym to AtomicProp> * TypeEnv -> 'consistent + CNF
;(define (theory-solve assignment Γ-type)

; L-Sub and L-SubNot should be used for theory propagation (needs to see <:-when clauses?)
; L-Bot firing means T-Inconsistent
; L-Update should be used for consistent updates + explanations

;; lit-type : T-State * DimacsLit -> T-Lit + #f
(define (lit-T-Lit t-state dimacs-lit)
  (cond
   ;; it only stores positive T-Lits
   [(dict-ref (T-State-atomic-propositions t-state) (dimacs-lit->dimacs-var dimacs-lit) #f)
    => (λ (t-lit) 
          (if (dimacs-polarity dimacs-lit)
              t-lit
              (T-Lit-invert t-lit)))]
   [else #f]))
           

;; ot-propagate : T-State * Nat * DimacsLit -> T-State * List<DimacsLit>
;; Given the literal most recently satisfied, the list of all theory literals,
;; and the partial assignment, return a list of literals that are currently implied.
;; XXX: Possibly save the explanations for later lookup.
(define (ot-propagate t-state strength lit)
  (let ((t-lit (lit-T-Lit t-state lit)))
    (if t-lit
        (let* ((sym (T-Lit-sym t-lit))
               (polarity (T-Lit-polarity t-lit))
               (σ (T-Lit-τ t-lit))
               (unassigned-vars
                (filter (λ (t-lit) (and (T-Lit-unassigned? t-lit)
                                        (eqv? (T-Lit-sym t-lit) sym)))
                        (dict-values (T-State-atomic-propositions t-state)))))
          (values
           t-state
           (if polarity
               (filter-map
                (λ (t-lit)
                   (and (σ . strong-<: . (T-Lit-τ t-lit) #f strength t-state)
                        (T-Lit-dimacs-var t-lit)))
                unassigned-vars) ; this literal should be satisfied
               (filter-map
                (λ (t-lit)
                   (and ((T-Lit-τ t-lit) . strong-<: . σ #f strength t-state)
                        (- (T-Lit-dimacs-var t-lit))))
                unassigned-vars))))
        (values t-state '()))))
            



;; literal is satisfied, and we know it was due to theory propagation. 
;; Propositionally, why was this literal entailed? (Returns clause)
;; ot-explain : T-State * Strength * DimacsLit -> List<DimacsLit>
(define (ot-explain t-state strength lit)
  (let ((this-lit (lit-T-Lit t-state lit)))
    (if this-lit
        (let* ((sym (T-Lit-sym this-lit))
               (polarity (T-Lit-polarity this-lit))
               (σ (T-Lit-τ this-lit))
               (relevant-lits
                (dict-ref (T-State-type-info t-state) sym)))
          (if (eqv? 'top σ)
              (list lit)
              (cond
               [(ormap
                 (λ (other-lit)
                    (if (eqv? lit (T-Lit-dimacs-lit other-lit))
                        #f ;; this lit can't explain itself
                        (let ((τ (T-Lit-τ other-lit)))
                          (if (T-Lit-polarity other-lit) ; assigned to true
                              (and polarity ; only true values contribute to a true assignment
                                   (cond
                                    [(τ . explain-strong-<: . σ #f strength t-state)
                                     ;; Explanation:  x:τ  τ <: σ implies x : σ. Thus {(not (: x τ)), (: x σ)}
                                     => (λ (explanation)
                                           (list* (- (T-Lit-dimacs-lit other-lit)) lit explanation))]
                                    [else #f])) ; doesn't make sense
                              (and (not polarity)
                                   ;; (not (: x τ))  σ <: τ implies (not (: x σ)). Thus {(: x τ), (not (: x σ))}
                                   (cond
                                    [(σ . explain-strong-<: . τ #f strength t-state)
                                     => (λ (explanation)
                                           (list* (- (T-Lit-dimacs-lit other-lit)) lit explanation))]
                                    [else #f])))))) ; doesn't make sense
                 relevant-lits)
                => (λ (x) x)]
               [else (error "no explanation" t-state lit)]))) ; can't find an explanation
        (list lit))))


(define (group-by lst selector cmp?)
  (if (empty? lst)
      '()
      (let*-values ([(sym) (selector (car lst))]
                    [(this rest) 
                     (partition (λ (i) (cmp? sym (selector i)))
                                lst)])
        `((,sym ,this)
          ,@(group-by rest selector cmp?)))))

(check equal?
       (group-by '(5 6 7 8 9 10) (λ (i) (modulo i 3)) eqv?)
       '((2 (5 8))
         (0 (6 9))
         (1 (7 10))))



; recover-Γ-prop-from-lits : List<T-Lit> -> Prop
(define (recover-Γ-prop-from-lits t-lits)
  `(and ,@(map T-Lit->prop t-lits)))

(define (T-State-flat-type-info t-state)
  (append* (dict-values (T-State-type-info t-state))))

;; Given the current partial assignment, is the conjection of all literals
;; consistent in the theory?
;; XXX: Try doing this incrementally
;; ot-consistent? : T-State * Strength -> Bool + List<DimacsLit>
(define (ot-consistent? t-state strength)
  (let/cc return
    (let ((assigned-lits (append* (dict-values (T-State-type-info t-state)))))
      (and 
       ;; lightweight consistency check
       (andmap (λ (lit) (consistent-update? t-state lit)) assigned-lits)
       ;; complete consistency check
       (foldr
        (lambda (x y) (and x y))
        #t
        (dict-map
         (T-State-type-info t-state)
         (λ (sym t-lits)
            (or
             (ormap (lambda (t-lit) (not (T-Lit-function? t-lit))) t-lits)
             (let*-values (((pos neg) (partition T-Lit-polarity t-lits)))
               (andmap
                (λ (pos)
                   (andmap
                    (λ (neg)
                       (match (explain-not-<: (T-Lit-τ pos) (T-Lit-τ neg) #f strength t-state)
                              [#t #t]
                              [explanation 
			       (debug "aren't subtypes" (T-Lit-τ pos) (T-Lit-τ neg))
			       (return explanation)]))))))))))))))


; T-State * DimacsLit -> T-State
(define (ot-satisfy t-state literal)
  (let* ((var (dimacs-lit->dimacs-var literal))
	 (t-lit (dict-ref (T-State-atomic-propositions t-state) var #f))
	 (satis-level (T-State-satisfaction-level t-state)))
    (if t-lit
        (let ((new-t-lit (T-Lit (T-Lit-sym t-lit) (T-Lit-τ t-lit) literal satis-level)))
          (T-State (dict-set (T-State-type-info t-state)
                             (T-Lit-sym t-lit)
                             (cons new-t-lit
				   ;; ...onto what we already know
                                   (dict-ref (T-State-type-info t-state)
                                             (T-Lit-sym t-lit)
                                             '())))
                   (dict-set (T-State-atomic-propositions t-state)
			     var new-t-lit)
                   (dict-set (T-State-backjump-table t-state)
                             satis-level var)
                   (+ 1 satis-level)))
	;; not a theory literal
	(T-State (T-State-type-info t-state)
		 (T-State-atomic-propositions t-state)
		 (T-State-backjump-table t-state)
		 (+ 1 satis-level)))))

(define (dict-filter-map dict fn)
  (let recur ((idx (dict-iterate-first dict)))
    (if idx
        (let ((res (fn (dict-iterate-key dict idx)
                       (dict-iterate-value dict idx))))
          (if res
              (cons res
                    (recur (dict-iterate-next dict idx)))
              (recur (dict-iterate-next dict idx))))
        '())))

(define (dict-value-filter dict pred? [empty-dict '()])
  (let recur ((idx (dict-iterate-first dict)))
    (if idx
        (if (pred? (dict-iterate-value dict idx))
            (dict-set (recur (dict-iterate-next dict idx))
                      (dict-iterate-key dict idx) (dict-iterate-value dict idx))
            (recur (dict-iterate-next dict idx)))
        empty-dict)))

(define (dict-key-filter-not dict pred? [empty-dict '()])
  (let recur ((idx (dict-iterate-first dict)))
    (if idx
        (if (pred? (dict-iterate-key dict idx))
            (recur (dict-iterate-next dict idx))
            (dict-set (recur (dict-iterate-next dict idx))
                      (dict-iterate-key dict idx) (dict-iterate-value dict idx)))
        empty-dict)))

;; Undo some number of assignments
(define (ot-backjump t-state backjump-by-sats)
  (let* ((new-satis-level (- (T-State-satisfaction-level t-state) backjump-by-sats))
         (too-high (lambda (lev) (and lev ;; is assigned
				      (lev . >= . new-satis-level)))))
    (T-State
     (dict-map
      (T-State-type-info t-state)
      (λ (sym t-lits)
         (cons sym (filter-not (lambda (t-lit) (too-high (T-Lit-level t-lit))) t-lits)))) ; create a new dictionary
     (dict-map
      (T-State-atomic-propositions t-state)
      (λ (dimacs-var t-lit)
         (cons dimacs-var
               (if (too-high (T-Lit-level t-lit))
                   (T-Lit-unassign t-lit)
                   t-lit))))
     (dict-key-filter-not (T-State-backjump-table t-state) too-high)
     new-satis-level)))

; Tests

(define (s-t-o expr)
  (let-values ([(τ ψ+ ψ- o) (type-of expr)])
    τ))

(define (<: τ σ)
  (not (not (prove-± (τ . <:-when . σ) +inf.0 #t))))

(define (never-<: τ σ)
  (prove-± (τ . <:-when . σ) +inf.0 #f))

(parameterize ([T-Satisfy ot-satisfy]
               [T-Propagate ot-propagate]
               [T-Explain ot-explain]
               [T-Consistent? ot-consistent?]
               [T-Backjump ot-backjump])


  (check <: 'number 'number)

  (check <:
         (abs 'x 'top bool `(: x ,bool) #t '∅)
         (abs 'x 'top bool `(: x ,bool) #t '∅))

  (check <:
         (abs 'x 'top bool `(: x true) #t '∅)
         (abs 'x 'top bool `(: x ,bool) #t '∅))

  (check <:
         (abs 'z 'top bool '(and (: z number) (: z number)) '(not (and (: z number) (: z number))) '∅)
         (abs 'z 'top bool '(: z number) '(not (: z number)) '∅))


  (check never-<:
         (abs 'z 'top bool '(and (: z number) (: w number)) '(not (and (: z number) (: w number))) '∅)
         (abs 'z 'top bool '(: z number) '(not (: z number)) '∅))


  
  (check equal?
         (simplify-type
          (s-t-o '(abs w top (abs z top (if (app (builtin number?) (var z)) (app (builtin number?) (var w)) false)))))
         (abs 'w 'top 
              (abs 'z 'top (union '(false true)) 
                   '(and (: z number) (: w number)) 
                   '(or (and (: z number) (not (: w number))) (not (: z number))) '∅) #t #f '∅))


  (check <:
         (abs 'z 'top bool '(: x number) `(: x ,bool) '∅)
         (abs 'z 'top bool `(not (: x ,bool)) '(not (: x number)) '∅))

  (check never-<:
         (abs 'z 'top bool `(not (: x ,bool)) '(not (: x number)) '∅) 
         (abs 'z 'top bool '(: x number) `(: x ,bool) '∅))




  (s-t-o
   `(abs x top (if (app (builtin number?) (var x)) (app (example-fn number true) (var x)) true)))


  (assert-has-type 
   `(abs y top (if (app (builtin number?) (if (app (builtin number?) (var y)) (var y) (num 1)))
                   (num 0)
                   false))
   (abs 'y 'top 'number #t #t '∅)
   #t
   empty-type-env
   +inf.0)
                   
 

 (check equal?
	(has-type
	 `(abs y top (if (app (builtin number?) (var y)) (var y) (num 0)))
	 (abs 'y 'top 'number #t #f '∅)
	 #t
	 empty-type-env
	 +inf.0)
	#t)
	 



         #;
  (s-t-o
   `(abs w top (app (abs f ,(abs 'w 'top bool '(: w number) '(not (: w number)) '∅) (var f))
                    (abs z top (if (app (builtin number?) (var z)) (app (builtin number?) (var w)) false)))))

 

#;
  (check equal?
         (assert-valid
          `(abs w top (app (abs f ,(abs 'w 'top bool '(: w number) '(not (: w number)) '∅) '(var f))
                           (abs z top (if (app (builtin number?) (var z)) (app (builtin number?) (var w)) false))))

))


)