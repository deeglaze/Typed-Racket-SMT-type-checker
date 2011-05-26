#lang racket

(provide prop->cnf bconn? hash-foldr single-ify)

; A Boolean connective (bconn) is
(define (bconn? x) (memq x '(or and not implies)))

;A Prop is one of
; - `(,bconn ,Prop ...)
; - #f
; - #t
; - other     ;;; interpreted

;A Literal is one of
; - Symbol
; - `(not Symbol)

;A Depth1Prop is one of
; - `(,bconn ,Literal ...)
; - #f
; - #t
; - other

(define (uninterpreted-prop? x)
  (not (or (boolean? x)
           (and (pair? x)
                (bconn? (car x))))))

(define (single-ify bconn base lst)
  (cond [(empty? lst) base]
        [(empty? (cdr lst)) (car lst)]
        [else (cons bconn lst)]))

(define (remove-prop-booleans prop)
  (match prop
    [`(not ,prop*)
     (let ([rprop* (remove-prop-booleans prop*)])
       (if (boolean? rprop*)
           (not rprop*)
           `(not ,rprop*)))]
    [`(implies ,prop1 ,prop2)
     (let ([rprop1 (remove-prop-booleans prop1)])
       (cond [(eqv? rprop1 #t) ;; TT => P == P
              (remove-prop-booleans prop2)]
             [(false? rprop1) ;; FF => P == TT
              #t]
             [else
              (let ([rprop2 (remove-prop-booleans prop2)])
                (cond [(eqv? rprop2 #t);; P => TT == P
                       rprop1]
                      [(false? rprop2) ;; P => FF == (not P)
                       `(not ,rprop1)]
                      [else ;; general case
                       `(implies ,rprop1 ,rprop2)]))]))]
    [`(and ,props ...)
     (let ([rprops (map remove-prop-booleans props)])
       (cond [(memq #f rprops)
              #f]
             [else (let ([rprops-no-t (remove* (list #t) rprops)])
                     (or (empty? rprops-no-t)
                         (single-ify 'and #t rprops-no-t)))]))]
    [`(or ,props ...)
     (let ([rprops (map remove-prop-booleans props)])
       (cond [(memq #t rprops)
              #t]
             [else (let ([rprops-no-f (remove* (list #f) rprops)])
                     (and (pair? rprops-no-f)
                          (single-ify 'or #f rprops-no-f)))]))]
    [other other]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (hash-foldr fn base hash)
  (let recur ((i (hash-iterate-first hash)))
    (if i
        (fn (hash-iterate-key hash i)
            (hash-iterate-value hash i)
            (recur (hash-iterate-next hash i)))
        base)))

(define (hash-reduce fn acc base hash)
  (let recur ([itr (hash-iterate-first hash)])
    (if itr
	(acc (fn (hash-iterate-key hash itr)
                 (hash-iterate-value hash itr))
             (recur (hash-iterate-next hash itr)))
        base)))

(define (incbox! b) (set-box! b (add1 (unbox b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tseitin transform functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; shred : Prop * Box Natural * Hash<Prop,Natural> -> Literal
; where Env is a Hash<Depth1Prop to DimacsLit>
; We do an initial structural hashing in order to spot
; sharing.
; XXX: For finding more sharing, we should normalize associations
; and order literal by some total order.
(define (shred prop varnum env)
 ;; shredrec : Prop -> Sym
  (let shredrec ([p prop])
    (match p
      [`(not ,p)
       (- (shredrec p))]
      [`(,(? bconn? op) ,ps ...)
       (let ([d1props (map shredrec ps)])
         (begin0 (hash-ref! env (cons op d1props) (unbox varnum))
                 (incbox! varnum)))]
      [(? boolean? x)
       (error "[Internal error] Literal false or true found!")]
      [other ;; intepreted
       (begin0 (hash-ref! env p (unbox varnum))
               (incbox! varnum))])))

;; Tseitin transform depth1props to Dimacs format.
;; This means counting the number of clauses created.
(define (wff-hash->cnf env num-clauses)
  ;; some shorthand for easy reading
  (define (implies p . q) (list* (- p) q))
  (define (implies* p q) (list* (- p) q))
  (define (or . ps) ps)
  (define (not p) (- p))
  (hash-reduce
   (lambda (prop dimacsvar)
     (match prop
            [`(not ,sym)
             (error "[Internal error] Naked NOT should not survive shredding.")]
            [`(implies ,p ,q)
             (set-box! num-clauses (+ 3 (unbox num-clauses)))
             (list (implies dimacsvar (not p) q)
                   (implies q dimacsvar)
                   (or dimacsvar p))]
            [`(and ,ps ...)
             ;; and gate is true iff all of ps are true
             (let ([andlits (map - ps)]
                   [impclauses (map (lambda (p)
                                      (incbox! num-clauses)
                                      (implies dimacsvar p))
                                    ps)])
               (incbox! num-clauses)
               (cons (cons dimacsvar andlits) ; ~andgate => (not (and ,@ps))
                     impclauses))]     ; for all p in ps, andgate => p
            [`(or ,ps ...)
             ;; or gate is true iff one of ps is true.
             (let ([impclauses (map (lambda (p)
                                      (incbox! num-clauses)
                                      (implies p dimacsvar))
                                    ps)])
               (incbox! num-clauses)
               (list* (implies* dimacsvar ps) ; orgate => p1 or p2 or ...
                      impclauses))]     ; for all p in ps, p => orgate
            [other ;; ground proposition. Not in clause.
             '()]))
   append '() env))

; prop->cnf : Prop -> CNF * T-State
(define (prop->cnf initialize-t-state prop)
  (let ((simp-prop (remove-prop-booleans prop)))
    (match simp-prop
      [#t (values #t (initialize-t-state (make-hash)))]
      [#f (values #f (initialize-t-state (make-hash)))]
      [non-trivial
       (let* ([env (make-hash)]
              [total-vars (box 1)] ;; start variables at 1 since 0 can't be negated
              [total-clauses (box 0)] ;; start with 0 clauses and count upwards
              [top-sym (shred non-trivial total-vars env)]
              [cnf (wff-hash->cnf env total-clauses)]
              [atomic-propositions
               ;; collect all theory literals in a dictionary keyed
               ;; by their propositional variable.
               (make-immutable-hash
                (hash-foldr
                 (λ (prop dimacs-lit atomic-assoc)
                    ;; dimacs-lit should always be positive for an uninterpreted prop
                    (if (uninterpreted-prop? prop)
                        (dict-set atomic-assoc prop dimacs-lit)
                        atomic-assoc))
                 '()
                 env))])
	 (values (list (sub1 (unbox total-vars)) ; one too many due to needing fresh names
                       (add1 (unbox total-clauses)) ; add 1 for top level assertion
                       (cons (list top-sym) ; assert the top level
                             cnf))
                 (initialize-t-state atomic-propositions)))])))
