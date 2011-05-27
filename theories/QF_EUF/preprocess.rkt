#lang racket

(require "data-structures.rkt"
         "../../prop2cnf.rkt"
         "../../dimacs.rkt"
         "../../debug.rkt")

(provide EUF→CNF)

;; This file implements the translation of the input formula with arbitrary
;; function application equalities to the Currified form described in
;; Nieuwenhuis & Oliveras : Fast Congruence Closure and Extensions

(define (declaration? x)
  (match x
    [`(declare-fun ,(? symbol? X) ,(? exact-nonnegative-integer? arity)) #t]
    [`(declare-bool ,(? symbol? X)) #t]
    [other #f]))

(define (get-decl-var x)
  (match x
    [`(declare-fun ,X ,arity) X]
    [`(declare-bool ,X)       X]))

(define (get-decl-arity x)
  (match x
    [`(declare-fun ,X ,arity) arity]
    [`(declare-bool ,X) 'Boolean]))

;; sexp → CNF * T-state
;; Prop2cnf works on sexp propositions, so that's what we build.
;; If there are any arity mismatches, or duplicate declarations,
;; we raise an error.
(define (EUF→CNF sexp)
  (match sexp
    [`(,(? declaration? decls) ... (formula ,φ))
     (let* ([Xs (map get-decl-var decls)]
            [arities (map get-decl-arity decls)]
            [duplicates (get-duplicates Xs)])
       (cond [(pair? duplicates)
              (error "Duplicate function declaration(s) ~a" duplicates)]
             [else
              (let* ([term-dict (make-hash)]
                     [arity-dict (dict-set!-many (make-hash) Xs arities)]
                     [tvar-count (box 0)]
                     [E (box '())] ;; equalities to collect
                     [φ* ((φ→formula-sexp tvar-count term-dict arity-dict E) φ)])
                (debug "Term-dict ~a~%φ* ~a~%" term-dict φ*)
                (prop->cnf (EUF-initializer term-dict arity-dict (unbox tvar-count))
                           (single-ify 'and #t (cons φ* (unbox E)))))]))]
    [other
     (error "EUF→CNF: Unexpected input format ~a" other)]))

(define (EUF-initializer term-dict arity-dict tmp-tv)
  (λ (sexp↦dimacslit)
     (debug "sexp↦dimacslit ~a~%" sexp↦dimacslit)
     (let ([equalities (extract-euf-lits sexp↦dimacslit arity-dict)]) ;; lit -> equality
       (EUF-state equalities
                  (untranslator term-dict arity-dict equalities)
                  0 ;; sat-level
                  0 ;; last-consistency-check
                  tmp-tv
                  #f   ;; last-sat
                  '()  ;; eqlit
                  '()  ;; backjump-table
                  '()  ;; representative
                  '()  ;; classes
                  '()  ;; uses
                  '()  ;; lookup
                  '())))) ;; proof

(define (extract-euf-lits sexp↦dimacslit arity-dict)
  (make-immutable-hash
   (hash-foldr
    (λ (sexp dimacslit new-dict)
       (if (internal-eq? sexp)
           (dict-set new-dict dimacslit sexp)
           new-dict))
    '()
    sexp↦dimacslit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Untranslator
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If lit stands for an equality at the input level, i.e.
;; (ConstEQ 1 2) and ∃ a. term-dict(a) = 1 or ∃ a. term-dict(a) = 2
;; how we deal with the other is a recursive untranslation.
;; If 1 or 2 is not mapped in term-dict, then it must be standing
;; in for the output of a fully curried function call of a function in arity-dict.
;; (CurriedEQ g arg a) and arity-dict(g) = 1 or
;; g is standing in for ∃ f. ∃ ā. App(...App(f,a₁),...,an-1) and arity-dict(f) = n.
;; INVARIANT: term-dict is injectively mapped
(define (untranslator term-dict arity-dict equalities)
  (λ (lit)
     (let ([equality (dict-ref equalities (dimacs-lit->dimacs-var lit) #f)])
       (match equality
         [(ConstEQ a₁ a₂)
          (let ([a₁′ (let/ec return
                             (tvar->top-level-application return
                                                          term-dict
                                                          arity-dict
                                                          a₁))]
                [a₂′ (let/ec return
                             (tvar->top-level-application return
                                                          term-dict
                                                          arity-dict
                                                          a₂))])
            (debug "consteq untranslate" a₁′ a₂′)
            (and a₁′ a₂′
                 `(,(lit->eq-or-neq lit) ,a₁′ ,a₂′)))]
         [(CurriedEQ g arg a)
          (let ([g′ (let/ec return
                            (tvar->top-level-application return
                                                         term-dict
                                                         arity-dict
                                                         g
                                                         1))]
                [arg′ (let/ec return
                              (tvar->top-level-application return
                                                           term-dict
                                                           arity-dict
                                                           arg))]
                [a′ (let/ec return
                            (tvar->top-level-application return
                                                         term-dict
                                                         arity-dict
                                                         a))])
            (debug "curriedeq untranslate" g′ arg′ a′)
            (if (symbol? g′) ;; was unary
                (and arg′ a′ `(,(lit->eq-or-neq lit) (,g′ ,arg′) ,a′))
                (and g′ arg′ a′ `(,(lit->eq-or-neq lit) (,@g′ ,arg′) ,a′))))]
         [other
          (debug "no equality" lit)
          #f]))))

;; for clarity of the untranslation
(define (lit->eq-or-neq lit)
  (if (positive? lit)
      '=
      '≠))

(define (tvar->top-level-application return term-dict arity-dict tvar [depth 0])
  (let ([key (key-of-value term-dict tvar)])
    (cond [(App? key)
           (let ([f′ (tvar->top-level-application return term-dict arity-dict (App-f key) (add1 depth))]
                 [arg′ (tvar->top-level-application return term-dict arity-dict (App-arg key) 0)])
             (if (symbol? f′)
                 (list f′ arg′)
                 (append f′ arg′)))]
          ;; XXX: allow equality with Booleans?
          [(equal? depth (dict-ref arity-dict key))
           key]
          ;; arity mismatch, couldn't have been top level.
          [else (return #f)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Top-level -> internal representation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Add an untranslate map so we can return understandable
;; counter-examples and implied equalities.
(define ((φ→formula-sexp tvar-count term-dict arities E) φ)
  (match φ
    [`(,(? bconn? conn) ,φs ...)
     `(,conn ,@(map (φ→formula-sexp tvar-count term-dict arities E) φs))]
    [`(= ,t₁ ,t₂)
     (equality→internal-equality tvar-count term-dict arities E t₁ t₂)]
    [(? symbol? x)
     (let ([x-kind (dict-ref arities x #f)])
       (cond [(integer? x-kind)
              (error "Function may not be used as a formula ~a" x)]
             [(eqv? x-kind 'Boolean)
              x] ;; will be uninterpreted
             [else
              (error "Unknown variable ~a" x)]))]
    [other (error "Unexpected formula form ~a" other)]))


(define (equality→internal-equality tvar-count term-dict arities E t₁ t₂)
  (let* ([t₁′ (term→depth2 tvar-count term-dict arities E t₁)]
         [t₂′ (term→depth2 tvar-count term-dict arities E t₂)]
         [t₂″ (term-lookup term-dict tvar-count t₂′)]) ;; apply(g,a) → 1
    (set-box! E (append (curry-or-num t₂′ t₂″) (unbox E)))
    (if (App? t₁′)
        (CurriedEQ (App-f t₁′) (App-arg t₁′) t₂″)
        (ConstEQ t₁′ t₂″))))

;; (g a b c) → apply(apply(apply(g,a),b),c)
(define (term→depth2 tvar-count term-dict arities E t)
  (flatten-subterms tvar-count term-dict E ((curryfy arities) t)))

(define (term-lookup term-dict tvar-count sym-or-num)
  (cond [(integer? sym-or-num) ;; already given a number
         sym-or-num]
        ;; constants, symbols and applications all must be given unique numbers
        [else (hash-ref! term-dict sym-or-num
                         (λ () (let ([val (unbox tvar-count)])
                                 (set-box! tvar-count (add1 val))
                                 val)))]))

;; (App (App (App g a) b) c) → (App 2 c)
;;                             (App g a) = 1 ∧ (App 1 b) = 2,
(define (flatten-subterms tvar-count term-dict E t)
  (match t
    [(App f a) ;; (App (App . .) .) or (App 'f .)
     (let* ([f♭ (flatten-subterms tvar-count term-dict E f)]
            [a♭ (flatten-subterms tvar-count term-dict E a)]
            [f♭-num (term-lookup term-dict tvar-count f♭)]
            [a♭-num (term-lookup term-dict tvar-count a♭)])
       (set-box! E (append (curry-or-num f♭ f♭-num)
                           (curry-or-num a♭ a♭-num)
                           (unbox E)))
       (App f♭-num a♭-num))]
    [(? symbol? a)
     (term-lookup term-dict tvar-count a)]))

(define (curry-or-num a a-num)
  (cond [(App? a)
         (list (CurriedEQ (App-f a) (App-arg a) a-num))]
        [(integer? a)
         '()]
        [(Const? a)
         '()]
        [else (error "curry-or-num: internal error" a)]))

(define ((curryfy arities) t)
  (cond [(symbol? t) ;; constant
         (cond [(dict-ref arities t #f) =>
                (λ (t-ary)
                   (cond [(zero? t-ary)
                          t]
                         ;; XXX: allow equality with Booleans?
                         [(eqv? t-ary 'Boolean)
                          (error "Equality with Booleans currently unsupported")]
                         [else (error "FOL cannot use functions as values" t)]))]
               [else (error "Undeclared function symbol" t)])]
        [(pair? t) ;; function application
         (when (not (symbol? (car t)))
               (error "Only named functions may be applied" (car t)))
         (cond [(dict-ref arities (car t) #f) =>
                (λ (f-ary)
                   (cond [(zero? f-ary) ;; (g) not allowed ever. Design decision.
                          (error "Constant functions cannot be applied" (car t))]
                         [(= f-ary (length (cdr t)))
                          (curry-inside-out (car t)
                                            (map (curryfy arities)
                                                 (reverse (cdr t))))]
                         [else (error "Arity mismatch" t)]))]
               [else (error "Undeclared function symbol" (car t))])]
        [else (Const t)]))

;; Args already reversed and curryfied.
;; (g a b c) given as g '(c b a)
;; Want (App (App (App g a) b) c)
(define (curry-inside-out f args)
  (cond [(empty? (cdr args)) ;; already handled the length 0 case.
         (App f (car args))]
        [else (App (curry-inside-out f (cdr args))
                   (car args))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (dict-set!-many dict keys values)
  (for ([key keys]
        [value values])
    (dict-set! dict key value))
  dict)

(define (key-of-value dict v)
  (let loop ([itr (dict-iterate-first dict)])
    (if itr
        (if (equal? (dict-iterate-value dict itr) v)
            (dict-iterate-key dict itr)
            (loop (dict-iterate-next dict itr)))
        #f)))
        

(define (get-duplicates lst)
  (let ((seen (make-hash)))
    (let loop ((lst lst)
               (dups '()))
      (cond [(empty? lst) dups]
            [else
             (let ((num-seen (hash-ref! seen (car lst) 0)))
               (hash-set! seen (car lst) (add1 num-seen))
               (if (zero? num-seen)
                   (loop (cdr lst) dups)
                   (loop (cdr lst) (cons (car lst) dups))))]))))
