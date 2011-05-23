#lang racket

(require "data-structures.rkt"
         rackunit)

(provide (all-defined-out))

;; This file implements the translation of the input formula with arbitrary
;; function application equalities to the Currified form described in
;; Nieuwenhuis & Oliveras : Fast Congruence Closure and Extensions

;;todo
(define (prop2cnf φ)
  #f)

;; sexp → CNF
;; Prop2cnf works on sexp propositions, so that's what we build.
;; If there are any arity mismatches, or duplicate declarations,
;; we raise an error.
(define (EUF→CNF sexp)
  (match sexp
    [`((declare-fun ,Xs ,arities) ... (formula ,φ))
     (let ((duplicates (get-duplicates Xs)))
       (cond [(pair? duplicates)
              (error "Duplicate function declaration(s) ~a" duplicates)]
             [else
              (let ([term-dict (make-hash)]
                    [arity-dict (dict-set!-many (make-hash) Xs arities)]
                    [tvar-count (box 0)])
                (prop2cnf ((φ→formula-sexp tvar-count term-dict arity-dict) φ)))]))]
    [other
     (error "EUF→CNF: Unexpected input format ~a" other)]))

(define (bconn? x)
  (memq x '(and or not implies xor iff)))

(define ((φ→formula-sexp tvar-count term-dict arities) φ)
  (match φ
    [`(,(? bconn? conn) ,φs ...)
     `(,conn ,@(map (φ→formula-sexp term-dict arities) φs))]
    [`(= ,t₁ ,t₂)
     (equality→internal-equality tvar-count term-dict arities t₁ t₂)]
    [other (error "Unexpected formula form ~a" other)]))

(define (equality→internal-equality tvar-count term-dict arities t₁ t₂)
  (let*-values ([(t₁′ φs) (term→depth2 tvar-count term-dict arities t₁)]
                [(t₂′ ψs) (term→depth2 tvar-count term-dict arities t₂)]
                [(t₂″) (hash-ref! term-dict t₂′ (incbox tvar-count))]) ;; apply(g,a) → 1
    `(and ,@φs ,@ψs
          ,(if (App? t₁′)
               (CurriedEQ (App-f t₁′) (App-arg t₁′) t₂″ #f)
               (ConstEQ t₁′ t₂″ #f)))))

(define (incbox box)
  (λ ()
     (let ((val (unbox box)))
       (set-box! box (add1 val))
       val)))

;; (g a b c) → apply(apply(apply(g,a),b),c)
(define (term→depth2 tvar-count term-dict arities t)
  (flatten-subterms tvar-count term-dict ((curryfy arities) t)))

;; (App (App (App g a) b) c) → (App 2 c)
;;                             (App g a) = 1 ∧ (App 1 b) = 2,
(define (flatten-subterms tvar-count term-dict t)
  (match t
    [(App f a) ;; (App (App . .) .) or (App 'f .)
     (let*-values ([(f♭ φs) (flatten-subterms tvar-count term-dict f)]
                   [(a♭ ψs) (flatten-subterms tvar-count term-dict a)]
                   [(f♭-num) (hash-ref! term-dict f♭ (incbox tvar-count))]
                   [(a♭-num) (hash-ref! term-dict a♭ (incbox tvar-count))])                   
       (values (App f♭-num a♭-num)
               (append (curry-or-num f♭ f♭-num)
                       (curry-or-num a♭ a♭-num)
                       φs
                       ψs)))]
    [(? symbol? a)
     (values (hash-ref! term-dict a (incbox tvar-count)) '())]))

(define (curry-or-num a a-num)
  (cond [(App? a)
         (list (CurriedEQ (App-f a) (App-arg a) a-num #f))]
        [(integer? a)
         '()]
        [else (error "curry-or-num: internal error ~a" a)]))

(define ((curryfy arities) t)
  (cond [(symbol? t) ;; constant
         (cond [(dict-ref arities t #f) =>
                (λ (t-ary)
                   (if (zero? t-ary)
                       t
                       (error "FOL cannot use functions as values ~a" t)))]
               [else (error "Undeclared function symbol ~a" t)])]
        [(pair? t) ;; function application
         (when (not (symbol? (car t)))
               (error "Only named functions may be applied ~a" (car t)))
         (cond [(dict-ref arities (car t) #f) =>
                (λ (f-ary)
                   (cond [(zero? f-ary) ;; (g) not allowed ever. Design decision.
                          (error "Constant functions cannot be applied ~a" (car t))]
                         [(= f-ary (length (cdr t)))
                          (curry-inside-out (car t)
                                            (map (curryfy arities)
                                                 (reverse (cdr t))))]
                         [else (error "Arity mismatch ~a" t)]))]
               [else (error "Undeclared function symbol ~a" (car t))])]
        [else (error "Expected symbol or (f args ...). Got ~a" t)]))

;; Args already reversed and curryfied.
;; (g a b c) given as g '(c b a)
;; Want (App (App (App g a) b) c)
(define (curry-inside-out f args)
  (cond [(empty? (cdr args)) ;; already handled the length 0 case.
         (App f (car args))]
        [else (App (curry-inside-out f (cdr args))
                   (car args))]))

(define (dict-set!-many dict keys values)
  (for ([key keys]
        [value values])
    (dict-set! dict key value))
  dict)

(define (get-duplicates lst)
  (let ((seen (make-hash)))
    (let loop ((lst lst)
               (dups '()))
      (cond [(empty? lst) dups]
            [else
             (let ((num-seen (hash-ref! seen (car lst) 0)))
               (hash-set! seen (car lst) (add1 num-seen))
               (if (zero? num-seen)
                   (loop (cdr lst) (cons (car lst) dups))
                   (loop (cdr lst) dups)))]))))
