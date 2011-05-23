#lang racket

(require "struct-with-set.rkt")
(provide (all-defined-out))

;; QF_EUF: Quantifier free theory of uninterpreted functions with equality
;; UNSORTED FOL
;; Grammar of formulae
;; φ ::= φ bconn φ | ¬ φ | t = t | t ≠ t
;; bconn ::= ∨ | ∧ | ⇒
;; t ::= x | f(t, ...)

;; Each function symbol has an arity that must be declared.
;; (declare-fun f 3) means that f must take 3 arguments.

;; Representation structures for arbitrary input formulae:

;; A Term is a Var or an App
(struct Var (x) #:transparent) ;; x : Natural
(struct App (f arg) #:transparent) ;; f : Symbol, args : Term
;; l and r are Terms.
(struct Equality (l r) #:transparent)

;; Internal representation structures after transformation:
;; A TVar is a Natural
(define TVar? exact-nonnegative-integer?)

;; f(g,arg) = a
(struct CurriedEQ (g arg a) #:transparent) ;; TVars
;; a = b
(struct ConstEQ (a₁ a₂) #:transparent) ;; TVars

;; l and r are CurriedEQ
(struct EQpair (l r) #:transparent)

;; Graph nodes for the proof forest
(struct Node ([next #:mutable] ;; Option Node      ;; #f if root
              [size #:mutable] ;; Natural
              [out-label #:mutable])) ;; (U EQpair ConstEQ #f) ;; #f if root

;; The entire theory solver state.

(struct-with-set EUF-state (equalities ;; DimacsVar ↦ Equality
;;                            to-propagate ;; DimacsVar ↦ Boolean (#f iff the equality has been propagated)
                            eqlit ;; Equality ↦ DimacsLit
                            backjump-table ;; Satisfaction-level ↦ (Listof DimacsVar)
                            satisfaction-level ;; Natural that gets bumped each T-Satisfy.
                            last-consistency-check ;; satisfaction-level the last T-Consistent? was called
                            ;; the rest of these are backtrackable hash tables
                            representative ;; TVar ↦ TVar
                            classes        ;; TVar ↦ Listof TVar
                            uses           ;; TVar ↦ Listof CurriedEQ
                            lookup         ;; (Pair TVar TVar) ↦ CurriedEQ (Var₁ ≤ Var₂)
                            proof          ;; TVar ↦ Node
                            ) #:transparent)

(define-syntax-rule (seq/EUF-state t-state e ... tail)
  (let* ([t-state e] ...)
    tail))

(define-syntax-rule (for/EUF-state t-state ([x e] ...) body ...)
  (let loop ([t-state t-state]
             [x e] ...)
    (if (or (empty? x) ...)
        t-state
        (loop (seq/EUF-state t-state body ...) (cdr x) ...))))

;; useful for stacking changes at different satisfaction levels
;; to backtrack easily.
(struct-with-set aged-hash (timestamp hash))
;; A backtrack-hash as a (Listof aged-hash) such that the most recent
;; hash is first, then second most recent, etc.

(define (aged-hash-ref ahash key [failure #f])
  (hash-ref (aged-hash-hash hash) key failure))
(define (aged-hash-has-key? ahash key)
  (hash-has-key? (aged-hash-hash hash) key))
(define (aged-hash-set ahash key value)
  (set-aged-hash-hash ahash (hash-set (aged-hash-hash hash) key value)))

;; We just want the most recent value for the given key
(define (bthash-ref bthash key)
  (and (pair? bthash)
       (aged-hash-ref (car bthash) key)))

;; INVARIANT: (pair? bthash)
(define (bthash-set bthash key value)
  (aged-hash-set (car bthash) key value))

;; remove all ahashes with timestamp >= given timestamp
(define (bthash-backtrack-to bthash timestamp)
  (memf (λ (ahash) (< (aged-hash-timestamp ahash) timestamp)) bthash))

;; INVARIANT: (empty? bthash) or (> timestamp (aged-hash-timestamp (car bthash)))
(define (bthash-new-age bthash timestamp)
  (if (empty? bthash)
      (list (aged-hash timestamp (make-immutable-hash)))
      (cons (aged-hash timestamp (aged-hash-hash (car bthash)))
            bthash)))