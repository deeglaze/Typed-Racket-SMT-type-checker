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

;; A Term is a Var, a Const or an App
(struct Const (c) #:transparent) ;; c : Any
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

(define (internal-eq? x)
  (or (CurriedEQ? x)
      (ConstEQ? x)))

;; l and r are CurriedEQ
(struct EQpair (l r) #:transparent)

;; Graph nodes for the proof forest
;; Option TVar, Natural, Option (U EQpair ConstEQ) (#f if root)
(struct Node (next size outlabel))
(define (set-Node-size node size)
  (Node (Node-next node)
        size
        (Node-outlabel node)))

;; The entire theory solver state.

(struct-with-set EUF-state (equalities ;; DimacsVar ↦ Equality
                            untranslator ;; DimacsLit -> Option S-exp
                            satisfaction-level ;; Natural that gets bumped each T-Satisfy.
                            last-consistency-check ;; satisfaction-level the last T-Consistent? was called
                            tmp-tv ;; Natural (used for flattening intermediate equalities)
                            last-sat ;; Option Equality (used for lightweight T-Consistent?)
                            ;; the rest of these are backtrackable hash tables
                            eqlit ;; Equality ↦ Option DimacsLit
                            backjump-table ;; Satisfaction-level ↦ DimacsVar
                            representative ;; TVar ↦ TVar (if not hashed, then self-represented)
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
        (loop (let ([x (car x)] ...)
                (seq/EUF-state t-state body ...))
              (cdr x) ...))))

;; useful for stacking changes at different satisfaction levels
;; to backtrack easily.
(struct-with-set aged-hash (timestamp hash) #:transparent)
;; A backtrack-hash as a (Listof aged-hash) such that the most recent
;; hash is first, then second most recent, etc.

(define (aged-hash-ref ahash key [failure #f])
  (hash-ref (aged-hash-hash ahash) key failure))
(define (aged-hash-has-key? ahash key)
  (hash-has-key? (aged-hash-hash ahash) key))
(define (aged-hash-set ahash key value)
  (set-aged-hash-hash ahash (hash-set (aged-hash-hash ahash) key value)))

;; We just want the most recent value for the given key
(define (bthash-ref bthash key [failure #f])
  (if (pair? bthash)
      (aged-hash-ref (car bthash) key failure)
      failure))

;; INVARIANT: (pair? bthash)
(define (bthash-set bthash key value)
  (cons (aged-hash-set (car bthash) key value)
        (cdr bthash)))

(define (bthash-iterate-first bthash)
  (and (pair? bthash)
       (hash-iterate-first (aged-hash-hash (car bthash)))))
(define (bthash-iterate-next bthash itr)
  (hash-iterate-next (aged-hash-hash (car bthash)) itr))
(define (bthash-iterate-key bthash itr)
  (hash-iterate-key (aged-hash-hash (car bthash)) itr))
(define (bthash-iterate-value bthash itr)
  (hash-iterate-value (aged-hash-hash (car bthash)) itr))


;; remove all ahashes with timestamp >= given timestamp
(define (bthash-backtrack-to bthash timestamp)
  (or (memf (λ (ahash) (< (aged-hash-timestamp ahash) timestamp)) bthash)
      ;; everything is wiped out.
      '()))

;; INVARIANT: (empty? bthash) or (> timestamp (aged-hash-timestamp (car bthash)))
(define (bthash-new-age bthash timestamp)
  (if (empty? bthash)
      (list (aged-hash timestamp (make-immutable-hash '())))
      (cons (aged-hash timestamp (aged-hash-hash (car bthash)))
            bthash)))