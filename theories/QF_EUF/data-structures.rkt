#lang racket

(require "../../struct-with-set.rkt"
         "../../bthash.rkt")
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

;; A Term is a Symbol, a Const or an App
(struct Const (c) #:transparent) ;; c : Any
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
