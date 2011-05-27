#lang racket

(require "smt-interface.rkt"
	 "statistics.rkt"
         "bthash.rkt"
         "struct-with-set.rkt"
	 "heuristic-constants.rkt"
	 "learned-clauses.rkt")

(provide (all-defined-out))

(struct-with-set SAT (clauses ;; ClauseID ↦ Clause
                      learned-clauses ;; allowed to be mutable since only a heuristic
                      variables
                      sats-per-dec-lev ;; (Listof Natural)
                      ;; numbers that must be maintained
                      statistics))
(struct SMT (sat T-State strength seed))

(define (set-SMT-sat smt sat)
  (SMT sat
       (SMT-T-State smt)
       (SMT-strength smt)
       (SMT-seed smt)))

(define (set-SMT-T-State smt t-state)
  (SMT (SMT-sat smt)
       t-state
       (SMT-strength smt)
       (SMT-seed smt)))

;; accessors for SMT
(define (SMT-clauses smt) (SAT-clauses (SMT-sat smt)))
(define (SMT-learned-clauses smt) (SAT-learned-clauses (SMT-sat smt)))
(define (SMT-variables smt) (SAT-variables (SMT-sat smt)))
(define (SMT-statistics smt) (SAT-statistics (SMT-sat smt)))
;; statistics accessors
(define (SMT-decision-level smt) (SAT-Stats-decision-level (SMT-statistics smt)))

;; different exceptions that pass the current smt instance for fast backtracking
;; (others are externally available, in smt-interface.rkt)
(struct bail-exn (smt))
(struct restart-exn (smt))

(define (set-SMT-statistics smt val)
  (set-SMT-sat smt (set-SAT-statistics (SMT-sat smt) val)))

(define (set-SMT-decision-level smt val)
  (SMT-set-statistics smt (set-decision-level (SMT-statistics smt) val)))

;; A DimacsLit is a nonzero integer
;; A valuation is #t, #f or 'unassigned

;; We'll store a vector of clauses, and a vector of learned clauses
;; A Clause is a   Vector of Literals * watched Literal 1 * watched Literal 2

(struct clause (literals watched1 watched2) #:mutable)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A Literal is a  Variable * Boolean
(struct literal (varid polarity) #:transparent)

;; A Variable is a  
;; DimacsLit * 
;; List of refs to Clauses * List of Refs to Clauses * 
;; negative activation Float * positive activation Float * 
;; igraph node ref * valuation

(struct var-heuristic (pos-activation ; for VSIDS decision heuristic (Float)
                       neg-activation
                       pos-watched ; for 2-watched literal heuristic (
                       neg-watched) #:mutable)
(struct-with-set var (heuristic ; info that can be arbitrary and not affect soundness
                      timestamp ; for VSIDS decision heuristic
                      dec-lev ; for implication graph information
                      antecedent ; #f + Clause + (SMT -> T-State * Clause)
                      value) ; valuation
                 #:transparent)

(define (make-n-vars n)
  (make-bthash
   (build-list n
               (lambda (idx)
                 (cons (add1 idx) ;; key
                       (var (var-heuristic INITIAL_ACTIVITY INITIAL_ACTIVITY '() '())
                            #f ;; timestamp
                            #f ;; dec-lev
                            #f ;; antecedent
                            'unassigned))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Clause functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (clause-size clause)
  (vector-length (clause-literals clause)))

(define (nth-literal clause n)
  (vector-ref (clause-literals clause) n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Literal functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-var-value vars varid)
  (var-value (bthash-ref vars varid)))

(define (literal-var vars literal)
  (bthash-ref vars (dimacs-lit->dimacs-var literal)))

(define (var-unassigned? vars var)
  (eqv? 'unassigned (get-var-value vars var)))

(define (polarize-valuation valuation polarity)
  (if (symbol? valuation) ; should be 'unassigned
      valuation
      ;; odd. if polarity, valuation. o.w. (not valuation).
      (eqv? valuation polarity)))

(define (literal-valuation vars literal)
  (polarize-valuation (var-value (literal-var vars literal))
                      (dimacs-polarity literal)))

(define (literal-unassigned? vars literal)
  (var-unassigned? vars (dimacs-lit->dimacs-var literal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Literal getters/setters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (literal-antecedent vars literal)
  (var-antecedent (bthash-ref vars (dimacs-lit->dimacs-var literal))))

(define (literal-dec-lev vars literal)
  (var-dec-lev (bthash-ref vars (dimacs-lit->dimacs-var literal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DIMACS format interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; assigned var -> DimacsLit
;; Used for extracting the partial model
(define (var->dimacs vars varid)
  (match (get-var-value vars varid)
    [#t (add1 varid)]
    [#f (- (add1 varid))]
    ['unassigned (error "[Internal error] var->dimacs called on unassigned variable")]))