#lang racket

(require "smt-interface.rkt"
	 "statistics.rkt"
	 "heuristic-constants.rkt"
	 "learned-clauses.rkt")

(provide (all-defined-out))

(struct SAT (clauses learned-clauses variables partial-assignment
	     ;; numbers that must be maintained
	     statistics))
(struct SMT (sat T-State strength seed))

(define (new-SAT smt sat)
  (SMT sat
       (SMT-T-State smt)
       (SMT-strength smt)
       (SMT-seed smt)))

(define (new-T-State smt t-state)
  (SMT (SMT-sat smt)
       t-state
       (SMT-strength smt)
       (SMT-seed smt)))

;; accessors for SMT
(define (SMT-clauses smt) (SAT-clauses (SMT-sat smt)))
(define (SMT-learned-clauses smt) (SAT-learned-clauses (SMT-sat smt)))
(define (SMT-variables smt) (SAT-variables (SMT-sat smt)))
(define (SMT-partial-assignment smt) (SAT-partial-assignment (SMT-sat smt)))
(define (SMT-statistics smt) (SAT-statistics (SMT-sat smt)))
;; statistics accessors
(define (SMT-decision-level smt) (SAT-Stats-decision-level (SMT-statistics smt)))

;; different exceptions that pass the current smt instance for fast backtracking
;; (others are externally available, in smt-interface.rkt)
(struct bail-exn (smt))
(struct restart-exn (smt))

(define (set-partial-assignment sat val)
  (SAT (SAT-clauses sat)
       (SAT-learned-clauses sat)
       (SAT-variables sat)
       val
       (SAT-statistics sat)))
(define (SMT-set-partial-assignment smt val)
  (new-SAT smt (set-partial-assignment (SMT-sat smt) val)))

(define (SAT-set-statistics sat val)
  (SAT (SAT-clauses sat)
       (SAT-learned-clauses sat)
       (SAT-variables sat)
       (SAT-partial-assignment sat)
       val))
(define (SMT-set-statistics smt val)
  (new-SAT smt (SAT-set-statistics (SMT-sat smt) val)))

(define (SMT-set-decision-level smt val)
  (SMT-set-statistics smt (set-decision-level (SMT-statistics smt) val)))

;; Helpers defined in terms of setters:

(define (add-to-current-decision-level sat literal)
  (set-partial-assignment 
   sat
   (cons (cons literal (first (SAT-partial-assignment sat)))
         (rest (SAT-partial-assignment sat)))))
(define (SMT-add-to-current-decision-level smt literal)
  (SMT-set-partial-assignment smt literal))

;; A Partial Assignment is a List of List of Literals
;; A DimacsLit is a nonzero integer
;; A valuation is #t, #f or 'unassigned

;; We'll store a vector of clauses, and a vector of learned clauses
;; A Clause is a   Vector of Literals * watched Literal 1 * watched Literal 2

(struct clause (literals watched1 watched2) #:mutable)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; IMPLICATION GRAPHS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An IGraph node is a  decision level Natural * antecedent Ref to Clause
(struct node (dec-lev antecedent))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A Literal is a  Variable * Boolean
(struct literal (var polarity) #:transparent)

;; A Variable is a  
;; DimacsLit * 
;; List of refs to Clauses * List of Refs to Clauses * 
;; negative activation Float * positive activation Float * 
;; igraph node ref * valuation 

(struct var 
  (name ; index into variables vector
   pos-watched neg-watched ; for 2-watched literal heuristic
   pos-activation neg-activation timestamp ; for VSIDS decision heuristic
   igraph-node ; for implication graph information
   value) ; for constant time valuation lookup
   #:mutable #:transparent)

(define (make-n-vars n)
  (build-vector n (lambda (idx) (var (+ 1 idx) '() '() 
				     INITIAL_ACTIVITY INITIAL_ACTIVITY
				     #f #f 'unassigned))))

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

(define (literal-name lit)
  (var-name (literal-var lit)))

(define (literal-eq? l1 l2)
  (and (eqv? (literal-var l1) (literal-var l2))
       (eq? (literal-polarity l1) (literal-polarity l2))))

(define (literal-eq-in-var? l1 l2)
  (eqv? (literal-var l1) (literal-var l2)))

(define (negate-literal lit)
  (literal (literal-var lit) (not (literal-polarity lit))))

(define (var-unassigned? var)
  (eqv? 'unassigned (var-value var)))

(define (polarize-valuation valuation polarity)
  (if (symbol? valuation) ; should be 'unassigned
      valuation
      ;; odd. if polarity, valuation. o.w. (not valuation).
      (eqv? valuation polarity)))

(define (literal-valuation literal)
  (polarize-valuation (var-value (literal-var literal))
                      (literal-polarity literal)))

(define (literal-unassigned? literal)
  (var-unassigned? (literal-var literal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Literal getters/setters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (set-literal-igraph-node! literal val)
  (set-var-igraph-node! (literal-var literal) val))

(define (literal-antecedent literal)
  (node-antecedent (var-igraph-node (literal-var literal))))

(define (literal-dec-lev literal)
  (node-dec-lev (var-igraph-node (literal-var literal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DIMACS format interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Literal -> DimacsLit
(define (literal->dimacs literal)
  (if (literal-polarity literal)
      (literal-name literal)
      (- (literal-name literal))))

;; assigned var -> DimacsLit
;; Used for extracting the partial model
(define (var->dimacs v)
  (match (var-value v)
    [#t (var-name v)]
    [#f (- (var-name v))]
    ['unassigned (error "[Internal error] var->dimacs called on unassigned variable")]))