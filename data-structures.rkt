#lang racket

(require "smt-interface.rkt")
(require "heuristic-constants.rkt")
(require "dimacs.rkt")
(require "learned-clauses.rkt")

(provide (all-defined-out))

(struct SAT (clauses learned-clauses variables partial-assignment
	     ;; numbers that must be maintained
	     decision-level assigned-order 
	     forget-threshold restart-threshold
	     conflicts-since-last-restart))
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
(define (SMT-decision-level smt) (SAT-decision-level (SMT-sat smt)))
(define (SMT-assigned-order smt) (SAT-assigned-order (SMT-sat smt)))

;; different exceptions that pass the current smt instance for fast backtracking
;; (others are externally available, in smt-interface.rkt)
(struct bail-exn (smt))
(struct restart-exn (smt))

(define (initialize cnf t-state strength [seed #f])
  (match cnf
   ;; dimacs-style:
   [`(,var-count ,clause-count ((,lit ...) ...))
    (let ((vars (make-n-vars var-count)))
      (SMT (SAT (list->vector (map (dimacs-lits->clause vars) lit))
		(empty-learned-clauses)
		vars
		'(())
		0 ;; decision level
		0 ;; assigned order
		FORGET_THRESHOLD_INITIAL_PERCENTAGE
		RESTART_INITIAL_THRESHOLD
		0) ;; conflicts since last restart
	   t-state
	   strength
	   seed))]))

(define (set-partial-assignment sat val)
  (SAT (SAT-clauses sat)
       (SAT-learned-clauses sat)
       (SAT-variables sat)
       val
       (SAT-decision-level sat)
       (SAT-assigned-order sat)
       (SAT-forget-threshold sat)
       (SAT-restart-threshold sat)
       (SAT-conflicts-since-last-restart sat)))
(define (SMT-set-partial-assignment smt val)
  (new-SAT smt (set-partial-assignment (SMT-sat smt) val)))

(define (set-decision-level sat val)
  (SAT (SAT-clauses sat)
       (SAT-learned-clauses sat)
       (SAT-variables sat)
       (SAT-partial-assignment sat)
       val
       (SAT-assigned-order sat)
       (SAT-forget-threshold sat)
       (SAT-restart-threshold sat)
       (SAT-conflicts-since-last-restart sat)))
(define (SMT-set-decision-level smt val)
  (new-SAT smt (set-decision-level (SMT-sat smt) val)))

(define (set-assigned-order sat val)
  (SAT (SAT-clauses sat)
       (SAT-learned-clauses sat)
       (SAT-variables sat)
       (SAT-partial-assignment sat)
       (SAT-decision-level sat)
       val
       (SAT-forget-threshold sat)
       (SAT-restart-threshold sat)
       (SAT-conflicts-since-last-restart sat)))
(define (SMT-set-assigned-order smt val)
  (new-SAT smt (set-assigned-order (SMT-sat smt) val)))

(define (inc-assigned-order sat)
  (set-assigned-order sat (+ 1 (SAT-assigned-order sat))))
(define (SMT-inc-assigned-order smt)
  (new-SAT smt (inc-assigned-order (SMT-sat smt))))

;; Helpers defined in terms of setters:

(define (satisfy-literal! sat literal)
  (begin (set-var-value! (literal-var literal) (literal-polarity literal))
         (set-var-timestamp! (literal-var literal) (SAT-assigned-order sat))
         (add-to-current-decision-level (inc-assigned-order sat) literal)))

(define (SMT-satisfy-literal! smt literal)
  (SMT (satisfy-literal! (SMT-sat smt) literal)
       ((T-Satisfy) (SMT-T-State smt) (literal->dimacs literal))
       (SMT-strength smt)
       (SMT-seed smt)))

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

;; An IGraph is a List of IGraph Nodes

;; An IGraph node is a  decision level Natural * antecedent Ref to Clause
(struct node (dec-lev antecedent))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A Literal is a  Variable * Boolean
(struct literal (var polarity) #:transparent)

;; A Variable is a  List of refs to Clauses * List of Refs to Clauses * negative activation Float * positive activation Float * igraph node ref * valuation * boolean

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

(define (literal-timestamp literal)
  (var-timestamp (literal-var literal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Watchedness getters/setters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (literal-watched literal)
  (if (literal-polarity literal)
      (var-pos-watched (literal-var literal))
      (var-neg-watched (literal-var literal))))
(define (literal-activation literal)
  (if (literal-polarity literal)
      (var-pos-activation (literal-var literal))
      (var-neg-activation (literal-var literal))))
(define (set-literal-watched! literal val)
  (if (literal-polarity literal)
      (set-var-pos-watched! (literal-var literal) val)
      (set-var-neg-watched! (literal-var literal) val)))
(define (set-literal-activation! literal val)
  (if (literal-polarity literal)
      (set-var-pos-activation! (literal-var literal) val)
      (set-var-neg-activation! (literal-var literal) val)))
(define (set-literal-igraph-node! literal val)
  (set-var-igraph-node! (literal-var literal) val))

(define (literal-antecedent literal)
  (node-antecedent (var-igraph-node (literal-var literal))))

(define (literal-dec-lev literal)
  (node-dec-lev (var-igraph-node (literal-var literal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for manipulating clauses for 2-watched literal heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (add-literal-watched! clause literal)
  (set-literal-watched! literal
                        (cons clause (literal-watched literal))))

(define (rem-literal-watched! clause literal)
  (set-literal-watched! literal 
                        (remove clause (literal-watched literal) eqv?)))

(define (clause-other-watched clause literal)
  (cond [(literal-eq? literal (clause-watched1 clause)) (clause-watched2 clause)]
        [(literal-eq? literal (clause-watched2 clause)) (clause-watched1 clause)]
        [else (error 'clause-other-watched "That's not being watched at all.")]))

(define (clause-watched-swap! clause cur-watched new-watched)
  (cond [(literal-eq? cur-watched (clause-watched1 clause))
         (set-clause-watched1! clause new-watched)]
        [(literal-eq? cur-watched (clause-watched2 clause))
         (set-clause-watched2! clause new-watched)]))

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

; DimacsLit -> Literal
(define ((dimacs-lit->literal variables) dimacs-lit)
  (literal 
   (vector-ref variables (- (dimacs-lit->dimacs-var dimacs-lit) 1)) ; -1 is variable 0
   (dimacs-polarity dimacs-lit))) ; -1 is negated. False polarity

; list of DimacsLit -> Clause
(define ((dimacs-lits->clause variables) dimacs-lits)
  (cond
   [(empty? dimacs-lits)
    (error 'dimacs-lits->clause 
           "There is an empty clause.  I don't think you will be satisfied.")]
   [else 
    (let* ((literals (list->vector (map (dimacs-lit->literal variables) dimacs-lits)))
	   (w1 (vector-ref literals 0))
	   (w2 (vector-ref literals (- (vector-length literals) 1)))
	   (C (clause literals w1 w2)))
      (add-literal-watched! C w1) ;it's safe for a clause to appear twice watched lists
      (add-literal-watched! C w2)
      C)]))