#lang racket

(require "data-structures.rkt")
(require "learned-clauses.rkt")
(require "heuristic-constants.rkt")

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for learning clauses with VSIDS heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (SAT-set-learned-clauses sat val)
  (SAT (SAT-clauses sat)
       val
       (SAT-variables sat)
       (SAT-partial-assignment sat)
       (SAT-decision-level sat)
       (SAT-assigned-order sat)
       (SAT-forget-threshold sat)
       (SAT-restart-threshold sat)
       (SAT-conflicts-since-last-restart sat)))
(define (SMT-set-learned-clauses smt val)
  (new-SAT (SAT-set-learned-clauses (SMT-sat smt) val)))

;; currently stateful. Might change later, so keep interface
(define (learn-clause sat learned-clause)
  (add-learned-clause! (SAT-learned-clauses sat)
		       learned-clause))
(define (SMT-learn-clause smt clause)
  ;; shadowing... ick.
  (let ((learned-clause (learned-clause clause INITIAL_ACTIVITY #f)))
    (learn-clause (SMT-sat smt) learned-clause)
    (values smt learned-clause)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for manipulating clauses for VSIDS heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (some-clause->clause C)
  (if (learned-clause? C)
      (learned-clause-clause C)
      C))

;; for interacting with the theory solver. When a literal
;; is implied, it returns a thunk that will build an explanation
;; of why it is true.
(define (literal-explanation smt literal)
  (lemma->lits smt (literal-antecedent literal)))

;; Clause -> Bool
;; should only be called during conflict analysis, once per clause
(define (lemma->lits smt lemma)
  (let ((lits (cond [(procedure? lemma)
		     (lemma smt)]
		    [else (inc-clause-activation! lemma)])))
    (increase-scores! lits)
    lits))

(define (inc-literal-activation! literal)
  (set-literal-activation! literal (+ ACTIVITY_INC 
				      (literal-activation literal))))

(define (increase-scores! literals [idx 0])
  (if (= idx (vector-length literals))
      (void)
      (begin (inc-literal-activation! (vector-ref literals idx))
	     (increase-scores! literals (+ 1 idx)))))

; slash-all-literals!: Vector<var> -> unit
; Exponentially decay activation of all literals. For VSIDS heuristic
(define (slash-all-literals! variables)
  (let walk ((idx 0))
    (if (= idx (vector-length variables))
	(void)
	(let ((var (vector-ref variables idx)))
	  (begin (set-var-pos-activation! var (/ (var-pos-activation var) ACTIVITY_DROPOFF))
		 (set-var-neg-activation! var (/ (var-neg-activation var) ACTIVITY_DROPOFF))
		 (walk (+ 1 idx)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for manipulating clauses for clause forgetting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (SMT-forget-threshold smt)
  (SAT-forget-threshold (SMT-sat smt)))
(define (SMT-restart-threshold smt)
  (SAT-restart-threshold (SMT-sat smt)))
(define (SMT-conflicts-since-last-restart smt)
  (SAT-conflicts-since-last-restart (SMT-sat smt)))

(define (SMT-bump-forget-threshold smt)
  (let ((sat (SMT-sat smt)))
    (new-SAT smt
	     (SAT (SAT-clauses sat)
		  (SAT-learned-clauses sat)
		  (SAT-variables sat)
		  (SAT-partial-assignment sat)
		  (SAT-decision-level sat)
		  (SAT-assigned-order sat)
		  (* (SAT-forget-threshold sat)
		     FORGET_THRESHOLD_COEFFICIENT)
		  (SAT-restart-threshold sat)
		  (SAT-conflicts-since-last-restart smt)))))
(define (SMT-bump-restart-threshold smt)
  (let ((sat (SMT-sat smt)))
    (new-SAT smt
	     (SAT (SAT-clauses sat)
		  (SAT-learned-clauses sat)
		  (SAT-variables sat)
		  (SAT-partial-assignment sat)
		  (SAT-decision-level sat)
		  (SAT-assigned-order sat)
		  (SAT-forget-threshold sat)
		  (* (SAT-restart-threshold sat)
		     RESTART_COEFFICIENT)
		  (SAT-conflicts-since-last-restart smt)))))
(define (SMT-set-conflicts-since-last-restart smt val)
  (let ((sat (SMT-sat smt)))
    (new-SAT smt
	     (SAT (SAT-clauses sat)
		  (SAT-learned-clauses sat)
		  (SAT-variables sat)
		  (SAT-partial-assignment sat)
		  (SAT-decision-level sat)
		  (SAT-assigned-order sat)
		  (SAT-forget-threshold sat)
		  (SAT-restart-threshold sat)
		  val))))

;; increase activity and return literals
(define (inc-clause-activation! clause)
  (if (learned-clause? clause)
      (begin
	(set-learned-clause-activation! clause
					(+ ACTIVITY_INC
					   (learned-clause-activation clause)))
	(increase-scores! (clause-literals (learned-clause-clause clause)))
	(clause-literals (learned-clause-clause clause)))
      (begin (increase-scores! (clause-literals clause))
	     (clause-literals clause))))

(define (SMT-forget-policy smt)
  (let ((num-learned (learned-clauses-count (SMT-learned-clauses smt)))
	(orig-size   (vector-length (SMT-clauses smt))))
    (if (num-learned . <= . (* orig-size (SMT-forget-threshold smt)))
	smt ;; not enough clauses to start forgetting
	(let* ((smt (SMT-set-learned-clauses
		     (slash-all-learned-clauses ;; Exponentially decay
		      (forget-up-to-bound! ;; Kill the weaklings
		       (SMT-learned-clauses smt)
		       (* orig-size FORGET_THRESHOLD_RETAIN_PERCENTAGE)))))
	       (smt (SMT-bump-forget-threshold smt)))
	  smt))))

(define (SMT-restart-policy smt)
  (if ((SMT-conflicts-since-last-restart smt) . < . (SMT-restart-threshold smt))
      smt
      (let* ((smt (SMT-set-conflicts-since-last-restart smt 0))
	     (smt (SMT-bump-restart-threshold smt)))
	(raise (restart-exn smt)))))

(define (SMT-on-conflict smt)
  (slash-all-literals! (SAT-variables (SMT-sat smt)))
  (let* ((smt (SMT-set-conflicts-since-last-restart 
	       smt
	       (+ 1 (SMT-conflicts-since-last-restart smt))))
	 (smt (SMT-forget-policy smt)))
    (SMT-restart-policy smt)))


