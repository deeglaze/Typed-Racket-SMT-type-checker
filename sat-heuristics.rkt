#lang racket

(require "data-structures.rkt"
	 "statistics.rkt"
	 "learned-clauses.rkt"
	 "heuristic-constants.rkt")

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for First-UIP heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (SMT-assigned-order smt) (SAT-Stats-assigned-order (SMT-statistics smt)))
(define (SMT-set-assigned-order smt val)
  (SMT-set-statistics smt (set-assigned-order (SMT-statistics smt) val)))

(define (inc-assigned-order stats)
  (set-assigned-order stats (+ 1 (SAT-Stats-assigned-order stats))))
(define (SAT-inc-assigned-order sat)
  (SAT-set-statistics sat 
		      (set-assigned-order (SAT-statistics sat)
					  (+ 1 (SAT-Stats-assigned-order (SAT-statistics sat))))))
(define (SMT-inc-assigned-order smt)
  (SMT-set-statistics smt (inc-assigned-order (SMT-statistics smt))))

(define (literal-timestamp literal)
  (var-timestamp (literal-var literal)))

; returns the literal assigned most recently in the given vector of literals
(define (choose-latest-literal literals)
  (let find-recent ((idx 1)
                    (candidate (vector-ref literals 0)))
    (if (= idx (vector-length literals))
        candidate
        (let* ((nthlit (vector-ref literals idx)))              
          (if ((literal-timestamp nthlit) . > . (literal-timestamp candidate))
              (find-recent (+ 1 idx) nthlit)
              (find-recent (+ 1 idx) candidate))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for learning clauses with VSIDS heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (SAT-set-learned-clauses sat val)
  (SAT (SAT-clauses sat)
       val
       (SAT-variables sat)
       (SAT-partial-assignment sat)
       (SAT-statistics sat)))
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
;; Functions for manipulating literals/clauses for VSIDS heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (some-clause->clause C)
  (if (learned-clause? C)
      (learned-clause-clause C)
      C))

(define (set-literal-activation! literal val)
  (if (literal-polarity literal)
      (set-var-pos-activation! (literal-var literal) val)
      (set-var-neg-activation! (literal-var literal) val)))

(define (literal-activation literal)
  (if (literal-polarity literal)
      (var-pos-activation (literal-var literal))
      (var-neg-activation (literal-var literal))))

;; for interacting with the theory solver. When a literal
;; is implied, it returns a thunk that will build an explanation
;; of why it is true.
(define (literal-explanation smt literal)
  (lemma->lits smt (literal-antecedent literal)))

;; Clause -> Bool
;; should only be called during conflict analysis, once per clause
;; XXX: Also for learned clause VSIDS heuristic!
(define (lemma->lits smt lemma)
  (let-values ([(t-state lits)
                (cond [(procedure? lemma)
                       (lemma smt)]
                      [else (values (SMT-T-State smt) (inc-clause-activation! lemma))])])
    (increase-scores! lits)
    (values (new-T-State smt t-state)
            lits)))

(define (inc-literal-activation! literal)
  (set-literal-activation! literal (+ ACTIVITY_INC 
				      (literal-activation literal))))

(define (increase-scores! literals [idx 0])
  (unless (= idx (vector-length literals))
          (begin (inc-literal-activation! (vector-ref literals idx))
                 (increase-scores! literals (+ 1 idx)))))

; slash-all-literals!: Vector<var> -> unit
; Exponentially decay activation of all literals. For VSIDS heuristic
(define (slash-all-literals! variables)
  (let walk ((idx 0))
    (unless (= idx (vector-length variables))
            (let ((var (vector-ref variables idx)))
              (begin (set-var-pos-activation! var (/ (var-pos-activation var) ACTIVITY_DROPOFF))
                     (set-var-neg-activation! var (/ (var-neg-activation var) ACTIVITY_DROPOFF))
                     (walk (+ 1 idx)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for manipulating literals for 2-watched literal heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (literal-watched literal)
  (if (literal-polarity literal)
      (var-pos-watched (literal-var literal))
      (var-neg-watched (literal-var literal))))

(define (set-literal-watched! literal val)
  (if (literal-polarity literal)
      (set-var-pos-watched! (literal-var literal) val)
      (set-var-neg-watched! (literal-var literal) val)))

(define (add-literal-watched! clause literal)
  (set-literal-watched! literal
                        (mcons clause (literal-watched literal))))

#|
;; XXX: This should be deprecated for a better representation of clauses a 
;; literal is watched in.
 (define (rem-literal-watched! clause literal)
   (set-literal-watched! literal 
                         (remove clause (literal-watched literal) eqv?)))
|#

;; We use a mutable list to keep track of the clauses a literal is watched in.
;; In order to do correct traversals with deletion, we abstract this into
;; a small iterator interface.
(struct watched-list-iterator (literal last current))
(define (watched-iterate-first literal)
  (let ((watched (literal-watched literal)))
    (and (not (empty? watched))
	 (watched-list-iterator literal #f watched))))

;; assumes no deletion
(define (watched-iterate-next itr)
  (let* ((current (watched-list-iterator-current itr))
	 (rest (mcdr current)))
    (and (not (empty? rest))
	 (watched-list-iterator (watched-list-iterator-literal itr)
				current 
				rest))))

;; assumes no next
(define (watched-iterate-remove itr)
  (let ((last (watched-list-iterator-last itr))
	(restcur (mcdr (watched-list-iterator-current itr)))
	(literal (watched-list-iterator-literal itr)))
    (if last ;; not the beginning of the list
	(set-mcdr! last restcur)
	;; at the beginning of the list. Change the root.
	(set-literal-watched! literal restcur))
    (and (not (empty? restcur))
	 (watched-list-iterator literal last restcur))))

(define (watched-iterate-clause itr)
  (mcar (watched-list-iterator-current itr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for manipulating clauses for 2-watched literal heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (clause-other-watched clause literal)
  (cond [(literal-eq? literal (clause-watched1 clause)) (clause-watched2 clause)]
        [(literal-eq? literal (clause-watched2 clause)) (clause-watched1 clause)]
        [else (error 'clause-other-watched "[Interal error] That's not being watched at all.")]))

(define (clause-watched-swap! clause cur-watched new-watched)
  (cond [(literal-eq? cur-watched (clause-watched1 clause))
         (set-clause-watched1! clause new-watched)]
        [(literal-eq? cur-watched (clause-watched2 clause))
         (set-clause-watched2! clause new-watched)]
	[else (error 'clause-watched-swap! "[Internal error] That's not being watched at all.")]))

(define (clause-watches-literal? clause literal)
  (or (literal-eq? literal (clause-watched1 clause))
      (literal-eq? literal (clause-watched2 clause))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for manipulating clauses for clause forgetting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (SMT-forget-threshold smt)
  (SAT-Stats-forget-threshold (SMT-statistics smt)))
(define (SMT-restart-threshold smt)
  (SAT-Stats-restart-threshold (SMT-statistics smt)))
(define (SMT-conflicts-since-last-restart smt)
  (SAT-Stats-conflicts-since-last-restart (SMT-statistics smt)))

(define (SMT-bump-forget-threshold smt)
  (SMT-set-statistics smt 
		      (set-forget-threshold (SMT-statistics smt)
					    (* (SAT-Stats-forget-threshold 
						(SMT-statistics smt))
					       FORGET_THRESHOLD_COEFFICIENT))))
(define (SMT-bump-restart-threshold smt)
  (SMT-set-statistics smt 
		      (set-restart-threshold (SMT-statistics smt)
					    (* (SAT-Stats-restart-threshold 
						(SMT-statistics smt))
					       RESTART_COEFFICIENT))))
(define (SMT-set-conflicts-since-last-restart smt val)
  (SMT-set-statistics smt 
		      (set-conflicts-since-last-restart
		       (SMT-statistics smt)
		       val)))

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
