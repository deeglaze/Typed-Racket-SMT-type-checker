#lang racket
(require "data-structures.rkt")
(require "learned-clauses.rkt")
(require "sat-heuristics.rkt")
(require "smt-interface.rkt")
(require "debug.rkt")
(require rackunit)

(provide propagate-assignment
	 resolve-conflict!
	 initial-bcp)

;bcp-clause : Clause -> SMT
(define (bcp-clause smt clause)
  (if (and (literal-eq? (clause-watched1 clause) (clause-watched2 clause))
           (literal-unassigned? (clause-watched1 clause)))
      (begin ;(debug "bcp-clause found something" (clause-watched1 clause))
	     (propagate-assignment smt (clause-watched1 clause) clause))
      smt))

; initial-bcp : SMT -> SMT
; Make sure we learn assignments from length 1 clauses in the beginning.
(define (initial-bcp smt)
  (let ((clauses (SMT-clauses smt)))
    (let recur ((smt smt)
		(idx 0))
    (if (= idx (vector-length clauses))
	smt
	(recur (bcp-clause smt (vector-ref clauses idx)) 
	       (+ 1 idx))))))

; learned-bcp : SMT * learned-clause -> SMT
; We've just learned something; do BCP on the new clause.
; By construction, we know our learned clause is unit after backjumping.
; Furthermore, we have set the first watched literal to be the unit literal.
(define (learned-bcp smt learned)
  (propagate-assignment smt (clause-watched1 
			     (learned-clause-clause learned))
			learned))

; propagate-assignment : SMT * Literal * Clause + #f -> SMT
; Assumes the given literal and does unit resolution
(define (propagate-assignment smt lit clause)
  (let ((smt (SMT-satisfy-literal! smt lit)))
    (set-literal-igraph-node! lit
			      (node (SMT-decision-level smt) clause))
    ;; (T-solver gets priority over propositional variables)
    (let ((smt (propagate-T-implications smt lit))
	  (falsify (negate-literal lit)))
      (let prop-watch ((watchlist (literal-watched falsify))
		       (smt smt)
		       (acc '())) ;; for clause forgetting. See note below
	(cond [(empty? watchlist) 
	       ;; TODO: bcp-4cases changes this list for each literal.
	       ;; figure out how to accomodate for these changes.
	       ;; The set-literal-watched! causes the tests to crash.
	       (begin ;(set-literal-watched! falsify acc) ;; for clause forgetting
		      smt)] ; done propagating. Continue.
	      [else
	       (if (clause-forgotten? (first watchlist))
		   ;; don't bother. Forgotten clause.
		   (prop-watch (rest watchlist) smt acc)
		   ;; No conflict; keep propagating.
		   (prop-watch (rest watchlist) 
			       (update-watchedness smt (first watchlist) falsify)
			       (cons (first watchlist) acc)))])))))
;; Note about clause forgetting:
;; We lazily forget clauses in the sense that once we have "forgotten" a clause,
;; we never use it in BCP. We can, however, still use it in conflict resolution,
;; if it is the case that a propagated literal has a forgotten clause as its antecedent.
;; We do not always clean up forgotten clauses either, since we do not have an
;; easy way to talk about open ended lists. Instead, we depend on the common case of
;; no conflicts - at the end of a propagation, we bang in the accumulated list of
;; clauses that were not forgotten as the new watch list.

;; Uses T-Propagate and T-Explain parameters
(define (propagate-T-implications smt lit)
  (let-values ([(t-state lits) 
                ((T-Propagate) (SMT-T-State smt) (SMT-strength smt) (literal->dimacs lit))])
    (let t-propagate ((lits lits)
                      (smt (new-T-State smt t-state)))
      (if (empty? lits) ;; done propagating
          smt
          (t-propagate 
           (cdr lits)
           (propagate-assignment 
            smt 
            ((dimacs-lit->literal (SMT-variables smt)) (car lits))
	    (lambda (smt) ;; don't calculate an explanation until you need to.
              (clause-literals 
               ((dimacs-lits->clause (SMT-variables smt))
                ((T-Explain) (SMT-T-State smt) (SMT-strength smt) (car lits)))))))))))

; Must obliterate all decided and implied literals from 
; decision level to absolute level.
; backjump! : DecisionLevel -> unit
(define (backjump! smt absolute-level learned)
  ;; now is a good time to exponentially decay activation levels
  (let ((smt (SMT-on-conflict smt))) ;; VSIDS, forget, restart
    ;; this loop destroys all assignment-related information about literals
    ;; down to (and including) absolute-level.
    (let obliterate-loop ((levels (- (SMT-decision-level smt)
				     absolute-level))
			  (pa (SMT-partial-assignment smt))
			  (total-vars-obliterated 0))
      (cond [(not (zero? levels)) ; sat unchanged. No need to thread through
	     (begin (for-each obliterate! (first pa))
		    (obliterate-loop (+ -1 levels) (rest pa) 
				     (+ (length (first pa)) 
					total-vars-obliterated)))]
	    [else
	     (let* ((smt (SMT-set-decision-level smt absolute-level))
		    ;; don't grow assigned order too much. Cut back by how many assignments
		    ;; we have obliterated.
		    (smt (SMT-set-assigned-order smt (- (SMT-assigned-order smt) total-vars-obliterated)))
		    (smt (SMT-set-partial-assignment smt pa))
		    ;; SAT-solver obliterated assignments. Tell T-solver to as well.
		    (smt (new-T-State smt ((T-Backjump) (SMT-T-State smt) total-vars-obliterated))))
	       ;; we only have one new clause that might have taught us something.
	       ;; Do a quick check to see if we can learn anything before
	       ;; going back to deciding.
	       (learned-bcp smt learned))]))))

; obliterate! : Literal -> unit
; unassign a literal
(define (obliterate! lit)
  (let ((var (literal-var lit)))
    (begin (set-var-value!       var 'unassigned)
           (set-var-igraph-node! var #f)
           (set-var-timestamp!   var #f))))

; Is this clause now a unit clause? 
; update-watchedness : SMT * Clause * Literal -> (values SMT Maybe<Asserting-Level>)
(define (update-watchedness smt clause decided-literal)
  (debug "updated-clause" clause)
  (debug "decided-literal" decided-literal)
  (let ((caseval (bcp-4cases (some-clause->clause clause) decided-literal)))
    (match caseval
     ['skip smt] ;; clause satisfied or unknown. Continue.
     ;; propagate-assignment will do our backjumping. Return the asserting level
     ['contradiction 
      (if (= 0 (SMT-decision-level smt)) ; don't need to do resolutions.
          (raise (unsat-exn smt))
          (resolve-conflict! smt clause))]
     [unit-literal  ;; found an implied literal. Immediately propagate.
      (propagate-assignment smt unit-literal clause)])))

; returns the literal assigned most recently in the given vector of literals
(define (choose-latest-literal literals)
  (let find-recent ((idx 1)
                    (candidate (vector-ref literals 0)))
    (if (= idx (vector-length literals))
        candidate
        (let* ((nthlit (vector-ref literals idx)))              
          (if (and ;(literal-implied? nthlit)
                   ((literal-timestamp nthlit) . > . (literal-timestamp candidate)))
              (find-recent (+ 1 idx) nthlit)
              (find-recent (+ 1 idx) candidate))))))

; Must resolve backwards along implied literals using their antecedents.
; Learn the asserting clause and return the asserting level in order
; to backjump.
; resolve-conflict! : SMT * Clause * Literal -> ⊥
(define (resolve-conflict! smt C)
  (let ((clause-lits (lemma->lits smt C)))
    (let ((literals-to-learn
           (let first-uip ((resolvent clause-lits))
             (cond [(asserting-literals? smt resolvent) 
                    resolvent]
                   [else ;; to get the First UIP, we must resolve against the most
                    ;; recently assigned literal's antecedent.
                    (let* ((resolve-lit (choose-latest-literal resolvent))
			   ;; literal-explanation also increases scores for VSIDS
                           (resolve-against (literal-explanation smt resolve-lit)))
                      (first-uip (resolve-on-lit resolvent resolve-against resolve-lit)))]))))
      (let* ((level-to-backjump-to (asserting-level smt literals-to-learn))
             (watch1 ;; 1st watched lit should always be unit when we backjump
              (choose-latest-literal literals-to-learn))
             (watch2 (if (literal-eq? (vector-ref literals-to-learn 0) watch1)
                         (vector-ref literals-to-learn (+ -1 (vector-length literals-to-learn)))
                         (vector-ref literals-to-learn 0)))
             (learned (clause literals-to-learn watch1 watch2)))
        (begin (add-literal-watched! learned watch1)
               (add-literal-watched! learned watch2)
               (let-values  ([(smt learned-clause) (SMT-learn-clause smt learned)])
                 (if (0 . > . level-to-backjump-to)
                     (raise (unsat-exn smt)) ; We can imply #f without assumptions => UNSAT
                     (raise (bail-exn (backjump! smt level-to-backjump-to learned-clause))))))))))

; asserting-clause? : Vector Literal -> Boolean
; Does this clause have only one node at the current decision level?
(define (asserting-literals? smt lits)
  (not 
   (let not-asserting? ((idx 0)
                        (found-one? #f))
     (and (not (= idx (vector-length lits))) ; Asserting since at most one lit at dec-lev
          (let* ((nthlit (vector-ref lits idx))
		 (dec-eq? (= (SMT-decision-level smt)
                             (literal-dec-lev nthlit))))
            (or (and found-one? dec-eq?) ; 2 lits at current dec-lev
                (not-asserting? (+ 1 idx)
                                ;; introduce #t if nthlit at current dec-lev
                                (or dec-eq? found-one?))))))))

; asserting-level: Vector Literal -> Nat
; To find the minimum decision level in the clause
; Assumption: All literals have a node/valuation
; According to the paper "Complete Algorithms," in the case that all
; literals are at the same decision level, its relative asserting level is
; -1, which means (+ -1 dec-lev)
(define (asserting-level smt lits)
  (let recur ([idx 0] [candidate -1] [all-same-level? #t])
    (if (= idx (vector-length lits))
        (if all-same-level?
            (+ -1 (literal-dec-lev (vector-ref lits 0)))
            candidate)
        (let* ((this-declev (literal-dec-lev (vector-ref lits idx)))
               (same-level-as-last? (or (0 . > . candidate)
					(= this-declev candidate)))
               (all-same-level?* (and all-same-level?
                                      same-level-as-last?)))
          (if (and (this-declev . > . candidate)
                   (not (= this-declev (SMT-decision-level smt))))
              (recur (+ 1 idx) this-declev all-same-level?*)
              (recur (+ 1 idx) candidate all-same-level?*))))))

;; XXX: Changed to remove* to fix bug in first-uip when there is a duplicate literal
(define (resolve-on-lit C D res-lit)
  (list->vector (list-union (remove* (list (negate-literal res-lit)) (remove* (list res-lit) (vector->list C)))
                            (remove* (list (negate-literal res-lit)) (remove* (list res-lit) (vector->list D)))
                            literal-eq?)))

;; returns 'contradiction if no nonfalse literal
;; if only one nonfalse literal and it's unassigned, returns nonfalse-literal
;; if nonfalse and true, then 'skip
;; if many, updates watched pointer and returns 'skip
(define (bcp-4cases clause p [nonfalse-literal #f] [multiple #f] [idx 0])
  (cond [(= idx (clause-size clause))
         (if multiple ;; must be case 1. Mutate.
             (begin (rem-literal-watched! clause p)
                    (add-literal-watched! clause nonfalse-literal) ;; variable's watch list
                    (clause-watched-swap! clause p nonfalse-literal)
                    'skip) ;; moved pointer. Done.
             (if nonfalse-literal
                 (if (literal-unassigned? nonfalse-literal)
                     nonfalse-literal ;; UNIT (Case 2)
                     'skip) ;; True. Do nothing. (Case 3)
                 'contradiction))] ;; Contradiction (Case 4)
        [else 
         (let* ((literal (nth-literal clause idx))
                (litval (literal-valuation literal)))
           (if (or (literal-eq? literal p) ;; only want OTHER literals
                   (false? litval))        ;; false is uninteresting
               ;; keep iterating. Change nothing.
               (bcp-4cases clause p nonfalse-literal multiple (+ 1 idx))
               ;; only want to pass along the nonfalse-literal in the multiple case IF it is NOT watched.
               (if (and (literal-eq? (clause-other-watched clause p)
                                     literal) ;; current literal is the other watched literal
                        nonfalse-literal)     ;; there is another nonfalse literal (we are in case 1)
                   (bcp-4cases clause p nonfalse-literal #t (+ 1 idx))
                   ;; We are NOT the other watched literal or
                   ;; there is NOT another watched literal.
                   (bcp-4cases clause p literal nonfalse-literal (+ 1 idx)))))]))

(define (memberf a B [proc equal?])
  (and (not (empty? B))
       (or (proc a (car B))
           (memberf a (cdr B) proc))))

(define (list-union A B [proc equal?])
  (cond [(empty? A) B]
        [(memberf (first A) B proc)
         (list-union (rest A) B proc)]
        [else (cons (first A)
                    (list-union (rest A) B proc))]))

;; unit (case 3)
(check equal?
       (let ((smt (initialize (list 5 ; A B C D E
                                    5 ; -A B ^ -A C ^ -B D ^ -C -D ^ A -C E
                                    '((-1 2)
                                      (-1 3)
                                      (-2 4)
                                      (-3 -4)
                                      (1 -3 5)))
                              #f
                              0)))
         (equal? (bcp-4cases (vector-ref (SMT-clauses smt) 0) ;clause
			     (literal (vector-ref (SMT-variables smt) 0)
				      #f))
		 (vector-ref (clause-literals (vector-ref (SMT-clauses smt) 0)) 1)));p
       #t)

;; update (case 1)
(check equal?
       (let ((smt (initialize (list 5 ; A B C D E
				    5 ; -A B ^ -A C ^ -B D ^ -C -D ^ A -C E
				    '((-1 2)
				      (-1 3)
				      (-2 4)
				      (-3 -4)
				      (1 -3 5)))
                              #f
                              0)))
	 (bcp-4cases (vector-ref (SMT-clauses smt) 4) ;clause
		     (literal (vector-ref (SMT-variables smt) 0)
			      #t)));p
	 'skip)