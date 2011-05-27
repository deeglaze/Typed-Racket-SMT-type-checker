#lang racket
(require (only-in "dimacs.rkt"
		  dimacs-lit->literal
		  dimacs-lits->clause)
	 "data-structures.rkt"
	 "learned-clauses.rkt"
	 "statistics.rkt"
	 "sat-heuristics.rkt"
	 "smt-interface.rkt"
	 "debug.rkt"
	 rackunit)

(provide propagate-assignment
         resolve-or-continue)

; learned-bcp : SMT * learned-clause -> SMT
; We've just learned something; do BCP on the new clause.
; By construction, we know our learned clause is unit after backjumping.
; Furthermore, we have set the first watched literal to be the unit literal.
(define (learned-bcp smt learned)
  (propagate-assignment smt (clause-watched1
			     (learned-clause-clause learned))
			learned))

(define (resolve-or-continue smt t-state explanation)
  (define (vars->clause-of-not-and vars)
    (let* ([negate-assigned
            (map (lambda (v)
                   (literal v (not (var-value v))))
		 vars)]
           [clause-list (list->vector negate-assigned)])
      (clause clause-list
              (vector-ref clause-list 0)
              (vector-ref clause-list (sub1 (vector-length clause-list))))))
  (define (not-partial-assignment smt)
    (vars->clause-of-not-and (filter-not var-unassigned?
                                         (vector->list (SMT-variables smt)))))
  (cond [(eqv? explanation #t)
         (set-SMT-T-State smt t-state)]
        [(not explanation)
         ;; no explanation, but bad
         (resolve-conflict smt (not-partial-assignment smt))]
        [else
         ;; explanation and bad
         (resolve-conflict smt
                           ((dimacs-lits->clause (SMT-variables smt))
                            explanation))]))

; propagate-assignment : SMT * Literal * Clause + #f + (SMT-> T-State * Clause) -> SMT
; Assumes the given literal and does unit resolution
(define (propagate-assignment smt lit clause)
  (let*-values ([(smt) (SMT-satisfy-literal smt lit clause)] ;; tell T-Solver lit is satisfied
                ;; Is this small change blatantly wrong? (Don't try hard)
                [(t-state res) ((T-Consistent?) (SMT-T-State smt) 0)]
                ;; If so, resolve, otherwise continue.
                [(smt) (resolve-or-continue smt t-state res)]
                ;; Continued, so get theory implications
                [(smt) (propagate-T-implications smt lit)]
                ;; All clauses watching the negation should be updated (BCP)
                [(falsify) (negate-literal lit)])
    ;; this iterator is stateful to crawl the mconses.
    (propagate-clauses-watching smt (watched-iterate-first falsify) falsify)))

(define (propagate-clauses-watching smt itr literal)
  (if itr
      (let ([watching-clause (watched-iterate-clause itr)])
        ;; we lazily collect forgotten clauses.
        (if (clause-forgotten? smt watching-clause)
            (propagate-clauses-watching smt (watched-iterate-remove itr) literal)
            ;; No conflict; keep propagating.
            (let-values ([(smt remove?)
                          (update-watchedness smt watching-clause literal)])
              (if remove?
                  (propagate-clauses-watching smt (watched-iterate-remove itr) literal)
                  (propagate-clauses-watching smt (watched-iterate-next itr) literal)))))
      smt))

;; Note about clause forgetting:
;; We lazily forget clauses in the sense that once we have "forgotten" a clause,
;; we never use it in BCP. We can, however, still use it in conflict resolution,
;; if it is the case that a propagated literal has a forgotten clause as its antecedent.
;;
;; The new behavior of bcp-4cases:
;; It used to be that when we moved which literal was being watched in a clause,
;; we would immediately remove the fact that the original literal was being watched
;; in that clause. Now that we bang in a new watched list, we have to be careful to
;; remove these references.

;; Uses T-Propagate and T-Explain parameters
(define (propagate-T-implications smt lit)
  (let-values ([(t-state lits)
                ((T-Propagate) (SMT-T-State smt) (SMT-strength smt) lit)])
    (for/let [smt (set-SMT-T-State smt t-state)]
             ([lit lits])
      (propagate-assignment smt
                            lit
                            ;; Don't calculate an explanation until you need to.
                            ;; We might have more theory state then, making it easier.
                            (T-Explanation-fn t-state lit)
                            lit))))

(define ((T-Explanation-fn t-state dimacslit) smt)
  ((T-Explain) (SMT-T-State smt) (SMT-strength smt) dimacslit))

(define (satisfy-literal sat literal dec-lev antecedent)
  (let ([var (literal-var (SAT-variables sat) literal)])
    (seq/let sat
             (set-SAT-variables sat
                                (bthash-set (SAT-variables sat)
                                            (dimacs-lit->dimacs-var literal)
                                            (var (var-heuristic var)
                                                 ;; timestamp for first UIP
                                                 (SAT-Stats-assigned-order (SAT-statistics sat))
                                                 dec-lev
                                                 antecedent
                                                 (literal-polarity literal))))
             (SAT-inc-assigned-order sat)
             ;; for faster unsetting in backjumps
             (set-SAT-sats-per-dec-lev sat (cons (add1 (car (SAT-sats-per-dec-lev sat)))
                                                 (cdr (SAT-sats-per-dec-lev sat)))))))

(define (SMT-satisfy-literal smt literal antecedent)
  (SMT (satisfy-literal (SMT-sat smt) literal (SMT-decision-level smt) antecedent)
       ;; Tell the T-Solver a literal has been satisfied
       ((T-Satisfy) (SMT-T-State smt) (literal->dimacs literal))
       (SMT-strength smt)
       (SMT-seed smt)))

; Must obliterate all decided and implied literals from
; decision level to absolute level.
; backjump : SMT * DecisionLevel * Clause -> unit
(define (backjump smt absolute-level learned)
  ;; now is a good time to exponentially decay activation levels
  (let*-values ([(smt) (SMT-on-conflict smt)] ;; VSIDS, forget, restart
                [(dropped remaining) (split-at (SMT-sats-per-dec-lev smt)
                                               (- (SMT-decision-level smt)
                                                  absolute-level))]
                [(total-vars-obliterated) (foldr + 0 dropped)])
    (seq/let smt
             ;; update bookkeeping for the changed decision level
             (set-SMT-decision-level smt absolute-level)
             ;; this undoes all assignment-related information about literals
             ;; down to (and including) absolute-level.
             (set-SMT-variables smt (bthash-backtrack-to (SMT-variables smt) absolute-level))
             ;; don't grow assigned order too much. Cut back by how many assignments
             ;; we have obliterated.
             (set-SMT-assigned-order smt (- (SMT-assigned-order smt) total-vars-obliterated))
             ;; obliterate gave us a new partial assignment
             (set-SMT-sats-per-dec-lev smt remaining)
             ;; SAT-solver obliterated assignments. Tell T-solver to as well.
             (set-SMT-T-State smt ((T-Backjump) (SMT-T-State smt) total-vars-obliterated))
             ;; we only have one new clause that might have taught us something.
             ;; Do a quick check to see if we can learn anything before
             ;; going back to deciding.
             (learned-bcp smt learned))))

; Is this clause now a unit clause?
; update-watchedness : SMT * Clause * Literal -> (values SMT Maybe<Asserting-Level>)
(define (update-watchedness smt clause decided-literal)
  ;; clause may be learned, so unpackage clause and do the 4 cases
  (match (bcp-4cases (some-clause->clause clause) decided-literal)
    ['skip (values smt #f)] ;; clause satisfied. Continue.
    ['remove (values smt #t)]
    ;; propagate-assignment will do our backjumping. Return the asserting level
    ['contradiction
     (if (zero? (SMT-decision-level smt)) ; don't need to do resolutions.
         (raise (unsat-exn smt))
         (resolve-conflict smt clause))]
    [unit-literal  ;; found an implied literal. Immediately propagate.
     (values (propagate-assignment smt unit-literal clause) #f)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for conflict resolution / clause learning
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; XXX: Changed to remove* to fix bug in first-uip when there is a duplicate literal
(define (resolve-on-lit C D res-lit)
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
  (list->vector (list-union (remove* (list (negate-literal res-lit) res-lit) (vector->list C))
			    (remove* (list (negate-literal res-lit) res-lit) (vector->list D))
			    literal-eq?)))

(define (first-UIP smt resolvent)
  (cond [(asserting-literals? smt resolvent)
         (values smt resolvent)]
        [else ;; to get the First UIP, we must resolve against the most
         ;; recently assigned literal's antecedent.
         (let*-values ([(resolve-lit) (choose-latest-literal resolvent)]
                       ;; literal-explanation also increases scores for VSIDS
                       [(smt resolve-against) (literal-explanation smt resolve-lit)])
           (first-UIP smt (resolve-on-lit resolvent resolve-against resolve-lit)))]))

; Must resolve backwards along implied literals using their antecedents.
; Learn the asserting clause and return the asserting level in order
; to backjump.
; resolve-conflict : SMT * Clause * Literal -> ⊥
(define (resolve-conflict smt C)
  (let*-values ([(smt literals-to-learn)
                 (call-with-values (λ () (lemma->lits smt C)) first-UIP)]
                [(level-to-backjump-to) (asserting-level smt literals-to-learn)]
                [(watch1) ;; 1st watched lit should always be unit when we backjump
                 (choose-latest-literal literals-to-learn)]
                ;; latest may be 0. If so, choose the opposite end.
                ;; otherwise, choose 0.
                ;; XXX: There may be research for smarter ways to watch literals.
                ;;      this choice is easy to implement.
                [(watch2) (if (literal-eq? (vector-ref literals-to-learn 0) watch1)
                              (vector-ref literals-to-learn (sub1 (vector-length literals-to-learn)))
                              (vector-ref literals-to-learn 0))]
                ;; Create the lemma clause.
                [(smt learned-clause) (SMT-learn-clause smt literals-to-learn watch1 watch2)])
        (if (0 . > . level-to-backjump-to)
            (raise (unsat-exn smt)) ; We can imply #f without assumptions => UNSAT
            (raise (bail-exn (backjump smt level-to-backjump-to learned-clause))))))

; asserting-clause? : Vector Literal -> Boolean
; Does this clause have only one node at the current decision level?
(define (asserting-literals? smt lits)
  (not
   (let not-asserting? ([idx 0]
                        [found-one? #f])
     (and (not (= idx (vector-length lits))) ; Asserting since at most one lit at dec-lev
          (let* ([nthlit (vector-ref lits idx)]
		 [dec-eq? (= (SMT-decision-level smt)
                             (literal-dec-lev nthlit))])
            (or (and found-one? dec-eq?) ; 2 lits at current dec-lev
                (not-asserting? (add1 idx)
                                ;; introduce #t if nthlit at current dec-lev
                                (or dec-eq? found-one?))))))))

; asserting-level: Vector Literal -> Nat
; To find the minimum decision level in the clause
; Assumption: All literals have a node/valuation
; According to the paper "Complete Algorithms," in the case that all
; literals are at the same decision level, its relative asserting level is
; -1, which means (+ -1 dec-lev)
(define (asserting-level smt lits)
  (let recur ([idx 0]
              [candidate -1]
              [all-same-level? #t])
    (if (= idx (vector-length lits))
        (if all-same-level?
            (sub1 (literal-dec-lev (vector-ref lits 0)))
            candidate)
        (let* ([this-declev (literal-dec-lev (vector-ref lits idx))]
               [same-level-as-last? (or (0 . > . candidate)
					(= this-declev candidate))]
               [all-same-level?* (and all-same-level?
                                      same-level-as-last?)])
          (if (and (this-declev . > . candidate)
                   (not (= this-declev (SMT-decision-level smt))))
              (recur (add1 idx) this-declev all-same-level?*)
              (recur (add1 idx) candidate all-same-level?*))))))

;; returns 'contradiction if no nonfalse literal
;; if only one nonfalse literal and it's unassigned, returns nonfalse-literal
;; if nonfalse and true, then 'skip
;; if many, updates watched pointer and returns 'remove for the list to be updated
(define (bcp-4cases clause p [nonfalse-literal #f] [multiple #f] [idx 0])
  (cond [(= idx (clause-size clause))
         (if multiple ;; must be case 1. Mutate.
             (begin (add-literal-watched! clause nonfalse-literal) ;; variable's watch list
                    (clause-watched-swap! clause p nonfalse-literal)
                    'remove) ;; moved pointer. Done.
             (if nonfalse-literal
                 (if (literal-unassigned? nonfalse-literal)
                     nonfalse-literal ;; UNIT (Case 2)
                     'skip) ;; True. Do nothing. (Case 3)
                 'contradiction))] ;; Contradiction (Case 4)
        [else
         (let* ([literal (nth-literal clause idx)]
                [litval (literal-valuation literal)])
           (if (or (literal-eq? literal p) ;; only want OTHER literals
                   (false? litval))        ;; false is uninteresting
               ;; keep iterating. Change nothing.
               (bcp-4cases clause p nonfalse-literal multiple (add1 idx))
               ;; only want to pass along the nonfalse-literal in the multiple case IF it is NOT watched.
               (if (and (literal-eq? (clause-other-watched clause p)
                                     literal) ;; current literal is the other watched literal
                        nonfalse-literal)     ;; there is another nonfalse literal (we are in case 1)
                   (bcp-4cases clause p nonfalse-literal #t (add1 idx))
                   ;; We are NOT the other watched literal or
                   ;; there is NOT another watched literal.
                   (bcp-4cases clause p literal nonfalse-literal (add1 idx)))))]))
