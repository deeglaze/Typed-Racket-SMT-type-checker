#lang racket

(require "../../smt-solve.rkt" #;(planet "smt-solve.rkt" ("ianj" "smt-solver.plt" 1 3))
         "../../dimacs.rkt" #;(planet "dimacs.rkt" ("ianj" "smt-solver.plt" 1 3))
         "../../smt-interface.rkt" #;(planet "smt-interface.rkt"  ("ianj" "smt-solver.plt" 1 3))
         "preprocess.rkt"
         "data-structures.rkt"
         "mergeprop.rkt"
         "proof-forest.rkt")

(define-syntax-rule (implies e e′) (if e e′ #t))

;; Bump the satisfaction timestamp and update the appropriate mappings
(define (qfeuf-satisfy t-state literal)
  (let ([maybe-eq (dict-ref (EUF-state-equalities t-state) literal #f)])
    (if maybe-eq ;; interpreted literal
        (set-literal t-state maybe-eq literal)
        (set-EUF-state-satisfaction-level t-state
                                          (add1 (EUF-state-satisfaction-level t-state))))))

;; update different mappings.
(define (set-literal t-state equality literal)
  (let* ([sat-level (add1 (EUF-state-satisfaction-level t-state))]
         [t-state (EUF-state (EUF-state-equalities t-state)
                             sat-level
                             (EUF-state-last-consistency-check t-state)
                             (EUF-state-tmp-tv t-state)
                             (if (negative? literal) ;; last-sat only useful if negative
                                  equality
                                  (EUF-state-last-sat t-state))
                             ;; backtracking hashes must have a new age created.
                             (bthash-set (bthash-new-age (EUF-state-eqlit t-state) sat-level)
                                         equality
                                         literal)
                             (bthash-set (bthash-new-age (EUF-state-backjump-table t-state) sat-level)
                                         sat-level
                                         (dimacs-lit->dimacs-var literal))
                             (bthash-new-age (EUF-state-representative t-state) sat-level)
                             (bthash-new-age (EUF-state-classes t-state) sat-level)
                             (bthash-new-age (EUF-state-uses t-state) sat-level)
                             (bthash-new-age (EUF-state-lookup t-state) sat-level)
                             (bthash-new-age (EUF-state-proof t-state) sat-level))])
    (if (positive? literal)
        (merge t-state equality)
        ;; Not changing anything here is correct, since disequalities can
        ;; only be refuted, not proved. Thus, we rely on a consistency check to
        ;; tell us that this was right or wrong.
        t-state)))

(define (qfeuf-propagate t-state strength literal)
  ;; the equality has already been merged, so just add unset equalities
  (values t-state
          (let loop ([unassigned-eq (unassigned-eqs t-state)])
            (if (empty? unassigned-eq)
                '()
                (if (equality-holds? t-state (car unassigned-eq))
                    (cons (dict-ref (EUF-state-equalities t-state) (car unassigned-eq))
                          (loop (cdr unassigned-eq)))
                    (loop (cdr unassigned-eq)))))))

(define (unassigned-eqs t-state)
  (let ([edict (EUF-state-equalities t-state)]
        [ldict (EUF-state-eqlit t-state)])
    (let loop ([itr (dict-iterate-first edict)])
      (if itr
          ;; collect only unmapped equalities
          (if (dict-ref ldict (dict-iterate-value edict itr) #f)
              (loop (dict-iterate-next edict itr))
              (cons (dict-iterate-value edict itr)
                    (loop (dict-iterate-next edict itr))))
          '()))))

;; This is not part of the typical DPLL(T) model, since it will
;; report equalities not textually represented in the problem.
;; Because of this, we have to know the representation of equalities
;; when querying the theory solver.
(define (qfeuf-known-equalities-since t-state sat-level)
  '()) ;; TODO

(define (qfeuf-explain t-state strength literal)
  (let ([equality (dict-ref (EUF-state-equalities t-state)
                            (dimacs-lit->dimacs-var literal) #f)])
    (if equality
        (explain-complexEQ t-state equality)
        (error "EUF-solver: Asked to explain an uninterpreted literal ~a" literal))))

;; Disregard strength and do a full consistency check
(define (qfeuf-consistent? t-state strength)
  (if (zero? strength) ;; lightweight check
      (quick-consistent? t-state)
      (let ([result (let/ec explain
                            (equalities-consistent-since? t-state
                                                          (EUF-state-last-consistency-check t-state)
                                                          explain))])
        (values (set-EUF-state-last-consistency-check t-state (EUF-state-satisfaction-level t-state))
                result))))

(define (quick-consistent? t-state)
  (let ([last-sat (EUF-state-last-sat t-state)])
    (values t-state
            (implies last-sat
                     (bad-disequality? t-state last-sat (λ (x) x))))))

(define (equalities-consistent-since? t-state sat-level explain)
  (let ([bjt (EUF-state-backjump-table t-state)])
    (let loop ([itr (bthash-iterate-first bjt)])
      (implies itr
               (and (implies (> (bthash-iterate-key bjt itr) sat-level) ;; only check what's new
                             (let* ([eq (dict-ref (EUF-state-equalities t-state) (bthash-iterate-value bjt itr))]
                                    [lit (dict-ref (EUF-state-eqlit t-state) eq)])
                               ;; an equality that doesn't hold IS CONSISTENT!
                               ;; We can create a model in which the equality does hold.
                               ;; Only a disequality that doesn't hold is inconsistent.
                               (implies (negative? lit)
                                        (bad-disequality? t-state eq explain))))
                    ;; don't know that hash iteration is ordered by key.
                    (loop (bthash-iterate-next bjt itr)))))))

(define (bad-disequality? t-state equality explain)
  (implies (equality-holds? t-state equality)
           ;; inconsistent => give explanation
           (explain (cons (- (dict-ref (EUF-state-eqlit t-state) equality))
                          (map - (explain-complexEQ t-state equality))))))
           
(define (qfeuf-backjump t-state backjump-by-sats)
  (let ([new-satisfaction-level (- (EUF-state-satisfaction-level t-state) backjump-by-sats)])
    (EUF-state (EUF-state-equalities t-state) ;; only thing unchanged.
               new-satisfaction-level
               (min new-satisfaction-level (EUF-state-last-consistency-check t-state))
               (bthash-backtrack-to (EUF-state-eqlit t-state) new-satisfaction-level)
               (bthash-backtrack-to (EUF-state-backjump-table t-state) new-satisfaction-level)
               (bthash-backtrack-to (EUF-state-representative t-state) new-satisfaction-level)
               (bthash-backtrack-to (EUF-state-classes t-state) new-satisfaction-level)
               (bthash-backtrack-to (EUF-state-uses t-state) new-satisfaction-level)
               (bthash-backtrack-to (EUF-state-lookup t-state) new-satisfaction-level)
               (bthash-backtrack-to (EUF-state-proof t-state) new-satisfaction-level))))

;; A complete backjump to 0. Generally more efficient than a backjump call.
(define (qfeuf-restart t-state)
  (EUF-state (EUF-state-equalities t-state)
             0 ;; satisfaction-level
             0 ;; last-consistency-check
             (EUF-state-tmp-tv t-state)
             #f ;; last-sat
             '() ;; eqlit
             '() ;; bjt
             '() ;; reps
             '() ;; classes
             '() ;; uses
             '() ;; lookup
             '() ;; proof
             ))

(define (euf-solve φ)
  (parameterize ([T-Satisfy qfeuf-satisfy]
                 [T-Propagate qfeuf-propagate]
                 [T-Backjump qfeuf-backjump]
                 [T-Restart qfeuf-restart]
                 [T-Explain qfeuf-explain]
                 [T-Consistent? qfeuf-consistent?])
    (let-values ([(CNF t-state) (EUF→CNF φ)])
      (printf "CNF ~a~%" CNF)
      (smt-assign CNF t-state +inf.0))))

(euf-solve '((declare-fun a0 0)
             (declare-fun a1 0)
             (declare-fun f 1)
             (formula (not (implies (and (= (f a0) a0)
                                         (= (f a1) a1)
                                         (= a1 a0))
                                    (= (f a0) (f a1)))))))
