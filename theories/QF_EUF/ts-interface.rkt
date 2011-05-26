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
  (let ([maybe-eq (dict-ref (EUF-state-equalities t-state) (dimacs-lit->dimacs-var literal) #f)])
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
                                         literal)
                             (bthash-new-age (EUF-state-representative t-state) sat-level)
                             (bthash-new-age (EUF-state-classes t-state) sat-level)
                             (bthash-new-age (EUF-state-uses t-state) sat-level)
                             (bthash-new-age (EUF-state-lookup t-state) sat-level)
                             (bthash-new-age (EUF-state-proof t-state) sat-level))])
    (printf "Literal ~a set ~a~%" literal (aged-hash-hash (car (EUF-state-eqlit t-state))))
    (if (positive? literal)
        (merge t-state equality) ;; should be an EUF-state
        ;; Not changing anything here is correct, since disequalities can
        ;; only be refuted, not proved. Thus, we rely on a consistency check to
        ;; tell us that this was right or wrong.
        t-state)))

(define (qfeuf-propagate t-state strength literal)
  ;; the equality has already been merged, so just add unset equalities
  (values t-state
          (let loop ([unassigned-eq (unassigned-eqs t-state)])
            (cond [(empty? unassigned-eq) '()]
                  [(equality-holds? t-state (car unassigned-eq))
                    (cons (dict-ref (EUF-state-equalities t-state) (car unassigned-eq))
                          (loop (cdr unassigned-eq)))]
                  [else (loop (cdr unassigned-eq))]))))

(define (unassigned-eqs t-state)
  (let ([edict (EUF-state-equalities t-state)] ;; lit -> equality
        [ldict (EUF-state-eqlit t-state)]) ;; equality -> lit
    (let loop ([itr (dict-iterate-first edict)])
      (if itr
          ;; collect only unmapped equalities
          (if (bthash-ref ldict (dict-iterate-value edict itr) #f) ;; lit assigned?
              (loop (dict-iterate-next edict itr))
              (cons (dict-iterate-value edict itr) ;; unassigned. Add EQUALITY.
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
  (unless (EUF-state? t-state)
          (error "WHAT? NOT EUF-state!!"))
  (if (zero? strength) ;; lightweight check
      (quick-consistent? t-state)
      (let-values  ([(t-state result)
                     (equalities-consistent-since? t-state
                                                   (EUF-state-last-consistency-check t-state))])
        (printf "Fully consistent? ~a~%" result)
        (values (set-EUF-state-last-consistency-check t-state (EUF-state-satisfaction-level t-state))
                result))))

(define (quick-consistent? t-state)
  (let ([last-sat (EUF-state-last-sat t-state)])
    (if last-sat
        (let-values ([(t-state res) (bad-disequality? t-state last-sat)])
          (if res ;; is bad
              (values t-state res)
              (values t-state #t)))
        (values t-state #f))))

(define (equalities-consistent-since? t-state sat-level)
  (let ([bjt (EUF-state-backjump-table t-state)])
    (printf "Consistent-since? ~a~%" sat-level)
    (let loop ([t-state t-state]
               [itr (bthash-iterate-first bjt)])
      (if itr
          (if (> (bthash-iterate-key bjt itr) sat-level) ;; only check what's new
              (let* ([lit (bthash-iterate-value bjt itr)]
                     [eq (dict-ref (EUF-state-equalities t-state) (dimacs-lit->dimacs-var lit))])
                (printf "in range ~a = ~a~%" eq lit)
                ;; an equality that doesn't hold IS CONSISTENT!
                ;; We can create a model in which the equality does hold.
                ;; Only a disequality that doesn't hold is inconsistent.
                (if (negative? lit)
                    (let-values ([(t-state res) (bad-disequality? t-state eq)])
                      (printf "Back from bad-dis ~a~%" res)
                      (if res ;; has an explanation
                          (values t-state res)
                          (loop t-state (bthash-iterate-next bjt itr))))
                    (loop t-state (bthash-iterate-next bjt itr))))
              ;; don't know that hash iteration is ordered by key.
              (loop t-state (bthash-iterate-next bjt itr)))
          (values t-state #t)))))

(define (bad-disequality? t-state equality)
  (let ([eq-holds? (equality-holds? t-state equality)])
    (printf "bad-dis: ~a holds? ~a~%" equality eq-holds?)
    (if eq-holds?
        (let-values ([(t-state res) (explain-complexEQ t-state equality)])
          (values t-state
                  (cons (- (bthash-ref (EUF-state-eqlit t-state) equality))
                        (map - res))))
        ;; inconsistent => give explanation
        (values t-state #f))))

(define (qfeuf-backjump t-state backjump-by-sats)
  (let ([new-satisfaction-level (- (EUF-state-satisfaction-level t-state) backjump-by-sats)])
    (EUF-state (EUF-state-equalities t-state) ;; only thing unchanged.
               new-satisfaction-level
               (min new-satisfaction-level (EUF-state-last-consistency-check t-state))
               (EUF-state-tmp-tv t-state)
               #f ;; last-sat most assuredly is unset
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

(printf "~%~%Should be UNSAT~%~%")

(euf-solve '((declare-fun a 0)
             (formula (not (= a a)))))

(printf "~%~%Should be UNSAT~%~%")
(euf-solve '((declare-fun a0 0)
             (declare-fun a1 0)
             (declare-fun f 1)
             (formula (not (implies (and (= (f a0) a0)
                                         (= (f a1) a1)
                                         (= a1 a0))
                                    (= (f a0) (f a1)))))))

(printf "~%~%Should be SAT~%~%")
(euf-solve '((declare-fun a0 0)
             (declare-fun a1 0)
             (declare-fun f 1)
             (formula (not (implies (and (= (f a0) a0)
                                         (= (f a1) a1)
                                         (= a1 a0))
                                    (not (= (f a0) (f a1))))))))
