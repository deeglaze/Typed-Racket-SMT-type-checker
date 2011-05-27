#lang racket

(require "../../smt-solve.rkt" #;(planet "smt-solve.rkt" ("ianj" "smt-solver.plt" 1 3))
         "../../dimacs.rkt" #;(planet "dimacs.rkt" ("ianj" "smt-solver.plt" 1 3))
         "../../smt-interface.rkt" #;(planet "smt-interface.rkt"  ("ianj" "smt-solver.plt" 1 3))
         "../../debug.rkt"
         "preprocess.rkt"
         "data-structures.rkt"
         "mergeprop.rkt"
         "proof-forest.rkt")

(define-syntax-rule (implies e e′) (if e e′ #t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; T-Satisfy
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bump the satisfaction timestamp and update the appropriate mappings
(define (qfeuf-satisfy t-state literal)
  (let ([maybe-eq (dict-ref (EUF-state-equalities t-state) (dimacs-lit->dimacs-var literal) #f)])
    (if maybe-eq ;; interpreted literal
        (set-literal t-state maybe-eq literal)
        (set-EUF-state-satisfaction-level t-state
                                          (add1 (EUF-state-satisfaction-level t-state))))))

;; update different mappings.
(define (set-literal t-state equality literal)
  (debug "Setting ~a~%" literal)
  (let* ([sat-level (add1 (EUF-state-satisfaction-level t-state))]
         [t-state (EUF-state (EUF-state-equalities t-state)
                             (EUF-state-untranslator t-state)
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
    (debug "Literal ~a set ~a~%" literal (aged-hash-hash (car (EUF-state-eqlit t-state))))
    (if (positive? literal)
        (merge t-state equality) ;; should be an EUF-state
        ;; Not changing anything here is correct, since disequalities can
        ;; only be refuted, not proved. Thus, we rely on a consistency check to
        ;; tell us that this was right or wrong.
        t-state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; T-Propagate
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (qfeuf-propagate t-state strength literal)
  ;; the equality has already been merged, so just add unset equalities
  (debug "Propagate: Eqv classes ~a~%" (EUF-state-classes t-state))
  (values t-state
          (let loop ([lit-eqs (unassigned-lits t-state)])
            (cond [(empty? lit-eqs) '()]
                  [(equality-holds? t-state (cdar lit-eqs))
                    (cons (caar lit-eqs)
                          (loop (cdr lit-eqs)))]
                  [else (loop (cdr lit-eqs))]))))

;;-> Listof DimacsVar
(define (unassigned-lits t-state)
  (let ([edict (EUF-state-equalities t-state)] ;; lit -> equality
        [ldict (EUF-state-eqlit t-state)]) ;; equality -> lit
    (let loop ([itr (dict-iterate-first edict)])
      (if itr
          ;; collect only unmapped equalities
          (if (bthash-ref ldict (dict-iterate-value edict itr) #f) ;; lit assigned?
              (loop (dict-iterate-next edict itr))
              (cons (cons (dict-iterate-key edict itr) ;; unassigned. Add LIT * EQ.
                          (dict-iterate-value edict itr))
                    (loop (dict-iterate-next edict itr))))
          '()))))

;; This is not part of the typical DPLL(T) model, since it will
;; report equalities not textually represented in the problem.
;; Because of this, we have to know the representation of equalities
;; when querying the theory solver.
(define (qfeuf-known-equalities-since t-state sat-level)
  (let* ([classes (EUF-state-classes t-state)]
         [old-classes (bthash-backtrack-to classes sat-level)]
         [representatives (bthash-values (EUF-state-representative t-state))])
    ;; walk the representatives and see what its class minus the previous class is.
    (let loop ([representatives representatives])
      (cond [(empty? representatives)
             '()]
            [else (let* ([rep (car representatives)]
                         [rep-class (bthash-ref (EUF-state-classes t-state) rep '())]
                         [old-rep (bthash-ref (EUF-state-representative t-state) rep rep)]
                         [old-rep-class (bthash-ref old-classes old-rep '())]
                         [new-equalities (remove* old-rep-class rep-class)])
                    (if (empty? new-equalities)
                        (loop (cdr representatives))
                        (cons (filter-map (EUF-state-untranslator t-state)
                                          (cons rep new-equalities))
                              (loop (cdr representatives)))))])))) ;; TODO

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; T-Explain
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (qfeuf-explain t-state strength literal)
  (let ([equality (dict-ref (EUF-state-equalities t-state)
                            (dimacs-lit->dimacs-var literal) #f)])
    (if equality
        (explain-complexEQ t-state equality)
        (error "EUF-solver: Asked to explain an uninterpreted literal ~a" literal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; T-Consistent?
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Disregard strength and do a full consistency check
(define (qfeuf-consistent? t-state strength)
  (unless (EUF-state? t-state)
          (error "WHAT? NOT EUF-state!!"))
  (debug "consistent? str ~a~%" strength)
  (if (zero? strength) ;; lightweight check
      (quick-consistent? t-state)
      (let-values  ([(t-state result)
                     (equalities-consistent-since? t-state
                                                   (EUF-state-last-consistency-check t-state))])
        (debug "Fully consistent? ~a~%" result)
        (values (set-EUF-state-last-consistency-check t-state (EUF-state-satisfaction-level t-state))
                result))))

(define (quick-consistent? t-state)
  (let ([last-sat (EUF-state-last-sat t-state)])
    (if last-sat
        (let*-values ([(t-state res) (bad-disequality? t-state last-sat)]
                      [(t-state) (set-EUF-state-last-sat t-state #f)])
          (if res ;; is bad
              (values t-state res)
              (values t-state #t)))
        ;; nothing to refute. Consistent.
        (values t-state #t))))

;; -> #t + DimacsClause
(define (equalities-consistent-since? t-state sat-level)
  (let ([bjt (EUF-state-backjump-table t-state)])
    (debug "Consistent-since? ~a~%" sat-level)
    (let loop ([t-state t-state]
               [itr (bthash-iterate-first bjt)])
      (if itr
          (if (> (bthash-iterate-key bjt itr) sat-level) ;; only check what's new
              (let* ([lit (bthash-iterate-value bjt itr)]
                     [eq (dict-ref (EUF-state-equalities t-state) (dimacs-lit->dimacs-var lit) (λ () (error "here2")))])
                (debug "in range" eq lit)
                ;; an equality that doesn't hold IS CONSISTENT!
                ;; We can create a model in which the equality does hold.
                ;; Only a disequality that doesn't hold is inconsistent.
                (if (negative? lit)
                    (let-values ([(t-state res) (bad-disequality? t-state eq)])
                      (debug "Back from bad-dis" res)
                      (if res ;; has an explanation
                          (values t-state res)
                          (loop t-state (bthash-iterate-next bjt itr))))
                    (loop t-state (bthash-iterate-next bjt itr))))
              ;; don't know that hash iteration is ordered by key.
              (loop t-state (bthash-iterate-next bjt itr)))
          (values t-state #t)))))

;; -> Option DimacsClause
(define (bad-disequality? t-state equality)
  (let ([eq-holds? (equality-holds? t-state equality)])
    (debug "bad-dis: " equality eq-holds?)
    (if eq-holds?
        (let-values ([(t-state res) (explain-complexEQ t-state equality)])
          (values t-state
                  (cons (- (bthash-ref (EUF-state-eqlit t-state) equality (λ () (error "here3"))))
                        (map - res))))
        ;; inconsistent => give explanation
        (values t-state #f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; T-Backjump
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (qfeuf-backjump t-state backjump-by-sats)
  (let ([new-satisfaction-level (- (EUF-state-satisfaction-level t-state) backjump-by-sats)])
    (EUF-state (EUF-state-equalities t-state) ;; only thing unchanged.
               (EUF-state-untranslator t-state)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; T-Restart
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A complete backjump to 0. Generally more efficient than a backjump call.
(define (qfeuf-restart t-state)
  (EUF-state (EUF-state-equalities t-state)
             (EUF-state-untranslator t-state)
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
             '())) ;; proof

(define (euf-solve φ)
  (parameterize ([T-Satisfy qfeuf-satisfy]
                 [T-Propagate qfeuf-propagate]
                 [T-Backjump qfeuf-backjump]
                 [T-Restart qfeuf-restart]
                 [T-Explain qfeuf-explain]
                 [T-Consistent? qfeuf-consistent?])
    (let-values ([(CNF t-state) (EUF→CNF φ)])
      (debug "CNF ~a~%" CNF)
      (filter-map (EUF-state-untranslator t-state)
                  (smt-assign CNF t-state +inf.0)))))

(euf-solve '((declare-fun a0 0)
             (declare-fun a1 0)
             (declare-fun f 1)
             (formula (not (implies (and (= (f a0) a0)
                                         (= (f a1) a1)
                                         (= a0 a1))
                                    (not (= (f a0) (f a1))))))))

(euf-solve '((formula (not (= 1 1)))))
