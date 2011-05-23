#lang racket

(require (planet "smt-solve.rkt" ("ianj" "smt-solver.plt" 1 3))
         (planet "dimacs.rkt"  ("ianj" "smt-solver.plt" 1 3))
         (planet "smt-interface.rkt"  ("ianj" "smt-solver.plt" 1 3))
         "mergeprop.rkt"
         "proof-forest.rkt")

;; Bump the satisfaction timestamp and update the appropriate mappings
(define (qfeuf-satisfy t-state literal)
  (seq/EUF-state t-state
                 (set-EUF-state-satisfaction-level
                  t-state
                  (add1 (EUF-state-satisfaction-level t-state)))
                 (let ([maybe-eq (dict-ref (EUF-state-equalities t-state) literal #f)])
                   (if maybe-eq ;; interpreted literal
                       (set-literal t-state maybe-eq literal)
                       t-state))))

;; update different mappings.
(define (set-literal t-state equality literal)
  (seq/EUF-state t-state
                 (set-EUF-state-eqlit t-state
                                      (dict-set (EUF-state-eqlit t-state)
                                                equality
                                                literal))
                 ;; backtracking hashes must have a new age created.
                 (set-EUF-state-representative t-state (bthash-new-age (EUF-state-representative t-state)
                                                                       (EUF-state-satisfaction-level t-state)))
                 (set-EUF-state-classes t-state (bthash-new-age (EUF-state-classes t-state)
                                                                (EUF-state-satisfaction-level t-state)))
                 (set-EUF-state-uses t-state (bthash-new-age (EUF-state-uses t-state)
                                                             (EUF-state-satisfaction-level t-state)))
                 (set-EUF-state-lookup t-state (bthash-new-age (EUF-state-lookup t-state)
                                                               (EUF-state-satisfaction-level t-state)))
                 (set-EUF-state-proof t-state (bthash-new-age (EUF-state-proof t-state)
                                                              (EUF-state-satisfaction-level t-state)))))

(define (qfeuf-propagate t-state strength literal)
  ...)

(define (qfeuf-explain t-state strength literal)
  (let ([equality (dict-ref (EUF-state-equality t-state)
                            (dimacs-lit->dimacs-var literal) #f)])
    (if equality
        (values t-state ...)
        (values t-state '()))))

(define (qfeuf-consistent? t-state strength)
  (let/ec explain
          (equalities-consistent-since? t-state (EUF-state-last-consistency-check t-state) explain)))

(define (equalities-consistent-since? t-state sat-level explain)
  (let ([bjt (EUF-state-backjump-table t-state)])
    (let loop ([itr (hash-iterate-first bjt)])
      (if (and itr
               (> (hash-iterate-key bjt itr) sat-level)) ;; only check what's new
          (and (andmap (λ (dimacsvar)
                          (let* ([eq (dict-ref (EUF-state-equalities t-state) dimacsvar)]
                                 [lit (dict-ref (EUF-state-eqlit t-state) eq)])
                            (or (equal? (equality-holds? t-state eq) (positive? lit))
                                (explain ...))) ;; TODO
                       (hash-iterate-value bjt itr))
               (loop (hash-iterate-next bjt itr)))
          #t))))

(define (qfeuf-backjump t-state backjump-by-sats)
  ...)

(define (qfeuf-restart t-state)
  ...)