#lang racket

(require "data-structures.rkt"
         "proof-forest.rkt"
         rackunit)

(provide merge equality-holds? explain-complexEQ)

;; Less mutation, so hopefully it makes more sense than
;; the Nieuwenhuis & Oliveras paper.

(define (merge t-state s=t)
  (match s=t
    [(ConstEQ a b)
     (propagate t-state s=t)]
    [(CurriedEQ a₁ a₂ a)
     (let* ([a₁′ (get-representative t-state a₁)]
            [a₂′ (get-representative t-state a₂)]
            [res (get-lookup t-state a₁′ a₂′)])
       (if (CurriedEQ? res)
           (propagate t-state (EQpair s=t res))
           (seq/EUF-state t-state
                          (set-lookup t-state a₁′ a₂′ s=t)
                          (add-to-uses t-state a₁′ s=t)
                          (add-to-uses t-state a₂′ s=t))))]
    [other (error "merge fail ~a" other)]))

(define (propagate t-state equality)
  (let*-values ([(a b) (E→a×b equality)]
                [(a′) (get-representative t-state a)]
                [(b′) (get-representative t-state b)])
    (if (eqv? a′ b′)
        t-state
        ;; Without loss of generality, let it be that
        ;; |ClassList(a′)| ≤ |ClassList(b′)|
        (let-values ([(a a′ b b′ equality)
                      (if (<= (length (get-class t-state a′))
                              (length (get-class t-state b′)))
                          (values a a′ b b′ equality)
                          (values b b′ a a′ (flip-equality equality)))])
          (seq/EUF-state
           t-state
           (set-EUF-state-proof
            t-state
            (add-explanation (EUF-state-proof t-state) a b equality))
           (union-equalities t-state a′ b′)
           (change-uses t-state a′ b′))))))

;; lines 17-19 of the paper's pseudocode
(define (union-equalities t-state a′ b′) ;; Returns EUF-state
  (seq/EUF-state t-state
    (for/EUF-state t-state ([c (get-class t-state a′)])
      (set-representative t-state c b′)
      (add-to-class t-state b′ c))
    (set-EUF-state-classes t-state
                           (bthash-set (EUF-state-classes t-state) a′ '())))) ;; nuke a′ classes

;; lines 20-26 of the paper's pseudocode
(define (change-uses t-state a′ b′)
  (let loop ([t-state t-state]
             [auses (get-uses t-state a′)]
             [pending '()])
    (if (empty? auses)
        (seq/EUF-state t-state
                       (set-EUF-state-uses t-state (bthash-set (EUF-state-uses t-state) a′ '()))
                       (for/EUF-state t-state ([equality pending])
                         (propagate t-state equality)))
        (let* ([ceq (car auses)]
               [c₁′ (get-representative t-state (CurriedEQ-g ceq))]
               [c₂′ (get-representative t-state (CurriedEQ-arg ceq))]
               [lookup (get-lookup t-state c₁′ c₂′)])
          (if (CurriedEQ? lookup)
              (loop t-state
                    (cdr auses)
                    (cons (EQpair (CurriedEQ c₁′ c₂′ (CurriedEQ-a ceq)) lookup)
                          pending))
              (seq/EUF-state t-state
                             (set-lookup t-state c₁′ c₂′ ceq)
                             (add-to-uses t-state b′ ceq)
                             (loop t-state (cdr auses) pending)))))))

(define (explain-complexEQ t-state equality)
  (if (ConstEQ? equality)
      (values t-state
              (explain (EUF-state-eqlit t-state)
                       (EUF-state-proof t-state)
                       equality))
      (let* ([tmp-tv (EUF-state-tmp-tv t-state)] ;; need a fresh TVar
             [t-state (merge t-state (CurriedEQ (CurriedEQ-g equality)
                                                (CurriedEQ-arg equality)
                                                tmp-tv))])
        (values (set-EUF-state-tmp-tv t-state (add1 tmp-tv))
                (explain (EUF-state-eqlit t-state)
                         (EUF-state-proof t-state)
                         (ConstEQ tmp-tv (CurriedEQ-a equality)))))))

;; This function has been adapted from are-congruent? from the original paper.
;; It instead works on our internal data structures.
;; (U ConstEQ CurriedEQ) → Boolean
(define (equality-holds? t-state equality)
  (match equality
    [(ConstEQ a b)
     (eqv? (get-representative t-state a)
           (get-representative t-state b))]
    [(CurriedEQ a₁ a₂ b) ;; f(a₁,a₂) = b
     (let* ([a₁′ (get-representative t-state a₁)]
            [a₂′ (get-representative t-state a₂)]
            [lookup (get-lookup t-state a₁′ a₂′)])
       ;; If lookup fails, we know nothing about f(a₁′,a₂′), so it can't possibly be b′.
       (and (CurriedEQ? lookup)
            (eqv? (get-representative t-state (CurriedEQ-a lookup))
                  (get-representative t-state b))))]
    [other (error 'equality-holds? "fail ~a" other)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Getters/setters follow. Uninteresting.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; for handling size bias in WLOG setting.
(define (flip-equality equality)
  (match equality
    [(ConstEQ a b)
     (ConstEQ b a)]
    [(EQpair (CurriedEQ a₁ a₂ a)
             (CurriedEQ b₁ b₂ b))
     (EQpair (CurriedEQ b₁ b₂ b)
             (CurriedEQ a₁ a₂ a))]
    [other (error "flip-equality: Internal invariant violated ~a" other)]))

;; Get what the equality is standing for.
(define (E→a×b equality)
  (match equality
    [(ConstEQ a b)
     (values a b)]
    [(EQpair (CurriedEQ a₁ a₂ a)
             (CurriedEQ b₁ b₂ b))
     (values a b)]
    [other (error "E→a×b: Internal invariant violated ~a" other)]))

;; Manage the classes table
(define (get-class t-state rep)
  (bthash-ref (EUF-state-classes t-state) rep '()))

(define (add-to-class t-state rep tvar)
  (set-EUF-state-classes t-state
                         (bthash-set
                          (EUF-state-classes t-state)
                          rep
                          (cons tvar (bthash-ref
                                      (EUF-state-classes t-state)
                                      rep)))))

;; Manage the lookup table
(define (get-lookup t-state rep₁ rep₂)
  (bthash-ref (EUF-state-lookup t-state)
              (cons (min rep₁ rep₂) (max rep₁ rep₂))))

(define (set-lookup t-state rep₁ rep₂ equality)
  (set-EUF-state-lookup t-state
   (bthash-set (EUF-state-lookup t-state)
               (cons (min rep₁ rep₂) (max rep₁ rep₂))
               equality)))

;; Manage the uses table
(define (get-uses t-state representative)
  (bthash-ref (EUF-state-uses t-state) representative '()))

(define (add-to-uses t-state representative equality)
  (set-EUF-state-uses t-state
    (bthash-set (EUF-state-uses t-state)
                representative
                (cons equality
                      (bthash-ref (EUF-state-uses t-state)
                                  representative)))))

;; Manage the representative table
(define (get-representative t-state tvar)
  ;; If unset, then tvar not in another other equivalence class than its own.
  ;; In that case, return itself
  (let ([res
  (bthash-ref (EUF-state-representative t-state) tvar tvar)])
    (if res
        res
        (error "rep is false! " tvar))))

(define (set-representative t-state tvar b′)
  (set-EUF-state-representative t-state
    (bthash-set (EUF-state-representative t-state) tvar b′)))