#lang racket

;; An implementation of disjoint sets in Racket
;; This is a mutable data structure.

#;(define-struct: (A) disjoint-set ([parent : (Option (disjoint-set A))]
                                    [rank : Natural]
                                    [elem : A]) #:mutable)
(define-struct disjoint-set (parent rank elem) #:mutable)

#;(: make-set : (All (A) (A -> (disjoint-set A))))
(define (make-set x)
  (make-disjoint-set #f 0 x))

;; AKA get-root
#;(: find! : (All (A) ((disjoint-set A) -> (disjoint-set A))))
(define (find! x)
  (let ((parent (disjoint-set-parent x)))
    (if parent
        (let ((res (find! parent)))
          (set-disjoint-set-parent! x parent)
          res)
        x)))

#;(: safe-parent : (All (A) ((disjoint-set A) -> (disjoint-set A))))
(define (safe-parent x)
  (or (disjoint-set-parent x)
      x))

#;(: union! : (All (A) ((disjoint-set A) (disjoint-set A) -> Void)))
(define (union! x y)
  (let ((xroot (find! x))
        (yroot (find! y)))
    (unless (eqv? xroot yroot)
            ;; x smaller than y, so make x's parent y, making x longer.
            (cond [(< (disjoint-set-rank xroot) (disjoint-set-rank yroot))
                   (set-disjoint-set-parent! (safe-parent xroot) yroot)]
                  [(> (disjoint-set-rank xroot) (disjoint-set-rank yroot))
                   (set-disjoint-set-parent! (safe-parent yroot) xroot)]
                  [else (set-disjoint-set-parent! (safe-parent yroot) xroot)
                        (set-disjoint-set-rank! xroot
                                                (add1 (disjoint-set-rank xroot)))]))))

#;(: set-equal? : (All (A) ((disjoint-set A) (disjoint-set A) -> Boolean)))
(define (set-equal? x y)
  (eqv? (find! x) (find! y)))

#;(: set-eqv-classes : (All (A) ((Listof (disjoint-set A)) -> (Listof (Listof A)))))
(define (set-eqv-classes xs)
  (let set-eqv-classes ([xs xs]
                        [classes '()])
    (if (empty? xs)
        classes
        (let ((x (car xs)))
          (let set-eqv-class ([xs xs]
                              [class '()]
                              [todo '()])
            (cond [(empty? xs)
                   (set-eqv-classes todo (cons class classes))]
                  [(set-equal? x (car xs))
                   (set-eqv-class (cdr xs)
                                  (cons (disjoint-set-elem (car xs)) class)
                                  todo)]
                  [else (set-eqv-class (cdr xs) class (cons (car xs) todo))]))))))

#;(: set-eqv-class : (All (A) ((disjoint-set A) (Listof (disjoint-set A)) -> (Listof A))))
(define (set-eqv-class x xs)
  (let loop ([xs xs]
             [class '()])
    (cond [(empty? xs)
           class]
          [(set-equal? x (car xs))
           (loop (cdr xs)
                 (cons (disjoint-set-elem (car xs)) class))]
          [else (loop (cdr xs) class)])))

;; We can package this all up to map elems to their disjoint-sets
;; and keep things sane.
(define union-find%
  (class object%
         (init-field (elem↦disjoint-set (make-hash)))

         (define/private (find-internal elem)
           (find! (hash-ref! elem↦disjoint-set
                             elem
                             (λ () (make-set elem)))))

         (define/public (find elem)
           (disjoint-set-elem (find-internal elem)))

         (define/public (union elem₁ elem₂)
           (union! (find-internal elem₁) (find-internal elem₂)))

         (define/public (all-eqv-classes)
           (set-eqv-classes (hash-values elem↦disjoint-set)))

         (define/public (elem-eqv-class elem)
           (set-eqv-class (hash-ref! elem↦disjoint-set elem (λ () (make-set elem)))
                          (hash-values elem↦disjoint-set)))
         (super-new)))

(provide make-set find! union! set-equal? set-eqv-class set-eqv-classes
         union-find%)