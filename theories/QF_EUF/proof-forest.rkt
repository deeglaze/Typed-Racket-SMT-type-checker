#lang racket

(require "data-structures.rkt"
         "unionfind.rkt")

(provide add-explanation explain)

;; FIXME: Traversal is all screwed up due to the new hash way of doing things.

(define (add-explanation proof start end label)
  (let*-values ([(proof snode) (get-node proof start)]
                [(proof enode) (get-node proof end)]
                [(start end snode enode) ;; WLOG |start| ≤ |end|
                 (if (<= (Node-size snode) (Node-size enode))
                     (values start end snode enode)
                     (values end start enode snode))]
                [(proof) (reverse-path-to-root proof start)])
    (add-edge proof start end label)))

;; TVar * TVar -> Node
(define (least-common-ancestor proof a b)
  (let ([aseen (make-hash)] ;; Node ↦ Boolean
        [bseen (make-hash)])
    (let loop ([a a]
               [b b]
               [b-next #f]) ;; #f if a next, #t if b next
      (if (eqv? a b)
          a
          (let*-values ([(anode) (bthash-ref proof a)]
                        [(bnode) (bthash-ref proof b)]
                        [(key hash a b)
                         (if b-next
                             (values b aseen a (Node-next bnode))
                             (values a bseen (Node-next anode) b))])
            (cond [(hash-has-key? hash key) key]
                  [key
                   (hash-set! hash key #t)
                   (loop proof a b (not b-next))]
                  [else (error 'LCA "not in same eqv class" a b)]))))))

(define (explain eqlit proof consteq)
  (explain-aux eqlit proof (instantiate union-find% ()) consteq))

(define (explain-aux eqlit proof UF consteq)
  (let* ([a (ConstEQ-a₁ consteq)]
         [b (ConstEQ-a₂ consteq)]
         [ab-lca (least-common-ancestor proof a b)])
    (append (explain-along-path eqlit proof UF a ab-lca)
            (explain-along-path eqlit proof UF b ab-lca))))

;; a,c : TVar
(define (explain-along-path eqlit proof UF a c)
  (let loop ([pending '()]
             [a (send UF find a)])
    (if (eqv? a c)
        (for/list ([consteq pending]) ;; explain the rest
          (explain-aux eqlit proof UF pending))
        (let* ([anode (bthash-ref proof a
                                  (λ () (error 'explain-along-path "Node should have explanation" a)))]
               [b (Node-next anode)])
          (send UF union a b) ;; a and b have a common ancestor, thus equal.
          (match (Node-outlabel anode)
            [(? ConstEQ? a=b)
             (cons (dict-ref eqlit a=b) ;; emit a=b literal as explanation.
                   (loop pending (send UF find b)))]
            [(EQpair (CurriedEQ a₁ a₂ a)
                     (CurriedEQ c₁ c₂ c))
             ;; emit structural equality explanation.
             (list* (dict-ref eqlit (CurriedEQ a₁ a₂ a))
                    (dict-ref eqlit (CurriedEQ c₁ c₂ c))
                    (loop (list* (ConstEQ a₁ c₁) ;; explain the extentional equality.
                                 (ConstEQ a₂ c₂)
                                 pending)
                          (send UF find b)))]
            [other (error "explain-along-path fail ~a" other)])))))
#|
This next mutation heavy function has a trick to it. We need to
maintain the invariant that (Node-size node) = # children of node.
Every node in the path along the way will be getting a larger size,
except for the previous root, which has to relinquish all the children
it previously had.
We thus add up how many children this root will be losing by reversing
this path and at the end, subtract that from its size.
|#
(define (reverse-path-to-root proof node-num [weight-of-path 0])
  (let* ([node (bthash-ref proof node-num)]
         [next-node-num (Node-next node)])
    (if next-node-num
        (let* ([proof (reverse-path-to-root proof next-node-num
                                            (+ 1 (Node-size node) weight-of-path))]
               ;; updated in reversal
               [next-node (bthash-ref proof next-node-num)]
               ;; node -->X, |node| = 1 + |next|
               [proof (bthash-set proof node
                                  (Node #f (add1 (Node-size next-node)) #f))])
          ;; next -L-> node, size hasn't changed.
          (bthash-set proof next-node-num (Node node-num (Node-size next-node) (Node-outlabel node))))
        (bthash-set proof node-num (set-Node-size node (- (Node-size node) weight-of-path))))))

(define (add-edge proof start end label)
  ;; s -L-> e  with size |s|
   (bthash-set proof
               start
               (Node end
                     (Node-size (bthash-ref proof start))
                     label)))

(define (get-node proof tvar)
  (let ([result (bthash-ref proof tvar)])
    (if result
        (values proof result)
        (let ([new-node (Node #f 0 #f)])
          ;; if it doesn't exist, make a new node for it.
          (values (bthash-set proof tvar new-node) new-node)))))