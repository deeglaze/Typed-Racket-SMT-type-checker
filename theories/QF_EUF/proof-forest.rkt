#lang racket

(require "data-structures.rkt"
         "unionfind.rkt")

(provide add-explanation! explain)

(define (add-explanation! t-state start end label)
  (let*-values ([(snode) (get-node t-state start)]
                [(enode) (get-node t-state end)]
                [(start snode enode) ;; WLOG |start| ≤ |end|
                 (if (<= (Node-size snode) (Node-size enode))
                     (values start snode enode)
                     (values end enode snode))])
    (reverse-path-to-root! t-state snode)
    (add-edge! snode enode label)))

(define (explain t-state consteq)
  (let ([UF (instantiate union-find%)]
        [a (ConstEQ-a₁ consteq)]
        [b (ConstEQ-a₂ consteq)]
        [c (LCA a b)]) ;; least-common-ancestor
    (append (explain-along-path t-state UF a c)
            (explain-along-path t-state UF b c))))

(define (explain-along-path t-state UF a c)
  (let loop ([pending '()]
             [a (send UF find a)])
         [anode (get-node t-state a)])
    (if (eqv? a c)
        (for/list ([consteq pending])
          (explain t-state pending))
        (let ([bnode (Node-next anode)])
          (match (Node-outlabel anode)
            [(? ConstEQ? a=b)
             (list (dict-ref (EUF-state-equalities t-state) a=b))]
            [(? EQpair? fa₁a₂=a×fb₁b₂=b)
             ...])))) ;; TODO
#|
This next mutation heavy function has a trick to it. We need to
maintain the invariant that (Node-size node) = # children of node.
Every node in the path along the way will be getting a larger size,
except for the previous root, which has to relinquish all the children
it previously had.
We thus add up how many children this root will be losing by reversing
this path and at the end, subtract that from its size.
|#
(define (reverse-path-to-root! node [weight-of-path 0])
  (if (Node-next node)
      (begin
        (reverse-path-to-root! (Node-next node)
                               (+ 1 (Node-size node) weight-of-path))
        (set-Node-size! node (add1 (Node-size (Node-next node))))
        ;; Reverse the outgoing edge
        (set-Node-next! (Node-next node) node)
        ;; node -L-> next (node == (Node next _ L)) is now
        ;; next -L-> node (next == (Node node _ L))
        (set-Node-outlabel! (Node-next node) (Node-outlabel node))
        ;; node is now root.
        (set-Node-next! node #f)
        (set-Node-outlabel! node #f))
      (set-Node-size! node (- (Node-size node) weight-of-path))))

(define (add-edge! snode enode label)
  ;; s -> e
  (set-Node-next! snode enode)
  ;; s -L-> e
  (set-Node-outlabel! snode label)
  ;; s has |s| children.
  ;; e had |e| children.
  ;; With s, e will have 1 + |s| more children (we now count s)
  (set-Node-size! enode (+ 1 (Node-size snode) (Node-size enode))))

(define (get-node t-state tvar)
  (bthash-ref (EUF-state-proof t-state) tvar
              (λ () (error "get-node: internal error"))))