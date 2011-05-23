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

;; Node * Node -> Node
(define (least-common-ancestor a b)
  (let ([aseen (make-hash)]
        [bseen (make-hash)])
    (let loop ([anode a]
               [bnode b]
               [b-next #f]) ;; #f if a next, #t if b next
      (let-values ([(key hash anode bnode)
                    (if b-next
                        (values b aseen anode (Node-next bnode))
                        (values a bseen (Node-next anode) bnode))])
        (if (hash-has-key? hash key)
            key
            (if key
                (begin (hash-set! hash key #t)
                       (loop anode bnode (not b-next)))
                (error "LCA: not in same eqv class ~a ~a" a b)))))))

(define (explain t-state consteq)
  (explain-aux t-state (instantiate union-find% ()) consteq))

(define (explain-aux t-state UF consteq)
  (let ([anode (get-node t-state (ConstEQ-a₁ consteq))]
        [bnode (get-node t-state (ConstEQ-a₂ consteq))]
        [ab-lca (least-common-ancestor a b)])
    (append (explain-along-path t-state UF anode ab-lca)
            (explain-along-path t-state UF bnode ab-lca))))

(define (explain-along-path t-state UF a c)
  (let loop ([pending '()]
             [a (send UF find a)])
    (if (eqv? a c)
        (for/list ([consteq pending]) ;; explain the rest
          (explain-aux t-state UF pending))
        (let ([b (Node-next anode)])
          (send UF union a b) ;; a and b have a common ancestor, thus equal.
          (match (Node-outlabel anode)
            [(? ConstEQ? a=b)
             (cons (dict-ref (EUF-state-eqlit t-state) a=b) ;; emit a=b literal as explanation.
                   (loop pending (send UF find b)))]
            [(EQpair (CurriedEQ a₁ a₂ a)
                     (CurriedEQ b₁ b₂ b))
             ;; emit structural equality explanation.
             (list* (dict-ref (EUF-state-eqlit t-state) (CurriedEQ a₁ a₂ a))
                    (dict-ref (EUF-state-eqlit t-state) (CurriedEQ a₁ a₂ a))
                    (loop (list* (ConstEQ a₁ b₁) ;; explain the extentional equality.
                                 (ConstEQ a₂ b₂)
                                 pending)
                          (send UF find b)))])))))
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
  (bthash-ref (EUF-state-proof t-state) tvar (Node #f 0 #f)))