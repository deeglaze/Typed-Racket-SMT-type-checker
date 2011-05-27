#lang racket

(require (for-syntax racket/syntax))
(provide struct-with-set)

(define-for-syntax (value-or-getter sv fv struct-name field-name param)
  (if (free-identifier=? field-name param)
      fv
      (let ([getter (format-id struct-name "~a-~a" struct-name param)])
        #`(#,getter #,sv))))

(define-syntax (make-struct-setter stx)
  (syntax-case stx ()
    [(_ struct-name field all-params ...)
     (with-syntax ([setter (format-id #'struct-name "set-~a-~a" #'struct-name #'field)])
       #`(define (setter struct-value field-value)
           (struct-name #,@(map (λ (param)
                                  (value-or-getter #'struct-value #'field-value #'struct-name #'field param))
                                (syntax->list #'(all-params ...))))))]))

;; Does not support super-structs or field options
(define-syntax (struct-with-set stx)
  (syntax-case stx ()
    [(_ struct-name (params ...) extras ...)
     #'(begin (struct struct-name (params ...) extras ...)
              (make-struct-setter struct-name params params ...) ...)]))
