#lang racket
(require "graph.rkt")
;; ===========================================================================
;; Interface:
(provide (struct-out fluent))
(provide fluent::->tree fluent::->models)

;; ===========================================================================
;; Data wrapper:
;; vars  : (listof X)
;; vals  : (listof Y)
;; interp: each X 'takes' one Y as value
(struct fluent (vars vals) #:transparent)

;; ===========================================================================
;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : ((cons X Y) (list (cons X Y))) -> boolean
;; ---------->: fluent -> node
(define (fluent::->tree pigeonvars var< legal?)
  (lambda (f0)
    (local [(define flu (fluent (sort (fluent-vars f0) var<) (fluent-vals f0)))
            (define (recur-deep agg flu)
              (if (or (empty? (fluent-vars flu))
                      (empty? (fluent-vals flu)))
                  (node `(,agg) agg empty)
                  (node `(,agg) 
                        agg
                        (recur-wide (map (lambda (val)
                                           (cons (first (fluent-vars flu)) val))
                                         (fluent-vals flu))
                                    agg
                                    (fluent (rest (fluent-vars flu))
                                            (fluent-vals flu))))))
            
            (define (recur-wide lop agg flu)
              (cond [(empty? lop) empty]
                    [(legal? (first lop) agg)
                     (local [(define val (cdr (first lop)))
                             (define vals- (filter (lambda (v)
                                                     (not (equal? v val)))
                                                   (fluent-vals flu)))]
                       (cons (recur-deep (cons (first lop) agg)
                                         (if pigeonvars
                                             (fluent (fluent-vars flu)
                                                     vals-)
                                             flu))
                             (recur-wide (rest lop) agg flu)))]
                    [else (recur-wide (rest lop) agg flu)]))]
      
      (recur-deep empty flu))))


;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : ((cons X Y) (list (cons X Y))) -> boolean
;; path<      : ((list node) (list node)) -> boolean
;; admit?     : (list (cons X Y)) -> boolean
;; ---------->: fluent -> (list (list (cons X Y)))
(define (fluent::->models pigeonvars var< legal? path< admit?)
  (lambda (f0)
    (local [(define root ((fluent::->tree pigeonvars var< legal?) f0))
            (define (goal? n)
              (and (empty? (node-arcs n))
                   (= (length (node-data n)) (length (fluent-vars f0)))))
            (define (probe frnt acc)
              (if (empty? frnt)
                  (reverse acc)
                  (let ([path (first frnt)])
                    (if (goal? (first path))
                        (probe (rest frnt)
                               (cons (node-data (first (first frnt))) acc))
                        (let ([reduct
                               (filter (lambda (alt)
                                         (and (not (equal? alt path))
                                              (admit? (node-data (first alt)))))
                                       (append (map (lambda (n) (cons n path))
                                                    (node-arcs (first path)))
                                                 frnt))])
                          (probe (sort reduct path<) acc))))))]
      (probe (list (list root)) empty))))
