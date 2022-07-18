#lang racket

(require "graph.rkt" "fluent.rkt")
;; ===========================================================================
;; Interface:
(provide search:once search::bnb search::sat search::satset)

;; ==========================================================================
;; /First found/
;; start  : node
;; goal?  : node -> boolean
;; path<  : (node node) -> boolean
;; prune  : (list (list node)) (list (list node)) -> (list (list node))
;; -----> : (list node)
(define (search:once path< prune)
  (lambda (start goal?)
    (local [(define (probe frnt acc)
              (if (empty? frnt)
                  empty
                  (let ([path  (first frnt)])
                    (if (goal? (first path))
                        (reverse path) ; start->end
                        (local [(define extens;ions of this path
                                  (map (lambda (n) (cons n path)) 
                                       (node-arcs (first path))))
                                (define fringe (prune frnt extens))
                                (define reduct;ion of the recurrence
                                  (filter (lambda (p) (not (equal? p path)))
                                          fringe))]

                          (probe (sort reduct path<) (cons path acc)))))))]
      
      (probe (list (list start)) empty))))

;; ==========================================================================
;; /Branch and Bound/
;; path<     : ((list node) (list node)) -> boolean
;; solnweight: (list node) -> number
;; --------->: (node (node -> boolean)) -> (list node)
(define (search::bnb path< weight)
  (lambda (start goal?)
    (local [(define probe (search:once path< prune-cycles))
            (define bench (probe start goal?))
            (define (optimize frnt rsf bnd)
              (if (empty? frnt)
                  (reverse rsf) ; start->end
                  (let ([path (first frnt)])
                    (if (goal? (first path))
                        (let ([nxtbnd (min (weight path) bnd)])
                          (optimize (filter (lambda (p) (< (weight p) nxtbnd))
                                            (rest frnt))
                                    (if (= nxtbnd bnd) rsf path)
                                    nxtbnd))
                        (let ([reduct (filter (lambda (p)
                                                (and (not (equal? p path))
                                                     (< (weight p) bnd)))
                                       (append (map (lambda (n) (cons n path))
                                                    (node-arcs (first path)))
                                               frnt))])
                          (optimize (sort reduct path<) rsf bnd))))))]
      (if (empty? bench)
          empty
          (optimize (list (list start)) bench (weight bench))))))

;; ==========================================================================
;; /First (such) Model Found/
;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : ((cons X Y) (list (cons X Y))) -> boolean
;; path<      : ((list node) (list node)) -> boolean
;; admit?     : (list (cons X Y)) -> boolean
;; ---------->: (list fluent) -> (list (list (cons X Y)))

(define (search::sat pigeonvars var< legal? path< admit? flu<)
  (lambda (loflu)
    (local [(define ->models
              (fluent::->models pigeonvars var< legal? path< admit?))
            (define (unify ctx agg aggwl ctxwl)
              (if (empty? ctx)
                  (reverse agg)
                  (let ([admitted 
                         (filter (lambda (mdl)
                                   (and (andmap (lambda (pair)
                                                  (legal? pair agg))
                                                mdl)
                                        (admit? (append mdl agg))))
                                 (first ctx))])
                    (if (empty? admitted)
                        (if (empty? ctxwl)
                           empty
                           (unify (first ctxwl)
                                  (first aggwl)
                                  (rest  aggwl)
                                  (rest  ctxwl)))
                        (unify (rest ctx)
                               (append (first admitted) agg)
                               (append (map (lambda (mdl) (append mdl agg))
                                            (rest admitted))
                                       aggwl)
                               (append (map (lambda (i) (rest ctx))
                                            (rest admitted))
                                       ctxwl))))))]
      (unify (map (lambda (f) (->models f)) (sort loflu flu<))
             empty
             empty
             empty))))

;; ==========================================================================
;; /All (such) Models/
;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : ((cons X Y) (list (cons X Y))) -> boolean
;; path<      : ((list node) (list node)) -> boolean
;; admit?     : (list (cons X Y)) -> boolean
;; ---------->: (list fluent) -> (list (list (cons X Y)))

(define (search::satset pigeonvars var< legal? path< admit? flu<)
  (lambda (loflu)
    (local [(define ->models
              (fluent::->models pigeonvars var< legal? path< admit?))
            (define (unify lolomdl agg aggwl ctxwl rsf)
              (if (empty? lolomdl)
                  (if (empty? aggwl)
                      (reverse (cons (reverse agg) rsf))
                      (unify (first ctxwl)
                             (first aggwl)
                             (rest  aggwl)
                             (rest  ctxwl)
                             (cons (reverse agg) rsf)))
                  (let ([admitted 
                         (filter (lambda (mdl)
                                   (and (andmap (lambda (pair)
                                                  (legal? pair agg))
                                                mdl)
                                        (admit? (append mdl agg))))
                                 (first lolomdl))])
                    (if (empty? admitted)
                        (if (empty? ctxwl)
                            empty
                            (unify (first ctxwl)
                                   (first aggwl)
                                   (rest  aggwl)
                                   (rest  ctxwl)
                                   rsf))
                        (unify (rest lolomdl)
                               (append (first admitted) agg)
                               (append (map (lambda (mdl) (append mdl agg))
                                            (rest admitted))
                                       aggwl)
                               (append (map (lambda (i) (rest lolomdl))
                                            (rest admitted))
                                       ctxwl)
                               rsf)))))]
          (unify (map (lambda (f) (->models f)) (sort loflu flu<))
                 empty
                 empty
                 empty
                 empty))))

;; ==========================================================================
