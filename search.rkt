#lang racket

(require "graph.rkt" "fluent.rkt")
;; ===========================================================================
;; Interface:
(provide search::once search::bnb search::sat search::satset)

;; ==========================================================================
;; /First found/
;; start  : node
;; goal?  : node -> boolean
;; path<  : (node node) -> boolean
;; prune  : (list (list node)) (list (list node)) -> (list (list node))
;; -----> : (list node)

(define (search::once path< prune)
  (lambda (start goal?)
    (local [(define (probe frnt acc)
              (if (empty? frnt)
                  empty
                  (let ([path  (first frnt)])
                    (if (goal? (first path))
                        (reverse path) ; start->end
                        (let ([reduct
                               (filter (lambda (d)
                                         (not (equal? (first d) (first path))))
                                       (prune frnt
                                              (map (lambda (n) (cons n path))
                                                   (node-arcs (first path)))))])
                          (probe (sort reduct path<) (cons path acc)))))))]
      
      (probe (list (list start)) empty))))

;; ==========================================================================
;; /Branch and Bound/
;; path<     : ((list node) (list node)) -> boolean
;; solnweight: (list node) -> number
;; --------->: (node (node -> boolean)) -> (list node)

(define (search::bnb path< weight)
  (lambda (start goal?)
    (local [(define probe (search::once path< prune-cycles))
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
                        (let ([reduct
                               (filter (lambda (d)
                                         (and (not (equal? (first d)
                                                           (first path)))
                                              (< (weight d) bnd)))
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

(define (search::sat pigeonvars var< legal? flu<)
  (lambda (loflu)
    (local [(define ->models
              (fluent::->models pigeonvars var< legal?))
            (define cells
              (map (lambda (f) (->models f)) (sort loflu flu<)))
            (define (unify ctx agg aggwl ctxwl)
              (if (empty? ctx)
                  agg
                  (let ([admit
                         (filter (lambda (mdl)
                                   (andmap (lambda (pair) (legal? pair agg))
                                           mdl))
                                 (first ctx))])
                        (if (empty? admit)
                        (if (empty? ctxwl)
                           empty
                           (unify (first ctxwl)
                                  (first aggwl)
                                  (rest  aggwl)
                                  (rest  ctxwl)))
                        (unify (rest ctx)
                               (append agg (first admit))
                               (append (map (lambda (mdl) (append mdl agg))
                                            (rest admit))
                                       aggwl)
                               (append (map (lambda (i) (rest ctx))
                                            (rest admit))
                                       ctxwl))))))]
      (unify cells empty empty empty))))
             
             
             

;; ==========================================================================
;; /All (such) Models/
;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : ((cons X Y) (list (cons X Y))) -> boolean
;; path<      : ((list node) (list node)) -> boolean
;; admit?     : (list (cons X Y)) -> boolean
;; ---------->: (list fluent) -> (list (list (cons X Y)))

(define (search::satset pigeonvars var< legal? flu<)
  (lambda (loflu)
    (local [(define ->models
              (fluent::->models pigeonvars var< legal?))
            (define cells
              (map (lambda (flu) (->models flu)) (sort loflu flu<)))
            (define (unify ctx agg aggwl ctxwl rsf)
              (if (empty? ctx)
                  (if (empty? aggwl)
                      (reverse (cons agg rsf))
                      (unify (first ctxwl) (first aggwl)
                             (rest  aggwl) (rest  ctxwl)
                             (cons agg rsf)))
                  (let ([admit
                         (filter (lambda (mdl)
                                   (andmap (lambda (pair) (legal? pair agg))
                                           mdl))
                                 (first ctx))])
                    (if (empty? admit)
                        (if (empty? ctxwl)
                            (reverse rsf)
                            (unify (first ctxwl) (first aggwl)
                                   (rest  aggwl) (rest  ctxwl)
                                   rsf))
                        (unify (rest ctx)
                               (append agg (first admit))
                               (append (map (lambda (mdl) (append agg mdl))
                                            (rest admit))
                                       aggwl)
                               (append (map (lambda (i) (rest ctx))
                                            (rest admit))
                                       ctxwl)
                               rsf)))))]
      (unify cells empty empty empty empty))))


;; ==========================================================================
