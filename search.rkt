#lang racket

(require "graph.rkt" "fluent.rkt")
;; ===========================================================================
;; Interface:
(provide search::once
         search::all
         search::bnb
         search::models
         search::sat
         search::satset
         search::sls
         search::anneal
         search::beam)


;; ==========================================================================
;; /First solution path found/
;; start  : node
;; goal?  : node -> boolean
;; path<  : (node node) -> boolean
;; prune  : (list (list node)) (list (list node)) -> (list (list node))
;; -----> : (list node)
(define (search::once path< prune)
  (λ (start goal?)
    (local [(define (probe frnt)
              (if (empty? frnt)
                  empty
                  (let ([path  (first frnt)])
                    (if (goal? (first path))
                        (reverse path) ; start->end
                        (let ([reduct (prune (map (λ (n) (cons n path))
                                                  (node-arcs (first path)))
                                             (rest frnt))])
                          (probe (sort reduct path<)))))))]
      (probe (list (list start))))))

;; ==========================================================================
;; /All solution paths/
;; start  : node
;; goal?  : node -> boolean
;; path<  : (node node) -> boolean
;; prune  : (list (list node)) (list (list node)) -> (list (list node))
;; -----> : (list node)
(define (search::all path< prune)
  (λ (start goal?)
    (local [(define (probe frnt rsf) 
              (if (empty? frnt)
                  (reverse rsf)
                  (let ([path (first frnt)]) 
                    (if (goal? (first path)) 
                        (probe (rest frnt)   
                               (cons (reverse path) rsf))
                        (let ([reduct (prune (map (λ (n) (cons n path))
                                                  (node-arcs (first path)))
                                             (rest frnt))])
                          (probe (sort reduct path<) rsf))))))]
      (probe (list (list start)) empty))))


;; ==========================================================================
;; /Branch and Bound/
;; path<     : ((list node) (list node)) -> boolean
;; solnweight: (list node) -> number
;; --------->: (node (node -> boolean)) -> (list node)
(define (search::bnb path< weight)
  (λ (start goal?)
    (local [(define probe (search::once path< prune-cycles))
            (define bench (probe start goal?))
            (define (optimize frnt rsf bnd)
              (if (empty? frnt)
                  (reverse rsf) ; start->end
                  (let ([path (first frnt)])
                    (if (goal? (first path))
                        (let ([nxtbnd (min (weight path) bnd)])
                          (optimize (filter (λ (p) (< (weight p) nxtbnd))
                                            (rest frnt))
                                    (if (= nxtbnd bnd) rsf path)
                                    nxtbnd))
                        (let ([reduct
                               (filter (λ (d) (< (weight d) bnd))
                                       (append (map (λ (n) (cons n path))
                                                    (node-arcs (first path)))
                                               (rest frnt)))])
                          (optimize (sort reduct path<) rsf bnd))))))]
      (if (empty? bench)
          empty
          (optimize (list (list start)) bench (weight bench))))))


;; ==========================================================================
;; /Models of a fluent/
;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : (list (cons X Y)) -> boolean
;; ---------->: fluent -> (list (list (cons X Y)))
(define (search::models pigeonvars loc)
  (λ (f0)
    (local [(define root (fluent::tree f0 pigeonvars loc))
            (define (goal? n)
              (and (empty? (node-arcs n))
                   (= (length (node-data n)) (length (fluent-vars f0)))))]
      (map (λ (p) (reverse (node-data (last p))))
           ((search::all path<::dfs append) root goal?)))))

;; ==========================================================================
;; /First Found Model of Fluents/
;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : (list (cons X Y)) -> boolean
;; flu<       : (fluent fluent) -> boolean
;; ---------->: (list fluent) -> (list (list (cons X Y)))
(define (search::sat pigeonvars loc)
  (λ (loflu)
    (local [(define cells (map (λ (f) (search::models f pigeonvars loc)) loflu))
            (define (unify ctx agg aggwl ctxwl)
              (if (empty? ctx)
                  agg
                  (let ([admit
                         (filter (λ (mdl)
                                   (andmap (λ (pair)
                                             ((laws->sat? loc) (cons pair agg)))
                                           mdl))
                                 (first ctx))])                         
                    (if (empty? admit)
                        (if (empty? ctxwl)
                            empty
                            (unify (first ctxwl) (first aggwl)
                                   (rest  aggwl) (rest  ctxwl)))
                        (unify (rest ctx)
                               (append agg (first admit))
                               (append (map (λ (mdl) (append mdl agg))
                                            (rest admit))
                                       aggwl)
                               (append (map (λ (i) (rest ctx))
                                            (rest admit))
                                       ctxwl))))))]
      (unify cells empty empty empty))))

;; ==========================================================================
;; /All Models of Fluents/
;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : (list (cons X Y)) -> boolean
;; path<      : ((list node) (list node)) -> boolean
;; admit?     : (list (cons X Y)) -> boolean
;; ---------->: (list fluent) -> (list (list (cons X Y)))
(define (search::satset pigeonvars loc)
  (λ (loflu) 
    (local [(define cells (map (λ (f) (search::models f pigeonvars loc)) loflu))
            (define (unify ctx agg aggwl ctxwl rsf)
              (if (empty? ctx) ; If aggregation complete (agg is a full model)
                  (if (empty? aggwl) ; If no more aggregates to extend...
                      (reverse (cons agg rsf)) ; return the list of models.
                      (unify (first ctxwl) (first aggwl) ; Else reduce worklist
                             (rest  aggwl) (rest  ctxwl)
                             (cons agg rsf)))
                  (let ([admit ; Models in first of context consistent w/ agg
                         (filter (λ (mdl)
                                   (andmap (λ (pair) ((laws->sat? loc)
                                                      (cons pair agg)))
                                           mdl))
                                 (first ctx))])
                    (if (empty? admit) ; If no models consistent w/ this agg...
                        (if (empty? ctxwl) ; If more aggregates to extend...
                            (reverse rsf)  ; return the list of models,
                            (unify (first ctxwl) (first aggwl) ; else reduce wl
                                   (rest  aggwl) (rest  ctxwl) 
                                   rsf))
                        (unify (rest ctx) ; Recurse
                               (append agg (first admit))
                               (append (map (λ (mdl) (append agg mdl))
                                            (rest admit))
                                       aggwl)
                               (append (map (λ (i) (rest ctx))
                                            (rest admit))
                                       ctxwl)
                               rsf)))))]
      
      (unify cells empty empty empty empty))))

;; ==========================================================================
;; Probabilistic bit
;; p :: real in (0...1)
;; (pbit p) is true with probability = p
(define (pbit p) (<= (random) p))

;; ==========================================================================
;; /Stochastic Local Search/
;; nbhood : (list (cons X Y)) -> (list (list (cons X Y)))
;; model? : (list (cons X Y)) -> boolean
;; reset  : (list (cons X Y)) -> (list (cons X Y))
(define (search::sls nbhood model? reset)
  ;; timeout : integer >= 0 := max num trials
  ;; score   : (list (cons X Y)) -> number
  ;; p-...   : real in [0, 1] := probabilities
  (λ (timeout score p-rand p-reset) 
    ;; agg : (list (cons X Y)) := initial total assignment
    (λ (agg)
      (local [(define (recurse trials curr bsf)
                (cond [(model? curr) (cons (cons 'trials trials) curr)]
                      [(= trials timeout) bsf]
                      [else
                       (local [(define nbrs
                                 (sort (nbhood curr)
                                       (lambda (i j) (> score i) (score j))))
                               (define nxt
                                 (cond [(pbit p-reset) (reset curr)]
                                       [(pbit p-rand)
                                        (list-ref nbrs (random (length nbrs)))]
                                       [(< (score curr) (score (first nbrs)))
                                        (first nbrs)]
                                       [else curr]))]
                         (recurse (add1 trials)
                                  nxt
                                  (if (< (score bsf) (score nxt)) nxt bsf)))]))]
        (recurse 0 agg agg)))))

;; ==========================================================================
;; /Simulated Annealing/
;; nbhood : (list (cons X Y)) -> (list (list (cons X Y)))
;; model? : (list (cons X Y)) -> boolean
(define (search::anneal nbhood model?)
  ;; timeout : integer >= 0 := max num trials
  ;; temp    : integer -> number
  ;; score   : (list (cons X Y)) -> number
  (λ (timeout temp score)
    ;; agg : (list (cons X Y)) := initial total assignment
    (λ (agg)
      (local [(define (recurse trials curr bsf)
                (cond [(model? curr) (cons (cons 'trials trials) curr)]
                      [(= trials timeout) bsf]
                      [else
                       (let ([nbr (list-ref (nbhood curr)
                                            (random (length (nbhood curr))))])
                         (if (or (< (score curr) (score nbr))
                                 (pbit (exp (/ (- (score curr) (score nbr))
                                               (temp trials)))))
                             (recurse (add1 trials)
                                      nbr
                                      (if (< (score bsf) (score nbr)) nbr bsf))
                             (recurse (add1 trials)
                                      curr
                                      bsf)))]))]
        (recurse 0 agg agg)))))

;; ==========================================================================
;; /Beam Search/
;; mutants : (list (cons X Y)) -> (list (list (cons X Y)))
;; model?  : (list (cons X Y)) -> boolean
(define (search::beam mutants model?)
  ;; timeout  : integer >= 0 := max num trials
  ;; score    : (list (cons X Y)) -> number
  ;; pop-size : integer
  (λ (timeout score pop-size) 
    ;; agg : (list (cons X Y))
    (λ (agg)
      (local [(define init-pop (map (build-list pop-size (λ (i) i)) agg))
              (define (scan-pop pop)
                (cond [(empty? pop) null]
                      [(model? (first pop)) (first pop)]
                      [else (scan-pop (rest pop))]))
              (define (next-gen pop)
                (take pop-size
                      (sort (foldr (λ (nbrs nx) (append nbrs nx))
                                   empty
                                   (map (λ (n) (mutants n)) pop))
                            (λ (n1 n2) (> (score n1) (score n2))))))
              (define (recurse pop gens bsf)
                (let ([res (scan-pop pop)]
                      [nxt (next-gen pop)])
                  (cond [(not (null? res)) res]
                        [(= gens timeout)  bsf]
                        [else (recurse nxt
                                  (add1 gens)
                                  (if (< (score bsf) (score (first nxt)))
                                      (first nxt)
                                      bsf))])))]
        (recurse init-pop 0 init-pop)))))

;; ==========================================================================
