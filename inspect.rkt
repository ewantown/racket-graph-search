#lang racket

(require "search.rkt" "graph.rkt" "fluent.rkt")


;; =======================================================================

(define (search::inspect search::X)
  (cond [(equal? search::X search::once)
         (lambda (path< prune pathmeasure)
           (lambda (start goal?)
             (let ([result ((inspect::terminal path< prune) start goal?)])
               (inspect::display result pathmeasure true))))]
        [(equal? search::X search::bnb)
         (lambda (path< weight pathmeasure)
           (lambda (start goal?)
             (let ([result ((inspect::bnb path< weight) start goal?)])
               (inspect::display result pathmeasure true))))]
        [else null]))


;; Formats output as "snapshot" of termination state
(define (inspect::format acc res frnt)
  (list (reverse (map (lambda (p) (reverse p)) acc))
        (reverse res)
        (map (lambda (p) (reverse p)) frnt)))

;; start  : node
;; goal?  : node -> boolean
;; path<  : (node node) -> boolean
;; prune  : (list (list node)) (list (list node)) -> (list (list node))
;; -----> : (list (list (list node)) (list node) (list (list node)))
;; Interp : (first  ret) := list of path expansions, in order expanded
;;        : (second ret) := path found
;;        : (third  ret) := paths to unvisited frontier nodes, ordered by path<
(define (inspect::terminal path< prune)
  (lambda (start goal?)
    (local [(define init-frnt (list (list start)))
            (define init-acc  empty)
            
            (define (probe frnt acc)
              (if (empty? frnt)
                  (inspect::format acc empty empty)
                  (let ([path  (first frnt)])
                    (if (goal? (first path))
                        (inspect::format acc path (rest frnt))
                        (local [(define extens;ions of this path
                                  (map (lambda (n) (cons n path)) 
                                       (node-arcs (first path))))
                                (define fringe (prune frnt extens))
                                (define reduct;ion of the recurrence
                                  (filter (lambda (p) (not (equal? p path)))
                                          fringe))]

                          (probe (sort reduct path<) (cons path acc)))))))]
      
      (probe init-frnt init-acc))))



;; xfs/<     : ((list node) (list node)) -> boolean
;; solnweight: (list node) -> number
;; --------->: (node (node -> boolean)) -> (typeof output)
(define (inspect::bnb xfs/< solnweight)
  (lambda (start goal?)
    (local [(define init-probe
              ((search::bnb xfs/< prune-cycles) start goal?))
            (define init-rsf (reverse (second init-probe)))]     
      (if (empty? init-rsf) ; (failed search?)
          (inspect::format (reverse (map (lambda (p) (reverse p)) (first init-probe)))
                  empty
                  empty)
          (local [(define init-frnt (map reverse (third init-probe)))
                  (define init-acc (map reverse (reverse (first init-probe))))
                  (define init-bnd (solnweight init-rsf))

                  (define (prune frnt exts bnd)
                    (append (filter (lambda (p) (< (solnweight p) bnd))
                                    exts)
                            frnt))
                  
                (define (it-probe frnt acc rsf bnd)
                  (if (empty? frnt)
                      (inspect::format acc rsf empty)
                      (let ([path (first frnt)])
                        (if (not (goal? (first path)))
                            (local [(define extens
                                      (map (lambda (n) (cons n path))
                                           (node-arcs (first path))))
                                    (define fringe (prune frnt extens bnd))
                                    (define reduct
                                      (filter (lambda (p)
                                                (not (equal? p path)))
                                              fringe))]
                              (it-probe (sort reduct xfs/<)
                                        (cons path acc)
                                        rsf
                                        bnd))
                            (local [(define nxtbnd (min (solnweight path) bnd))
                                    (define nxtrsf (if (= nxtbnd bnd)
                                                       rsf
                                                       path))
                                    (define nxtacc (cons path acc))]
                              (it-probe (filter (lambda (p) (< (solnweight p)
                                                               nxtbnd))
                                                (rest frnt))
                                        nxtacc
                                        nxtrsf
                                        nxtbnd))))))]
            (it-probe init-frnt (cons init-rsf init-acc) init-rsf init-bnd))))))
                                   
;; Display format (for result inspection)
;; results  : (cons (list (list node)) (list node) (list (list node)))
;; cost/rec : (list node) -> number
;; flag     : boolean (:= display-partial-path-costs?)

(define (inspect::display results cost/rec part-cost-flag)
  (let ([rep-acc (foldr (lambda (p nxt)
                          (cons
                           (if part-cost-flag
                               (cons (map (lambda (n) (node-id n)) p)
                                     (cost/rec (reverse p)))
                                     ; For f-values instead:
                                     ;(+ (node-data (last p))
                                     ;   (cost/rec (reverse p))))
                                                               
                               (map (lambda (n) (node-id n)) p))
                           nxt))
                        empty
                        (first results))]
        [rep-path  (cons (map (lambda (nd) (node-id nd))
                              (second results))
                         (cost/rec (reverse (second results))))]
        [rep-frnt
         (foldr (lambda (p nxt)
                  (cons
                   (if part-cost-flag
                       (cons (map (lambda (n) (node-id n)) p)
                             (cost/rec (reverse p)))
                       (map (lambda (n) (node-id n)) p))                                     
                   nxt))
                empty
                (third results))])
    

    (display "Probed: \n")
    (pretty-print rep-acc)
    (display "Found: \n")
    (pretty-print rep-path)
    (display "Unexpanded: \n")
    (pretty-print rep-frnt)))





