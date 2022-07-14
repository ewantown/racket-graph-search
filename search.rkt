#lang racket

;; ===========================================================================
;; Module interface:

(provide (struct-out node))
(provide prune-nothing prune-cycles prune-extension-joins prune-frontier-joins)
(provide tie::< dfs::< bfs::< cost::< h::< a*::<)
(provide cost::recur search::terminal search::iterative)
(provide ::tie<)
(provide represent)

;; ==========================================================================
;; Basic struct def for directed graph node:

;; (node X Y (listof node))
;; (equal? <node> <node>) :: (equal? X X)
(struct node (id data arcs)
  #:methods
  gen:equal+hash
  ;; Simple hashing scheme.
  ;; Note: requires unique identifiers for nodes.
  ;; However, always have at least three options:
  ;;   i) let id := `(,data) - i.e. data as symbol
  ;;  ii) let id := `(,arcs) - i.e. arc-list as symbol
  ;; iii) let id := `(,(cons data arcs)) - i.e. (data . arc) link as symbol
  [(define (equal-proc a b recur)
     (equal? (node-id a) (node-id b)))
   (define (hash-proc a recur) (equal-hash-code (node-id a)))
   (define (hash2-proc a recur) (equal-secondary-hash-code (node-id a)))])

;; ==========================================================================
;; Core search mechanism

;; Formats output as "snapshot" of termination state
(define (output acc res frnt)
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
(define (search::terminal path< prune)
  (lambda (start goal?)
    (local [(define init-frnt (list (list start)))
            (define init-acc  empty)
            
            (define (probe frnt acc)
              (if (empty? frnt)
                  (output acc empty empty)
                  (let ([path   (first frnt)])
                    (if (goal? (first path))
                        (output acc path (rest frnt))
                        (local [(define extens;ions of this path
                                  (map (lambda (n) (cons n path)) 
                                       (node-arcs (first path))))
                                (define fringe (prune frnt extens))
                                (define reduct;ion of the recurrence
                                  (filter (lambda (p) (not (equal? p path)))
                                          fringe))]

                          (probe (sort reduct path<) (cons path acc)))))))]
      
      (probe init-frnt init-acc))))

;; ==========================================================================
;; Factory for path cost functions

;; lon   : (list node); s.t.: (first lon) is current, (last lon) is initial
;; costfn: (cons node node) -> number; s.t. edge-pair is (cons tail head)
;; ----->: (list node) -> number; s.t. computes cost(path-to-curr) recursively
(define (cost::recur costfn)
  (lambda (lon)
    (local [(define route (reverse lon)) 
            (define (recsum p)
              ;; error conditions caught with +/- infinite costs
              ;; messages for data reversal / termination debug
              (cond [(empty? p) -inf.0]
                    ;(error "cost of empty path")]
                    [(empty? (rest p)) 0] ; singleton
                    [(null? (costfn (cons (first p) (second p)))) +inf.0]
                    ;(error "no such edge: "(map (lambda (n) (node-id n)) p))]
                    [else (+ (costfn (cons (first p) (second p)))
                             (recsum (rest p)))]))]
      (recsum route))))

;; ==========================================================================
;; Factories for priority functions

;; Tie-breaker factory (breakers are by node id)
;; Defaults to:
;; - false for type-clash
;; - defer to built-in ordering if node ids are primitives
;; - recursively deepen comparison for (partial) ties
;; Specifiable behaviour is for lists as ids
(define (tie::< list-data-rel)
  (lambda (p1 p2)
    (local [(define (breaker l1 l2)
              (let ([i1 (if (empty? l1) null (node-id (first l1)))]
                    [i2 (if (empty? l2) null (node-id (first l2)))])
                (cond [(null? i1) (not (null? i2))]
                      [(null? i2) false]
                      [(and (number? i1) (number? i2))
                       (or (< i1 i2)
                           (and (= i1 i2)
                                (breaker (rest l1) (rest l2))))]
                      [(and (symbol? i1) (symbol? i2))
                       (or (symbol<? i1 i2)
                           (and (equal? i1 i2)
                                (breaker (rest l1) (rest l2))))]
                      [(and (string? i1) (string? i2))
                       (or (string<? i1 i2)
                           (and (equal? i1 i2)
                                (breaker (rest l1) (rest l2))))]
                      [(and (list? i1) (list? i2)) (list-data-rel i1 i2)]
                      [else false])))]
      (cond 
            [else (breaker (reverse p1) (reverse p2))]))))
                  
;; Provided (default) tie-breaking relation
(define ::tie< (tie::< (lambda (l1 l2) (< (length l1) (length l2)))))

;; DFS relation factory
(define (dfs::< tie/<)
  (lambda (p nxt) (or (> (length p) (length nxt))     
                      (and (= (length p) (length nxt))
                           (tie/< p nxt)))))

;; BFS relation factory
(define (bfs::< tie/<)
  (lambda (p nxt) (or (< (length p) (length nxt))     
                      (and (= (length p) (length nxt))
                           (tie/< p nxt)))))
  
;; Cost relation factory
(define (cost::< costfn tie/<)
  (let ([cost/rec (cost::recur costfn)]) 
    (lambda (p nxt) (or (< (cost/rec p) (cost/rec nxt))
                        (and (= (cost/rec p) (cost/rec nxt))
                             (tie/< p nxt))))))

;; Heuristic relation factory
(define (h::< h tie/<)
  (lambda (p nxt)
      (or (< (h (first p)) (h (first nxt)))
          (and (= (h (first p)) (h (first nxt)))
               (tie/< p nxt)))))

;; A* relation factory
(define (a*::< h cost/rec tie/<) 
  (lambda (p nxt)
    (local [(define (weight p) (+ (h (first p)) (cost/rec p)))]
      (or (< (weight p) (weight nxt))
          (and (= (weight p) (weight nxt))
               (tie/< p nxt))))))                                    
                                    
;; ==========================================================================
;; Iterative Bounded Search Factory

;; xfs/<     : ((list node) (list node)) -> boolean
;; solnweight: (list node) -> number
;; --------->: (node (node -> boolean)) -> (typeof output)
(define (search::iterative xfs/< solnweight)
  (lambda (start goal?)
    (local [(define init-probe
              ((search::terminal xfs/< prune-cycles) start goal?))
            (define init-rsf (reverse (second init-probe)))]     
      (if (empty? init-rsf) ; (failed search?)
          (output (reverse (map (lambda (p) (reverse p)) (first init-probe)))
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
                      (output acc rsf empty)
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


;; ==========================================================================
;; Pruning functions (self-explanatory?)

(define (prune-nothing frnt exts) (append exts frnt))

(define (prune-cycles frnt exts)
  (append (filter (lambda (p) (not (member (first p) (rest p)))) exts)
          frnt))

(define (prune-frontier-joins  frnt exts)
  (append exts
          (filter (lambda (fp)
                    (andmap (lambda (ep)
                              (not (equal? (first ep) (first fp))))
                            exts))
                  frnt)))

(define (prune-extension-joins frnt exts)
  (append (filter (lambda (ep)
                    (andmap (lambda (fp)
                              (not (equal? (first fp) (first ep))))
                            frnt))
                  exts)
          frnt))

;; =======================================================================
;; Display format (for result inspection)
;; results  : (cons (list (list node)) (list node) (list (list node)))
;; cost/rec : (list node) -> number
;; flag     : boolean (:= display-partial-path-costs?)

(define (represent results cost/rec part-cost-flag)
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




