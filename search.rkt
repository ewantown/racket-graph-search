#lang racket

;; ==========================================================================
;; Basic struct def for directed graph node:

;; (node X Y (listof node))
;; (equal? <node> <node>) :: (equal? X X)
(struct node (id data arcs)
  #:methods
  gen:equal+hash
  ;; Simple hashing scheme (id hashcodes)
  ;; presupposes no duplicate node ids 
  [(define (equal-proc a b recur)
     (and (equal? (node-id a)   (node-id b))
          (equal? (node-data a) (node-data b))))
   (define (hash-proc a recur) (equal-hash-code (node-id a)))
   (define (hash2-proc a recur) (equal-secondary-hash-code (node-id a)))])

;; ==========================================================================
;; Main search mechanism:

;; start  : node
;; goal?  : node -> boolean
;; path<  : (node node) -> boolean
;; pruner : (list (list node)) (list (list node)) -> (list (list node))
;; -----> : (list (list (list node)) (list node) (list (list node)))
;; Interp : (first  ret) := list of path expansions in "rewind" order (pi...p0)
;;        : (second ret) := path found, in rewind order (ni...n0)
;;        : (third  ret) := paths to unvisited frontier nodes, ordered by path<
(define (search start goal? path< pruner)
  (local [(define init-frnt (list (list start)))
          (define init-acc  empty)
                  
          (define (output acc res frnt)
            (list (reverse (map (lambda (p) (reverse p)) acc))
                  (reverse res)
                  (map (lambda (p) (reverse p)) frnt)))

          (define (probe frnt acc)
            (if (empty? frnt)
                (output ('(empty) '() '(empty)))
                (let ([path   (first frnt)])
                  (if (goal? (first path))
                      (output acc path (rest frnt))
                      (local [(define extens;ions of this path with discoverds
                                (map (lambda (n) (cons n path)) 
                                     (node-arcs (first path))))
                              (define fringe (pruner frnt extens))
                              (define reduct;ion of the recurrence
                                (filter (lambda (p) (not (equal? p path)))
                                        fringe))]

                        (probe (sort reduct path<) (cons path acc)))))))]
    
    (probe init-frnt init-acc)))

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

;; ==========================================================================
;; Priority functions

;; Simple tie-breaker
(define (pref p1 p2) (string<? (node-id (first p1)) (node-id (first p2))))

;; Simple heuristic
(define (est n) (node-data n)) 
(define (h< n1 n2) (< (est n1) (est n2))) 
(define (h= n1 n2) (= (est n1) (est n2)))

;; DFS order: prioritized stack
(define dfs< (lambda (p nxt) (or (> (length p) (length nxt))     
                                 (and (= (length p) (length nxt))
                                      (pref p nxt)))))

;; BFS order: prioritized queue
(define bfs< (lambda (p nxt) (or (< (length p) (length nxt))     
                                 (and (= (length p) (length nxt))
                                      (pref p nxt)))))

;; Least-cost-first: queue prioritized by path-cost
(define cost< (lambda (p nxt) (or (< (path-cost p) (path-cost nxt))
                                  (and (= (path-cost p) (path-cost nxt))
                                       (pref p nxt)))))

;; A*: queue prioritized by combined heuristic/cost weighting
(define a*< (lambda (p nxt)
  (local [(define (weight path) (+ (path-cost path) (est (first path))))]
    (or (< (weight p) (weight nxt))
        (and (= (weight p) (weight nxt))
             (pref p nxt))))))
                                 

;; ==========================================================================
;; Sample data:

(define Z (node "Z" 0.0  '()))
(define G (node "G" 4.0  (list Z)))
(define H (node "H" 6.0  (list Z)))
(define F (node "F" 12.0 (list G H Z)))
(define D (node "D" 9.0  (list F)))
(define E (node "E" 11.0 (list F)))
(define C (node "C" 19.0 (list D E F)))
(define A (node "A" 21.0 (list C)))
(define B (node "B" 19.0 (list C)))
(define S (node "S" 24.0 (list A B C)))

(define (cost edge)
  (cond [(or (equal? edge (cons S B)) (equal? edge (cons G Z))) 9.0]
        [(or (equal? edge (cons C F)) (equal? edge (cons F G))) 8.0]
        [(or (equal? edge (cons E F)) (equal? edge (cons F H))) 7.0]
        [(or (equal? edge (cons C D)) (equal? edge (cons D F))) 5.0]
        [(or (equal? edge (cons S C)) (equal? edge (cons C E))) 4.0]
        [(equal? edge (cons F Z)) 18.0]
        [(equal? edge (cons B C)) 13.0]
        [(equal? edge (cons H Z)) 6.0] 
        [(equal? edge (cons S A)) 3.0]
        [(equal? edge (cons A C)) 2.0]
        [else null]))

(define (path-cost lon)
  (local [(define route (reverse lon))
           (define (recsum p)
             (cond [(empty? p) (error "cost of empty path")]
                   [(empty? (rest p)) 0] ; singleton
                   [(null? (cost (cons (first p) (second p))))
                    (error "no such edge: "(map (lambda (n) (node-id n)) p))]
                   [else (+ (cost (cons (first p) (second p)))
                            (recsum (rest p)))]))]
    (recsum route)))

;; ==========================================================================
;; Sample output parameters

(define target? (lambda (nd) (equal? (node-id nd) "Z")))

(define (represent results)
  (let ([rep-acc (foldr (lambda (lon nxt)
                          (cons (map (lambda (n) (node-id n)) lon)
                                nxt))
                        empty
                        (first results))]
        [rep-path  (cons (map (lambda (nd) (node-id nd))
                              (second results))
                         (path-cost (reverse (second results))))]
                  
        [rep-frnt (foldr (lambda (lon nxt)
                          (cons (map (lambda (n) (node-id n)) lon)
                                nxt))
                        empty
                        (third results))])

    (display "Probed: \n")
    (pretty-print rep-acc)
    (display "Found: \n")
    (pretty-print rep-path)
    (display "Unexpanded: \n")
    (pretty-print rep-frnt)))


(define pruning prune-nothing)

(define DFS (search S target? dfs< pruning))
(define BFS (search S target? bfs< pruning))
(define COST< (search S target? cost< pruning))
(define A* (search S target? a*< pruning))

(define (main)
  
  (display "DFS\n")
  (represent DFS)
  (display "\n")
  
  (display "BFS\n")
  (represent BFS)
  (display "\n")
  
  (display "COST<\n")
  (represent COST<)
  (display "\n")
  
  (display "A*\n")
  (represent A*)
  (display "\n"))


;; ===========================================================================
;; Module interface:
(provide (struct-out node))
(provide prune-nothing prune-cycles prune-extension-joins prune-frontier-joins)
(provide search main)



