#lang racket

(require "search.rkt")

(provide h tie<)

;; ==========================================================================
;; Sample data:

(define Z (node 'Z 0.0  '()))
(define G (node 'G 4.0  (list Z)))
(define H (node 'H 6.0  (list Z)))
(define F (node 'F 12.0 (list G H Z)))
(define D (node 'D 9.0  (list F)))
(define E (node 'E 11.0 (list F)))
(define C (node 'C 19.0 (list D E F)))
(define A (node 'A 21.0 (list C)))
(define B (node 'B 19.0 (list C)))
(define S (node 'S 24.0 (list A B C)))

;     A     D     G
;   /   \ /   \ /   \
;  S --- C --- F --- Z
;   \   / \   / \   /
;     B     E     H

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

;; ==========================================================================
;; Sample parameter specs

;; Simple tie-breaker
;; Notes: Client can only (& must) specify case for nodes w/ lists as ids.
;; In other standard cases ties are broken by comparing primitives.
;; In non-standard and type-clash cases, always evals to false.
(define tie< (tie::< (lambda (l1 l2) (< (length l1) (length l2)))))

;; DFS order: tie-prioritized stack
(define dfs< (dfs::< tie<))

;; BFS order: tie-prioritized queue
(define bfs< (bfs::< tie<))

;; Sums cost of edges over list of nodes (LON)
;; Notes: Cost function is provided by client.
;; The defined procedure is such that:
;; = +inf.0 if LON is empty
;; =      0 if LON is singleton
;; = -inf.0 if (cost ((car LON) . (car (cdr LON)))) is null (aka empty)
(define path-cost (cost::recur cost))

;; Least-cost-first: Cost-prioritized queue (w/ order finalized by tie-breaker)
(define cost< (cost::< cost tie<))

;; Simple heuristic (w/ data-dependent admissability)

(define h node-data)

(define h< (h::< h tie<))

;; A*: Queue prioritized by path-cost + heuristic weighting (tie-breaker final)
(define a*< (a*::< h path-cost tie<))

;; Demo search specs
(define target? (lambda (nd) (equal? (node-id nd) 'Z)))
(define pruner prune-nothing)
                                       
(define FAIL ((search::terminal  dfs<     pruner) A (lambda (n) (equal? n S))))
(define DFS  ((search::terminal  dfs<     pruner) S target?))
(define BFS  ((search::terminal  bfs<     pruner) S target?))
(define LCF  ((search::terminal  cost<    pruner) S target?))
(define A*   ((search::terminal  a*<      pruner) S target?))
(define DFBB ((search::iterative dfs<  path-cost) S target?))



;; ==========================================================================
;; Sample output:

(define show-part-costs #f)

(define (main)

  (display "FAIL\n")
  (represent FAIL path-cost show-part-costs)
  (display "\n")
  
  (display "DFS\n")
  (represent DFS path-cost show-part-costs)
  (display "\n")
  
  (display "BFS\n")
  (represent BFS path-cost show-part-costs)
  (display "\n")
  
  (display "LCF\n")
  (represent LCF path-cost show-part-costs)
  (display "\n")
  
  (display "A*\n")
  (represent A* path-cost show-part-costs)
  (display "\n")

  (display "DFBB\n")
  (represent DFBB path-cost show-part-costs)
  (display "\n"))






