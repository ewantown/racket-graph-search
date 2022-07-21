#lang racket

(require  "graph.rkt"
         "fluent.rkt"
         "inspect.rkt"
         "search.rkt")

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

(define pathcost (cost::sum cost))

(define cost< (path<::cost cost))

;; Heuristic (w/ data-dependent admissibility)
(define h node-data)

(define a*< (path<::a* h cost))

;; Demo search specs
(define target? (lambda (nd) (equal? (node-id nd) 'Z)))
(define pruner prune-nothing)

(define FAIL ((inspect::once  path<::dfs     pruner) A (lambda (n) (equal? n S))))
(define DFS  ((inspect::once  path<::dfs     pruner) S target?))
(define BFS  ((inspect::once  path<::bfs     pruner) S target?))
(define LCF  ((inspect::once  cost<          pruner) S target?))
(define A*   ((inspect::once  a*<            pruner) S target?))
(define CBDF ((inspect::bnb   path<::dfs     pathcost) S target?))
(define CBBF ((inspect::bnb   path<::bfs     pathcost) S target?))

(define nand-constraint (lambda (x agg)
                          (andmap (lambda (y) (not (and (cdr x) (cdr y))))
                                  
                                  agg)))

(define and-constraint (lambda (x agg)
                         (andmap (lambda (y) (and (cdr x) (cdr y))) agg)))

(define or-constraint (lambda (x agg)
                        (andmap (lambda (y) (or (cdr x) (cdr y)))                                                      agg)))

(define nor-constraint (lambda (x agg)
                         (andmap (lambda (y) (not (or (cdr x) (cdr y))))
                                 
                                 agg)))

(define (legality p lop)
  (local [(define (iffer sym1 sym2 pair bool)
            (or (not (equal? sym1 (car p)))
                (not (equal? sym2 (car pair)))
                (bool (cdr p) (cdr pair))))]
    (andmap (lambda (i)
              (and (iffer 'A 'G i (lambda (m n) (>= m n)))
                   (iffer 'G 'A i (lambda (m n) (>= n m)))
                   (iffer 'A 'H i (lambda (m n) (< m n)))
                   (iffer 'H 'A i (lambda (m n) (< n m)))
                   (iffer 'B 'F i (lambda (m n) (= 1 (abs (- n m)))))
                   (iffer 'F 'B i (lambda (m n) (= 1 (abs (- m n)))))
                   (iffer 'C 'G i (lambda (m n) (= 1 (abs (- n m)))))
                   (iffer 'G 'C i (lambda (m n) (= 1 (abs (- m n)))))
                   (iffer 'C 'D i (lambda (m n) (not (= m n))))
                   (iffer 'D 'C i (lambda (m n) (not (= n m))))
                   (iffer 'C 'E i (lambda (m n) (not (= m n))))
                   (iffer 'E 'C i (lambda (m n) (not (= n m))))
                   (iffer 'C 'F i (lambda (m n) (not (= m n))))
                   (iffer 'F 'C i (lambda (m n) (not (= n m))))
                   (iffer 'C 'H i (lambda (m n) (even? (abs (- n m)))))
                   (iffer 'H 'C i (lambda (m n) (even? (abs (- m n)))))
                   (iffer 'D 'H i (lambda (m n) (not (= m n))))
                   (iffer 'H 'D i (lambda (m n) (not (= n m))))
                   (iffer 'D 'E i (lambda (m n) (< n (sub1 m))))
                   (iffer 'E 'D i (lambda (m n) (< m (sub1 n))))
                   (iffer 'D 'F i (lambda (m n) (not (= m n))))
                   (iffer 'F 'D i (lambda (m n) (not (= n m))))
                   (iffer 'D 'G i (lambda (m n) (>= m n)))
                   (iffer 'G 'D i (lambda (m n) (>= n m)))
                   (iffer 'E 'F i (lambda (m n) (odd? (abs (- m n)))))
                   (iffer 'F 'E i (lambda (m n) (odd? (abs (- n m)))))
                   (iffer 'E 'H i (lambda (m n) (not (= m (- n 2)))))
                   (iffer 'H 'E i (lambda (m n) (not (= n (- m 2)))))
                   (iffer 'F 'G i (lambda (m n) (not (= m n))))
                   (iffer 'G 'F i (lambda (m n) (not (= n m))))
                   (iffer 'F 'H i (lambda (m n) (not (= m n))))
                   (iffer 'H 'F i (lambda (m n) (not (= n m))))
                   (iffer 'G 'H i (lambda (m n) (< m n)))
                   (iffer 'H 'G i (lambda (m n) (< n m)))))
            lop)))


;(random-seed 1) ; same sequence of randoms on each run
(define rand< (lambda (v1 v2) (< (random) 0.5))) ; coin flip
;(define var< (lambda (v1 v2) false)) ; for given order
(define var< symbol<?)



(define inspect-fluent (inspect::fluent->models false
                                                var<
                                                legality))

(define inspect-sat (inspect::sat false
                                  var<
                                  legality
                                  (lambda (x y) false)))

(define search-sat (search::sat false
                                var<
                                legality
                                (lambda (x y) false)))

(define inspect-satset (inspect::satset false
                                        var<
                                        legality
                                        (lambda (x y) false)))

(define search-satset (search::satset false
                                      var<
                                      legality
                                      (lambda (x y) false)))

(define searcher (search::satset false var< legality (lambda (x y) false)))

(define results (searcher (list (fluent (list 'E 'D 'H 'F 'C 'A 'G 'B)
                                        (list 1 2 3 4)))))
;(define afluent (fluent (list 'E 'D 'H 'F 'C 'A 'G 'B)
;                        (list 1 2 3 4)))


; Max cuts => lower in tree  => less efficient
;(define afluent (fluent (list 'F 'H 'D 'G 'A 'B 'C 'E)
;                        (list 1 2 3 4)))

; Min cuts => higher in tree => more efficient
(define afluent (fluent (list 'E 'D 'F 'C 'H 'G 'A 'B)
                        (list 1 2 3 4)))

(define partitioned (list (fluent (list 'F 'H 'D 'G) (list 1 2 3 4))
                          (fluent (list 'A 'B 'C 'E) (list 1 2 3 4))))

(define (optimize trials)
  ;(cdr (first rsf))
  (local [(define searcher (inspect::satset false rand< legality rand<))
          (define (rec rsf cnt)
            (if (= 0 cnt)
                rsf
                (let ([res (searcher (list afluent))]);partitioned)])
                  (rec (if (< (cdr (first res)) (cdr (first rsf)))
                           res
                           rsf)
                       (sub1 cnt)))))]
    (rec (searcher (list afluent)) trials)))

;; Experiment results:
;; (cut 4004): (F H D G) (A B C E)
;; (cut 84):   E D F C H G A B -- after 100k runs.

;; ==========================================================================
;; Sample output:
(define (main)
  ;(display "FAIL\n")
  ;(pretty-print FAIL)
  ;(display "\n")
  
  ;(display "Depth-First-Search\n")
  ;(pretty-print DFS)
  ;(display "\n")
  
  ;(display "Breadth-First-Search\n")
  ;(pretty-print BFS)
  ;(display "\n")
  
  ;(display "Least-Cost-First\n")
  ;(pretty-print LCF)
  ;(display "\n")
  
  ;(display "Cost-Bounded Depth-First B&B\n")
  ;(pretty-print CBDF)
  ;(display "\n")
  
  ;(display "Cost-Bounded Breadth-First B&B\n")
  ;(pretty-print CBBF)
  ;(display "\n")

  ;(display "A*\n")
  ;(pretty-print A*)
  ;(display "\n")
   
  ;(display "inspect::fluent->models")
  ;(display "\n")
  ;(pretty-print (time (inspect-fluent afluent)))
  ;(display "\n")

  ;(display "inspect::sat-unifluent")
  ;(display "\n")
  ;(pretty-print (time (inspect-sat (list afluent))))
  ;(display "\n")

  ;(display "inspect::sat-multifluent")
  ;(display "\n")
  ;(pretty-print (time (inspect-sat partitioned)))
  ;(display "\n")

  ;(display "inspect::satset-unifluent")
  ;(display "\n")
  ;(time (search-satset (list afluent)))
  ;(pretty-print (time (inspect-satset (list afluent))))
  ;(display "\n")

  ;(display "inspect::satset-multifluent")
  ;(display "\n")
  ;(time (search-satset (list afluent)))
  ;(pretty-print (time(inspect-satset (list afluent))))
  ;(display "\n")

  (define solver (inspect::fluent->models false var< legality))
  ;; A(2) B(1) C(5) D(5) E(4) F(6) G(5) H(6)
  ;; Best: (list 'E 'D 'F 'C 'H 'G 'A 'B)
  
  (solver (fluent (list 'E 'D 'F 'C 'H 'G 'A 'B)
                  (list 1 2 3 4)))

  )

