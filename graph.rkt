#lang racket
;; ===========================================================================
;; Interface

(provide (struct-out node))  

(provide ::tree)
(provide cost::sum)
(provide path<::ith path<::cost path<::h path<::a*)
(provide path<::tie path<::dfs path<::bfs) 
(provide prune-nothing prune-cycles prune-extension-joins prune-frontier-joins)


;; ===========================================================================
;; Directed graph node:
;; (node X Y (listof node))
;; (equal? <node> <node>) :: (equal? X X)
(struct node (id data arcs)
  #:methods
  gen:equal+hash
  ;; Simple hashing scheme.
  ;; Note: requires unique identifiers for nodes.
  ;; At least three options for "anonymous" nodes:
  ;;   i) let id := `(,data) 
  ;;  ii) let id := `(,arcs) 
  ;; iii) let id := `(,(cons data arcs))
  [(define (equal-proc a b recur)
     (equal? (node-id a) (node-id b)))
   (define (hash-proc a recur)
     (equal-hash-code (node-id a)))
   (define (hash2-proc a recur)
     (equal-secondary-hash-code (node-id a)))])

;; ===========================================================================
;; Tree generator:
;; root-ctx  :  Y
;; root-data :  X
;; terminal? : (X Y) -> boolean
;; nexts     : (X Y) -> (list X)
;; reduce    : (X Y) -> Y
;; legal?    : (cons X Y) -> boolean
;;---------->: node
(define (::tree root-ctx root-data terminal? reduce nexts legal?)
  (local [(define (recur-deep ctx data)
            (if (terminal? data ctx)
                (node `(,data) data empty)
                (node `(,data)
                      data
                      (recur-wide (reduce data ctx)
                                  (nexts  data ctx)))))
          (define (recur-wide ctx lodata)
              (cond [(empty? lodata) empty]
                    [(legal? (cons (first lodata) ctx))
                     (cons (recur-deep ctx (first lodata))
                           (recur-wide ctx (rest  lodata)))]
                    [else  (recur-wide ctx (rest  lodata))]))]
    (recur-deep root-ctx root-data)))

;; ===========================================================================
;; Factories:
;; costfn : (cons node node) -> number
;; ------>: (list node) -> number
(define (cost::sum costfn)
  ;; d : (list node) w/ (first d) the last visited 
  (λ (d)
    (local [(define (recsum p)
              (cond [(empty? p) -inf.0] ; cost of empty path
                     [(empty? (rest p)) 0] ; singleton is base
                     [(null? (costfn (cons (first p) (second p)))) +inf.0]
                     [else (+ (costfn (cons (first p) (second p)))
                              (recsum (rest p)))]))]
      (recsum (reverse d)))))

;; Start->end ith node comparator
;; node-rel: (node node) -> boolean
;; ------->: ((list node) (list node)) -> boolean
(define (path<::ith node-rel)
  (λ (d1 d2)
    (local [(define (breaker p1 p2)
              (cond [(empty? p1) (not (empty? p2))]
                     [(empty? p2) false]
                     [else (or (node-rel (first p1) (first p2)))
                           (and (equal? (first p1) (first p2))
                                (breaker (rest p1) (rest p2)))]))]
      (breaker (reverse d1) (reverse d2)))))
                  
;; Least-cost comparator
;; costfn: (cons node node) -> boolean
;; ----->: ((list node) (list node)) -> boolean
(define (path<::cost costfn)
  (let ([pathcostfn (cost::sum costfn)]) 
    (λ (d nxt) (or (< (pathcostfn d) (pathcostfn nxt))
                        (and (= (pathcostfn d) (pathcostfn nxt))
                             (path<::tie d nxt))))))

;; Heuristic comparator
;; h : node -> number
;; ----->: ((list node) (list node)) -> boolean
(define (path<::h heur)
  (λ (d nxt)
      (or (< (heur (first d)) (heur (first nxt)))
          (and (= (heur (first d)) (heur (first nxt)))
               (path<::tie d nxt)))))

;; A* comparator
;; h      : node -> number
;; costfn : (cons node node) -> number
;; ----->: ((list node) (list node)) -> boolean
(define (path<::a* h costfn) 
  (λ (d nxt)
    (let ([weight (λ (x) (+ (h (first x)) ((cost::sum costfn) x)))])
      (or (< (weight d) (weight nxt))
          (and (= (weight d) (weight nxt))
               (path<::tie d nxt))))))

;; ===========================================================================
;; Predefineds.

;; Tiebreaker, defaults to:
;; - false for type-clash
;; - defer to built-in ordering if node ids are primitives
;; - recursively deepen comparison for (partial) ties
;; ((list node) (list node)) -> boolean
(define (path<::tie d1 d2)
    (local [(define (breaker p1 p2)
              (let ([i1 (if (empty? p1) null (node-id (first p1)))]
                    [i2 (if (empty? p2) null (node-id (first p2)))])
                (cond [(null? i1) (not (null? i2))]
                      [(null? i2) false]
                      [(and (number? i1) (number? i2))
                       (or (< i1 i2)
                           (and (= i1 i2)
                                (breaker (rest p1) (rest p2))))]
                      [(and (symbol? i1) (symbol? i2))
                       (or (symbol<? i1 i2)
                           (and (equal? i1 i2)
                                (breaker (rest p1) (rest p2))))]
                      [(and (string? i1) (string? i2))
                       (or (string<? i1 i2)
                           (and (equal? i1 i2)
                                (breaker (rest p1) (rest p2))))]
                      [(and (list? i1) (list? i2)) (< (length i1)
                                                      (length i2))]                     
                      [else false])))]
      (breaker (reverse d1) (reverse d2))))

;; ((list node) (list node)) -> boolean
(define path<::dfs (λ (d nxt) (or (> (length d) (length nxt))     
                                   (and (= (length d) (length nxt))
                                        (path<::tie d nxt)))))

;; ((list node) (list node)) -> boolean
(define path<::bfs (λ (d nxt) (or (< (length d) (length nxt))     
                                   (and (= (length d) (length nxt))
                                        (path<::tie d nxt)))))

;; ((list node) (list node)) -> (list node)
(define (prune-nothing exts frnt) (append exts frnt))

;; ((list node) (list node)) -> (list node)
(define (prune-cycles exts frnt)
  (append (filter (λ (d) (not (member (first d) (rest d)))) exts)
          frnt))

;; ((list node) (list node)) -> (list node)
(define (prune-frontier-joins exts frnt)
  (append exts
          (filter (λ (fd)
                    (andmap (λ (ed)
                              (not (equal? (first ed) (first fd))))
                            exts))
                  frnt)))

;; ((list node) (list node)) -> (list node)
(define (prune-extension-joins exts frnt)
  (append (filter (λ (ed)
                    (andmap (λ (fd)
                              (not (equal? (first fd) (first ed))))
                            frnt))
                  exts)
          frnt))


