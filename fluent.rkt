#lang racket
(require "graph.rkt")
;; ===========================================================================
;; Interface:
(provide (struct-out fluent))
(provide fluent::tree laws->sat? vardeg)

;; ===========================================================================
;; Data wrapper:
;; vars  : (listof X)
;; vals  : (listof Y)
;; interp: each X 'takes' one Y as value
(struct fluent (vars vals) #:transparent)

;; ===========================================================================
;; f0         : fluent
;; pigeonvars : boolean := at-most-one-var-per-val?
;; loc : (list (quote <S-EXP>))
;; ---------->: fluent -> node
(define (fluent::tree f0 pigeonvars loc)
    (let ([flu (fluent (sort (fluent-vars f0)
                             (λ (v1 v2) (> (vardeg v1 loc)
                                           (vardeg v2 loc))))
                       (fluent-vals f0))])
      (::tree flu                                ; root-ctx  := ordered fluent
              empty                              ; root-data := empty model
              (λ (agg flu)                       ; termination condition
                (or (empty? (fluent-vars flu))
                    (empty? (fluent-vals flu))))
              (λ (agg flu) (fluent (rest (fluent-vars flu)) ; remove var
                                   (if (not pigeonvars)
                                       (fluent-vals flu)
                                       (filter-not 
                                        (λ (val) (equal? (cdr (first agg))
                                                         val))))))
              (λ (agg flu)                    
                (map (λ (val)                    ; extensions of part model 
                       (cons (cons (first (fluent-vars flu)) val)
                             agg))
                     (fluent-vals flu)))              
              (λ (agg) ((laws->sat? loc) agg)))))          ; legality check 

;; ==========================================================================
;; /Partially-saturated-satisfaction predicate factory/
;; loc : (list (quote <S-EXP>))
;; --->: (list (cons X Y)) -> boolean
(define (laws->sat? loc)
  (λ (agg)
    (local [(define (saturated? sexp)
              (and (not (empty? sexp))
                   (or (and (= 1 (length sexp))
                            (not (false? (assoc (eval (first sexp)) agg))))
                       (andmap (λ (id) (not (false? (assoc (eval id) agg))))
                               (rest sexp)))))

            (define (sub-eval saturated)
                (map (λ (sexp)
                     (if (= 1 (length sexp))
                         (cdr (assoc (eval (first sexp)) agg))
                         (eval (cons (first sexp)
                                     (map (λ (id) (cdr (assoc (eval id) agg)))
                                          (rest sexp))))))
                     saturated))]
      
      (foldr (λ (c nxt) (and c nxt))
             true
             (sub-eval (filter saturated? loc))))))

;; ==========================================================================
;; Measure of involvement of variable in constraints
;; loc : (list (quote <S-EXP>))
;; --->: X -> natural
(define (vardeg var loc) (count (λ (c) (member `',var c)) loc))

;; ==========================================================================
;; Constraint Sat Sample:

(define FLU (fluent (list 'T 'F 'A 'B 'C 'D)
                    (list #t #f)))

(define CON (list '('T)         ; 0-ary (atoms) wrapped in list
                  '(not 'F)    
                  '(or  'A 'B) 
                  '((λ (x y) (not (and x y))) 'A 'B) 
                  '(or  'C 'D)  ; not saturated => not evaluated
                  '((λ (x y z) (not (and x y z))) 'A 'B 'C)))
                            
(define AGG (list (cons 'T #t)
                  (cons 'F #f)
                  (cons 'A #t)
                  (cons 'B #f)
                  (cons 'C #t)))

;; (vardeg 'A CON) ; = 3
;; (fluent::tree FLU false '()) ;node := root of tree w/ 2^6 leaves
;; ((laws->sat? CON) AGG) ;boolean := #f, unless sub #f for #t in (cons 'C #t)
;; (fluent::tree FLU false CON) ;node := root of satisfiable-extension tree
;; ==========================================================================



