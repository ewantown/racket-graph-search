#lang racket
(require "graph.rkt")
;; ===========================================================================
;; Interface:
(provide (struct-out fluent))
(provide fluent::->tree fluent::->models)

;; ===========================================================================
;; Data wrapper:
;; vars  : (listof X)
;; vals  : (listof Y)
;; interp: each X 'takes' one Y as value
(struct fluent (vars vals) #:transparent)

;; ===========================================================================
;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : ((cons X Y) (list (cons X Y))) -> boolean
;; ---------->: fluent -> node
(define (fluent::->tree pigeonvars var< legal?)
  (lambda (f0) ; returned procedure takes fluent as arg
    (local [; Initial fluent with specified var ordering
            (define flnt
              (fluent (sort (fluent-vars f0) var<) (fluent-vals f0)))
            ; Builds the tree vertically (by selecting a var)
            (define (recur-deep agg flu)
              ; Note: agg is a list of (var . val) pairs (partial model)
              (if (or (empty? (fluent-vars flu))
                      (empty? (fluent-vals flu)))
                  ; Terminal node if fluent is out of vars/vals
                  (node `(,agg) agg empty)
                  ; else make a node w/ recursively generated subs (arcs)
                  (node `(,agg) 
                        agg
                        (recur-wide (map (lambda (val)
                                           ; Pass all assignments to first var
                                           (cons (first (fluent-vars flu)) val))
                                         (fluent-vals flu))
                                    agg
                                    ; Pass the rest of the vars
                                    (fluent (rest (fluent-vars flu))
                                            (fluent-vals flu))))))
            ; Builds tree horizontally (generates heads of outgoing arcs of node)
            (define (recur-wide lop agg flu)
              (cond [(empty? lop) empty] ; base of self-recurrence
                    ; If first assignment is consistent w/ model...
                    [(legal? (first lop) agg)
                     (local [; (just for "pigeonhole-ing")
                             (define val (cdr (first lop)))
                             (define vals- (filter (lambda (v)
                                                     (not (equal? v val)))
                                                   (fluent-vals flu)))]
                       ; ... add branch for first assign, "all the way down"...
                       (cons (recur-deep (cons (first lop) agg)
                                         (if pigeonvars
                                             (fluent (fluent-vars flu)
                                                     vals-)
                                             flu))
                             ;... to list of branches for all assigns.
                             (recur-wide (rest lop) agg flu)))]
                    ; Else just add branches for alternative assigns.
                    [else (recur-wide (rest lop) agg flu)]))]
      ; Initiate mutual recursion w/ empty partial model, initial fluent.
      (recur-deep empty flnt))))


;; pigeonvars : boolean := at-most-one-var-per-val?
;; var<       : (X X) -> boolean
;; legal?     : ((cons X Y) (list (cons X Y))) -> boolean
;; path<      : ((list node) (list node)) -> boolean
;; admit?     : (list (cons X Y)) -> boolean
;; ---------->: fluent -> (list (list (cons X Y)))
(define (fluent::->models pigeonvars var< legal?)
  (lambda (f0)
    (local [(define root ((fluent::->tree pigeonvars var< legal?) f0))
            ; Note, pruning is done during construction by fluent::->tree.
            (define (goal? n)
              ; True iff "full model" (all vars of init. fluent get vals)
              (and (empty? (node-arcs n))
                   (= (length (node-data n)) (length (fluent-vars f0)))))
            ; DFS procedure tailored to fluent-trees
            (define (probe frnt acc) ; frnt:= "frontier", acc:= "accumulator"
              (if (empty? frnt)
                  (reverse acc)
                  (let ([path (first frnt)]) ; Pull partial path off frontier...
                    (if (goal? (first path)) ; ...if it's a full model...
                        (probe (rest frnt)   ; add it to the list, probe onward.
                               (cons (reverse (node-data (first (first frnt))))
                                     acc))
                        (let ([reduct ; Else, update the frontier...
                               ; i.e. minus paths to here, plus all extensions
                               (filter (lambda (alt)
                                         (not (equal? (first alt) (first path))))
                                       (append (map (lambda (n) (cons n path))
                                                    (node-arcs (first path)))
                                               frnt))])
                          ; ... then probe onward.
                          (probe (sort reduct path<::dfs) acc))))))]
      ;; Initialize search with root of generated tree.
      (probe (list (list root)) empty))))
