#lang racket
(require "ast.rkt")
(provide lambdas)

;; Prog -> [Listof Lam]
;; List all of the lambda expressions in p
(define (lambdas p)
  (match p
    [(Prog ds e)
     (append (lambdas-ds ds) (lambdas-e e))]))

;; Defns -> [Listof Lam]
;; List all of the lambda expressions in ds
(define (lambdas-ds ds)
  (match ds
    ['() '()]
    [(cons (Defn f xs e) ds)
     (append (lambdas-e e)
             (lambdas-ds ds))]))

;; Expr -> [Listof Lam]
;; List all of the lambda expressions in e
(define (lambdas-e e)
  (match e
    [(Prim p es)        (append-map lambdas-e es)]
    [(If e1 e2 e3)      (append (lambdas-e e1) (lambdas-e e2) (lambdas-e e3))]
    [(Begin e1 e2)      (append (lambdas-e e1) (lambdas-e e2))]
    [(Let x e1 e2)      (append (lambdas-e e1) (lambdas-e e2))]
    [(App e1 fs es)     (append (lambdas-e e1) (append-map lambdas-e es))] ;; TODO: maybe treat thunks as lambdas? (we do have zero arg lambdas after all...)
    [(Lam f xs e1)      (cons e (lambdas-e e1))]
    [(Match e ps es)    (append (lambdas-e e) (append-map lambdas-e es))]
    [_                  '()]))
