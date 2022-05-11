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
;; Also gets the expressions that need to be thunked
(define (lambdas-e e)
  (match e
    [(Prim p es)        (append-map lambdas-e es)]
    [(DCons dc fs es)   (append (thunk-lambdas fs es) (append-map lambdas-e es))]
    [(If e1 e2 e3)      (append (lambdas-e e1) (lambdas-e e2) (lambdas-e e3))]
    [(Begin e1 e2)      (append (lambdas-e e1) (lambdas-e e2))]
    [(Let x f e1 e2)    (append (thunk-lambdas (list f) (list e1)) (append (lambdas-e e1) (lambdas-e e2)))]
    [(Letrec x f e1 e2) (append (thunk-lambdas (list f) (list e1)) (append (lambdas-e e1) (lambdas-e e2)))]
    [(App e1 fs es)     (append (thunk-lambdas fs es) (lambdas-e e1) (append-map lambdas-e es))]
    [(Lam f xs e1)      (cons e (lambdas-e e1))]
    [(Match f e ps es)  (append (thunk-lambdas (list f) (list e)) (append (lambdas-e e) (append-map lambdas-e es)))]
    [_                  '()]))

(define (thunk-lambdas fs es)
  (match* (fs es)
    [('() '()) '()]
    [((cons f fs) (cons e es))
     (match e
       [(or (Var _) (Quote _)) (thunk-lambdas fs es)]
       [_ (cons (Lam f '() e) (thunk-lambdas fs es))])]))
    
