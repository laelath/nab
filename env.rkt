#lang racket
(provide lookup-env extend-env)

;; Env Variable -> Address
(define (lookup-env env x)
  (match env
    ['() 'err]
    [(cons (list y i) env)
     (match (symbol=? x y)
       [#t i]
       [#f (lookup-env env x)])]))

;; Env Variable Address -> Value
(define (extend-env r x i)
  (cons (list x i) r))
