#lang racket

(require "debug.rkt")

(provide lookup-env extend-env)

;; Env Variable -> Address
(define (lookup-env env x)
  (displayln-debug "lookup-env")
  (displayln-debug (format "  env: ~a" env))
  (displayln-debug (format "  var: ~a" x))
  (match env
    ['() (begin (displayln-debug "  failed to match") 'err)]
    [(cons (list y i) env)
     (match (symbol=? x y)
       [#t (begin (displayln-debug "  matched") i)]
       [#f (begin (displayln-debug "  continuing...") (lookup-env env x))])]))

;; Env Variable Address -> Env
(define (extend-env r x l)
  (cons (list x l) r))
