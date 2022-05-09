#lang racket
(provide Delay lookup-box-in-sto extend-sto update-sto)

;; type Address = Integer
;; type Thunk = Value | (Delay Expr Env)
(struct Delay (expr env) #:prefab)

;; type Sto = (Listof (List Address (Boxof Thunk)))

;; Sto Address -> (Boxof Thunk)
(define (lookup-box-in-sto s l)
  (match s
    ['() 'err]
    [(cons (list m bt) s)
     (match (= l m)
       [#t bt]
       [#f (lookup-box-in-sto s l)])]))

;; Sto Address -> Thunk
(define (lookup-sto s l)
  (match (lookup-box-in-sto s l)
    ['err 'err]
    [bt (unbox bt)]))

;; Sto -> Address
(define (next-addr s)
  (match s
    ['() 0]
    [(cons (list l _) _) (add1 l)]))

;; Sto Thunk -> (Sto, Address)
;; Extends the given store and returns a pair of the extended store with the
;; new Address that was used to extend it.
(define (extend-sto s t)
  (let ([l (next-addr s)])
    (cons (cons (list l (box t)) s) l)))

;; Sto Address Thunk -> ()
(define (update-sto s l t)
  (match (lookup-box-in-sto s l)
    ['err 'err]
    [bt (set-box! bt t)]))