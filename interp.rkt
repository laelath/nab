#lang racket
(provide interp interp-env)
(require "ast.rkt"
         "env.rkt"
         "interp-prims.rkt"
         "sto.rkt"
         "do.rkt")

;; type Answer = Value | 'err

;; type Value =
;; | Integer
;; | Boolean
;; | Character
;; | Eof
;; | Void
;; | '()
;; | (cons Value Value)
;; | (box Value)
;; | (vector Value ...)
;; | (string Char ...)
;; | (Value ... -> Answer)
;; | (StructVal Symbol (Vectorof Val))

;; type Address = Integer
;; type REnv = (Listof (List Id Address))
;; type Sto = (Listof (List Address Thunk))
;; type Thunk = Value | (Delay Expr Env)
;; type Defns = (Listof Defn)

;; Sto Address Defns -> Answer
(define (lookup-sto s l ds)
  (match (lookup-box-in-sto s l)
    ['err 'err]
    [bt (match (unbox bt)
          [(Delay e r)
           ;; TODO: Verify this works correctly with recursion.
           (interp-env r s e ds)]
          [a a])]))

;; Prog -> Answer
(define (interp p)
  (match p
    [(Prog ds e)
     (match (interp-env '() '() e ds)
       [(cons a _) a]
       [e e])]))

;; FIXME: signature is incorrect now (return type a little different)
;; Env Sto Exp Defns -> ((Pairof Value Sto) | 'err)
(define-match-do (interp-env #:error-value 'err
                             #:env r #:sto s
                             #:matching e
                             ds)
  [(Quote d)
   ;; (! (displayln (format "Quote: ~a" d)))
   (return d)]
  [(Eof)
   ;; (! (displayln "Eof"))
   (return eof)]
  [(Var x)
   ;; (! (displayln (format "Var ~a" x)))
   (interp-var r s x ds)]
  [(Prim p es)
   ;; (! (displayln (format "Prim: ~a ~a" p es)))
   (vs <- (interp-env* r s es ds))
   ;; (! (displayln (format "  interp'ed vs: ~a" vs)))
   (return (interp-prim p vs))]
  [(If c e1 e2)
   ;; (! (displayln (format "If: ~a ~a ~a" c e1 e2)))
   (v <- (interp-env r s c ds))
   (if v
       (interp-env r s e1 ds)
       (interp-env r s e2 ds))]
  [(Begin e1 e2)
   ;; (! (displayln (format "Begin: ~a ~a" e1 e2)))
   (_ <- (interp-env r s e1 ds))
   (interp-env r s e2 ds)]
  [(Let x _ e1 e2)
   ;; (! (displayln (format "Let: ~a = ~a in ~a" x e1 e2)))
   ;; (! (displayln (format "  r: ~a" r)))
   ;; (! (displayln (format "  s: ~a" s)))
   ;; (! (displayln (format "  extend ~a with thunk" x)))
   (extend x (Delay e1 r))
   ;; (! (displayln (format "  r: ~a" r)))
   ;; (! (displayln (format "  s: ~a" s)))
   (interp-env r s e2 ds)]
  [(Lam _ xs e)
   ;; (! (displayln (format "Lam: ~a ~a" xs e)))
   ;; Allocate a bunch of empty boxes in the store and then use those locations
   ;; when the function is called.
   (new-allocated-locations := extend* xs (map (λ (_) (box #f)) xs))
   (original-r = r)
   (return
    (λ vs
      (if (= (length xs) (length vs))
          ;; May need to verify that this fold goes the correct direction.
          (let ([new-r (for/fold ([r original-r])
                                 ([xls (map cons xs new-allocated-locations)])
                         (match xls
                           [(cons x l)
                            (extend-env r x l)]))])
            (interp-env new-r s e ds))
          'err)))]
  [(App e _ es)
   ;; (! (displayln (format "App: ~a ~a" e es)))
   (f <- (interp-env r s e ds))
   (vs <- (interp-env* r s es ds))
   (return-if (procedure? f) (apply f vs))]
  [(Match e ps es)
   ;; (! (displayln (format "Match: ~a ~a ~a" e ps es)))
   (v <- (interp-env r s e ds))
   (interp-match r s v ps es ds)])

;; Env Sto Value [Listof Pat] [Listof Expr] Defns -> Answer
(define (interp-match r s v ps es ds)
  (match* (ps es)
    [('() '()) 'err]
    [((cons p ps) (cons e es))
     (match (interp-match-pat r s p v)
       [#f (interp-match r s v ps es ds)]
       [r  (interp-env r s e ds)])]))

;; Env Sto Pat Value -> [Maybe (Pairof Env Sto)]
(define-match-do (interp-match-pat #:error-value #f
                                   #:env r #:sto s
                                   #:matching p
                                   v)
  [(PWild) (return r)]
  [(PVar x) (extend x v)
            (return r)]
  [(PSymb s) (return-if (eq? s v) r)]
  [(PStr s) (return-if (and (string? v) (string=? s v)) r)]
  [(PLit l) (return-if (eqv? l v) r)]
  [(PBox p)
   ((box v) = v)
   (interp-match-pat r s p v)]
  [(PCons p1 p2)
   ((cons v1 v2) = v)
   (r <- (interp-match-pat r s p1 v1))
   (interp-match-pat r s p2 v2)]
  [(PAnd p1 p2)
   (r <- (interp-match-pat r s p1 v))
   (interp-match-pat r s p2 v)]
  [(PStruct t ps)
   ((StructVal n vs) = v)
   (return-if (eq? t n) (interp-match-pats r s ps (vector->list vs)))])

(define-match-do (interp-match-pats #:error-value #f
                                    #:env r #:sto s
                                    #:matching ps
                                    vs)
  ['() (return r)]
  [(cons p ps)
   ((cons v vs) = vs)
   (r <- (interp-match-pat r s p p v))
   (interp-match-pats r s ps vs)])

;; [Listof Pat] [Listof Val] Env -> [Maybe Env]
#;(define (interp-match-pats ps vs r s)
  (match ps
    ['() r]
    [(cons p ps)
     (match vs
       [(cons v vs)
        (match (interp-match-pat p v r s)
          [#f #f]
          [r1 (interp-match-pats ps vs r1)])])]))

;; Env Sto Id [Listof Defn] -> (Pairof Answer Sto)
(define (interp-var r s x ds)
  (match (lookup-env r x)
    ['err (match (defns-lookup ds x)
            [(Defn f xs e) (interp-env '() s (Lam f xs e) ds)]
            [#f 'err])]
    [l (lookup-sto s l ds)]))

;; Env Sto (Listof Expr) Defns -> (Pairof (Listof Value) Sto) | 'err
(define-match-do (interp-env* #:error-value 'err
                              #:env r #:sto s
                              #:matching es
                              ds)
  ['()
   ;; (! (displayln "interp-env*: empty input"))
   (return '())]
  [(cons e es)
   ;; (! (displayln (format "interp-env*: ~a and ~a" e es)))
   ;; (! (displayln (format "v <- (interp-env ~a ~a ~a ~a)" r s e ds)))
   (v <- (interp-env r s e ds))
   ;; (! (displayln (format "interp-env*: interp'ed v: ~a" v)))
   ;; (! (displayln (format "vs <- (interp-env ~a ~a ~a ~a)" r s es ds)))
   (vs <- (interp-env* r s es ds))
   ;; (! (displayln (format "interp-env*: interp'ed vs: ~a" vs)))
   (return (cons v vs))])

;; Defns Symbol -> [Maybe Defn]
(define (defns-lookup ds f)
  (findf (match-lambda [(Defn g _ _) (eq? f g)])
         ds))

(define (zip xs ys)
  (match* (xs ys)
    [('() '()) '()]
    [((cons x xs) (cons y ys))
     (cons (list x y)
           (zip xs ys))]))
