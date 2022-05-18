#lang racket
(provide interp interp-env)
(require "ast.rkt"
         "debug.rkt"
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

;; Sto Address Defns -> (Pairof Value Sto) | 'err
(define (lookup-sto s l ds)
  ;; FIXME: Remove mutation.
  (displayln-debug "lookup-sto")
  (displayln-debug (format "lookup-sto: sto: ~a" s))
  (displayln-debug (format "lookup-sto: addr: ~a" l))
  (match (lookup-box-in-sto s l)
    ['err (begin (displayln-debug "lookup-sto: no match") 'err)]
    [bt (begin (displayln-debug "lookup-sto: match found")
               (match (unbox bt)
                 [(Delay e r)
                  ;; TODO: Verify this works correctly with recursion.
                  (displayln-debug "  lookup-sto: found Delay")
                  (match (interp-env r s e ds)
                    [(cons v s)
                     (displayln-debug (format "  lookup-sto: evaluated delayed term: ~a" v))
                     (update-sto! s l v)
                     (displayln-debug "  lookup-sto: updated store:")
                     (displayln-debug (format "    l: ~a" l))
                     (displayln-debug (format "    v: ~a" v))
                     (displayln-debug (format "    s: ~a" s))
                     (cons v s)]
                    [_ 'err])]
                 [a
                  (displayln-debug (format "    found value: ~a" a))
                  (cons a s)]))]))

;; Prog -> Value | 'err
(define (interp p)
  (match p
    [(Prog ds e)
     (displayln-debug (format "PROG USING DEFNS: ~a" ds))
     (match (interp-env '() '() e ds)
       [(cons a s)
        (displayln-debug "PROG RETURNED WITH CONS:")
        (displayln-debug (format "    (cons ~a" a))
        (displayln-debug (format "          ~a)" s))
        a]
       [e
        (displayln-debug "PROG RETURNED WITH NON-CONS")
        e])]))

;; Env Sto Exp Defns -> (Pairof Value Sto) | 'err
(define-match-do (interp-env #:error-value 'err
                             #:env r #:sto s
                             #:matching e
                             ds)
  [(Quote d)
   (! (displayln-debug (format "**  Quote: ~a" d)))
   (return d)]
  [(Eof)
   (! (displayln-debug "**  Eof"))
   (return eof)]
  [(Var x)
   (! (displayln-debug (format "**  Var: ~a" x)))
   (interp-var r s x ds)]
  [(Prim p es)
   ;; FIXME: Intercept location-sensitive primitives.
   (! (displayln-debug (format "**  Prim: ~a ~a" p es)))
   (vs <- (interp-env* r s es ds))
   (interp-special-prims r s p vs ds)
   #;(! (displayln-debug (format "    Prim arguments: ~a" vs)))
   #;(! (displayln-debug (format "    env: ~a" r)))
   #;(! (displayln-debug (format "    sto: ~a" s)))
   #;(result = (interp-prim p vs))
   #;(! (displayln-debug (format "    Prim result: ~a" result)))
   #;(return result)]
  [(DCons c _ es)
   (! (displayln-debug (format "**  DCons: ~a ~a" c es)))
   (interp-dcons r s c es ds)]
  [(If c e1 e2)
   (! (displayln-debug "**  If"))
   (v <- (interp-env r s c ds))
   (if v
       ((interp-env r s e1 ds))
       ((interp-env r s e2 ds)))]
  [(Begin e1 e2)
   (! (displayln-debug "**  Begin"))
   (_ <- (interp-env r s e1 ds))
   (interp-env r s e2 ds)]
  [(Let x _ e1 e2)
   (! (displayln-debug "**  Let"))
   (extend x (Delay e1 r))
   (interp-env r s e2 ds)]
  [(Lam _ xs e)
   (! (displayln-debug "**  Lam"))
   (return
    (λ (s)
      (displayln-debug "(accepted store in lambda)")
      (λ vs
        (displayln-debug "(accepted values in lambda)")
        (if (= (length xs) (length vs))
            (let-values ([(r s) (for/fold ([r r] [s s])
                                          ([xv (map cons xs vs)])
                                  (match-let* ([(cons x v) xv]
                                               [(cons s l) (extend-sto s v)]
                                               [r (extend-env r x l)])
                                    (displayln-debug (format "  inside lambda: extended env with: (~a, ~a)" x l))
                                    (displayln-debug (format "  inside lambda: extended sto with: (~a, ~a)" l v))
                                    (values r s)))])
              (displayln-debug (format "  inside lambda: completed env: ~a" r))
              (displayln-debug (format "  inside lambda: completed sto: ~a" s))
              (interp-env r s e ds))
            'err))))]
  [(App e _ es)
   (! (displayln-debug "**  App"))
   (f <- (interp-env r s e ds))
   (! (displayln-debug (format "    App: applying f: ~a" f)))
   (! (displayln-debug (format "    App: (procedure? f): ~a" (procedure? f))))
   (ts = (map (λ (v) (Delay v r)) es))
   (! (displayln-debug (format "    App: delayed arguments: ~a" ts)))
   (if (procedure? f)
       ((! (displayln-debug "    App: performing application..."))
        (result <- (apply (f s) ts))
        (! (displayln-debug (format "    App: got result: ~a" result)))
        (return result))
       ((return-error)))
   #;(return-if (procedure? f) (apply f es))]
  [(Match _ e ps es)
   (! (displayln-debug "**  Match"))
   (v <- (interp-env r s e ds))
   (interp-match r s v ps es ds)]
  [_
   (! (displayln-debug (format "error: received unknown input: ~a" e)))
   'err])

;; Env Sto (Op | DC) (Listof Value) Defns -> (Pairof Value Sto) | 'err
(define-match-do (interp-special-prims #:error-value 'err
                                       #:env r #:sto s
                                       #:matching p
                                       vs ds)
  ['struct-ref
   ((list accessed-name index (StructVal actual-name vs)) = vs)
   (if (and (eq? accessed-name actual-name) (<= 0 index (sub1 (vector-length vs))))
       ((l = (vector-ref vs index))
        (lookup-sto s l ds))
       ((return-error)))]
  [_ (return (interp-prim p vs))])

;; Env Sto DC (Listof Expr) Defns -> (Pairof Value Sto) | 'err
(define-match-do (interp-dcons #:error-value 'err
                               #:env r #:sto s
                               #:matching dc
                               es ds)
  ['make-struct
   (! (displayln-debug (format "  interp-dcons: (make-struct ~a)" es)))
   ;; (make-struct name args ...)
   ;;
   ;; Evaluate the first argument. It ought to be a symbol naming the kind of
   ;; struct to create. The other arguments should be delayed and placed in the
   ;; store, with their locations written to a vector that is wrapped in a
   ;; StructVal along with the name.
   ((cons e es) = es)
   (name <- (interp-env r s e ds))
   (! (displayln-debug (format "    make-struct: name: ~a" name)))
   (! (displayln-debug (format "    make-struct: env: ~a" r)))
   (! (displayln-debug (format "    make-struct: sto: ~a" s)))
   ((cons s ls) = (for/fold ([s s]
                             [ls '()]
                             #:result (begin
                                        (displayln-debug "    make-struct: connecting result")
                                        (cons s (reverse ls))))
                            ([e es])
                    (begin
                      (displayln-debug (format "      make-struct: s: ~a" s))
                      (displayln-debug (format "      make-struct: ls: ~a" ls))
                      (displayln-debug (format "      make-struct: e: ~a" e))
                      (match (extend-sto s (Delay e r))
                        [(cons s l)
                         (values s (cons l ls))]))))
   (! (displayln-debug (format "    make-struct: store extended: ~a" s)))
   (! (displayln-debug (format "    make-struct: locations added: ~a" ls)))
   (vec = (list->vector ls))
   (! (displayln-debug (format "    make-struct: vector allocated: ~a" vec)))
   (strct = (StructVal name vec))
   (! (displayln-debug (format "    make-struct: StructVal constructed: ~a" strct)))
   (return strct)]
  #;['make-vector
   ;; (make-vector length init)
   ;;
   ;; Evaluate the first argument. It ought to be an integer dictating the
   ;; length of the vector to create. The other argument is an initial value
   ;; with which to fill all the slots in the vector. However, evaluation of
   ;; this value is delayed until needed, so thunks are allocated for each
   ;; position in the vector. The vector itself contains locations rather than
   ;; values, and the values live in the store.
   ((list e1 e2) = es)
   (v1 <- (interp-env r s e1 ds))
   (if (integer? v1)
       (((cons s ls) = (for/fold ([s s]
                                  [ls '()]
                                  #:result (cons s (reverse ls)))
                                 ([e (build-list v1 (λ (_) (Delay e2 r)))])
                         (match (extend-sto s e)
                           [(cons s l)
                            (values s (cons l ls))])))
        (vec = (list->vector ls))
        (return vec))
       ((return-error)))]
  [_
   ;; Any other DCons is passed through to interp-prim.
   (! (displayln-debug (format "  interp-dcons: ~a" dc)))
   (vs <- (interp-env* r s es ds))
   ;; FIXME: Check this is correct. Call interp-special-prims?
   (return (interp-prim dc vs))])

;; Env Sto Value (Listof Pat) (Listof Expr) Defns -> (Pairof Value Sto) | 'err
(define (interp-match r s v ps es ds)
  (match* (ps es)
    [('() '()) 'err]
    [((cons p ps) (cons e es))
     (match (interp-match-pat r s p v ds)
       [#f (interp-match r s v ps es ds)]
       [(cons r s)  (interp-env r s e ds)])]))

;; Env Sto Pat Value -> Maybe (Pairof Env Sto)
(define-match-do (interp-match-pat #:error-value #f
                                   #:env r #:sto s
                                   #:matching p
                                   v ds)
  [(PWild) (return r)]
  [(PVar x)
   (! (displayln-debug (format "$$ PVar ~a" x)))
   (if (Address? v)
       ((! (displayln-debug (format "     found Address: ~a" v)))
        (v <- (lookup-sto s v ds))
        (extend x v)
        (return r))
       ((! (displayln-debug (format "     did not find address: ~a" v)))
        (extend x v)
        (return r)))]
  [(PSymb sym) (return-if (eq? sym v) r)]
  [(PStr str) (return-if (and (string? v) (string=? str v)) r)]
  [(PLit l) (return-if (eqv? l v) r)]
  [(PBox p)
   ((box v) = v)
   (interp-match-pat r s p v ds)]
  [(PCons p1 p2)
   ((cons v1 v2) = v)
   (r <- (interp-match-pat r s p1 v1 ds))
   (interp-match-pat r s p2 v2 ds)]
  [(PAnd p1 p2)
   (r <- (interp-match-pat r s p1 v ds))
   (interp-match-pat r s p2 v ds)]
  [(PStruct t ps)
   (! (displayln-debug "$$ PStruct"))
   (! (displayln-debug (format "     v: ~a" v)))
   ((StructVal n vs) = v)
   (! (displayln-debug (format "     deconstructed v as (StructVal ~a ~a)" n vs)))
   (if (eq? t n)
       ((! (displayln-debug "     matched struct type"))
        (interp-match-pats r s ps (vector->list vs) ds))
       ((! (displayln-debug "     failed to match struct type"))
        (return-error)))])

;; Env Sto (Listof Pat) (Listof Value) -> Maybe (Pairof Env Sto)
(define-match-do (interp-match-pats #:error-value #f
                                    #:env r #:sto s
                                    #:matching ps
                                    vs ds)
  ['() (return r)]
  [(cons p ps)
   ((cons v vs) = vs)
   (r <- (interp-match-pat r s p v ds))
   (interp-match-pats r s ps vs ds)])

;; Env Sto Id Defns -> (Pairof Value Sto) | 'err
(define (interp-var r s x ds)
  (displayln-debug "interp-var")
  (displayln-debug (format "  env: ~a" r))
  (displayln-debug (format "  sto: ~a" s))
  (displayln-debug (format "  var: ~a" x))
  (displayln-debug (format "  defns: ~a" ds))
  (match-do
   #:error-value 'err #:env r #:sto s
   (lookup-env r x)
   ['err (! (displayln-debug (format "  lookup-env failed")))
         ((Defn f xs e) = (defns-lookup ds x))
         (! (displayln-debug (format "  building lambda as (Lam ~a ~a ~a)" f xs e)))
         (interp-env '() s (Lam f xs e) ds)]
   [l    (! (displayln-debug (format "  matched address ~a" l)))
         (result <- (lookup-sto s l ds))
         ;; (result = (lookup-sto s l ds))
         (! (displayln-debug (format "  found result: ~a" result)))
         (return result)]))

;; Env Sto (Listof Expr) Defns -> (Pairof (Listof Value) Sto) | 'err
(define-match-do (interp-env* #:error-value 'err
                              #:env r #:sto s
                              #:matching es
                              ds)
  ['() (return '())]
  [(cons e es)
   (v <- (interp-env r s e ds))
   (vs <- (interp-env* r s es ds))
   (return (cons v vs))])

;; Defns Symbol -> [Maybe Defn]
(define (defns-lookup ds f)
  (displayln-debug (format "defns-lookup for: ~a" f))
  (let ([result (findf (match-lambda [(Defn g _ _) (eq? f g)])
                       ds)])
    (displayln-debug (format "  result: ~a" result))
    result))

#;(define (zip xs ys)
  (match* (xs ys)
    [('() '()) '()]
    [((cons x xs) (cons y ys))
     (cons (list x y)
           (zip xs ys))]))
