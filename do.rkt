#lang racket

(require "debug.rkt"
         "env.rkt"
         "sto.rkt")
(require (for-syntax syntax/parse
                     racket/match))
(provide (all-defined-out))

;; The do-block creates a code block where an environment and store are threaded
;; along throughout the program, similar to a state-carrying monadic do
;; environment. It's a bit cursed, but it makes implementations involving the
;; environment and store a lot easier to write.
;;
;; The do-block requires three parameters:
;;
;;     #:error-value errv          This is an error-propagating state monad, so
;;                                     this parameter describes the kind of
;;                                     errors we are using. Some examples might
;;                                     be ['err] or [#f].
;;
;;     #:env r                     The current environment.
;;
;;     #:sto s                     The current store.
;;
;; These are the forms allowed inside the do-block:
;;
;; (! e) d ...+                    Executes [e] and discards the result. Then,
;;                                     proceeds with [d ...]. (Useful for
;;                                     printing.)
;;
;; (v <- e) d ...+                 Executes [e]. If the result is ['err], the
;;                                     ['err] is returned and execution stops
;;                                     (no additional [d ...] are evaluated). If
;;                                     the result of [e] is not ['err], the
;;                                     result is bound to [v] and evaluation
;;                                     proceeds with [d ...].
;;
;; (p = e) d ...+                  Binds the pattern [p] to the expression [e],
;;                                     then proceeds with [d ...].
;;
;; (ls := extend* xs vs) d ...+    Extends the environment and store to map the
;;                                     variables [xs] to the values [vs], and
;;                                     binds the new locations to [ls]. Then,
;;                                     proceeds with [d ...].
;;
;; (extend* xs vs) d ...+          Extends the environment and store to map the
;;                                     variables [xs] to the values [vs]. Then,
;;                                     proceeds with [d ...].
;;
;; (l := extend x v) d ...+        Extends the environment and store to map the
;;                                     variable [x] to the value [v], and binds
;;                                     the new location to [l]. Then, proceeds
;;                                     with [d ...].
;;
;; (extend x v) d ...+             Extends the environment and store to map the
;;                                     variable [x] to the value [v]. Then,
;;                                     proceeds with [d ...].
;;
;; (if c (e1s ...+) (e2s ...+))    Evaluates the conditional expression [c]. If
;;                                     it is true, evaluates [e1s ...].
;;                                     Otherwise, evaluates [e2s ...].
;;
;; (return v:id)                   Returns a pair of the identifier [v] with the
;;                                     current store [s].
;;
;; (return e)                      Returns the result of evaluating [e].
;;
;; (return-if c v:id)              Evaluates the conditional expression [c]. If
;;                                     it is true, returns a pair of the
;;                                     identifier [v] with the current store
;;                                     [s]. Otherwise, returns ['err].
;;
;; (return-if c e)                 Evaluates the conditional expression [c]. If
;;                                     it is true, returns the result of
;;                                     evaluating [e]. Otherwise returns ['err].
;;
;; (return-error)                  Returns the [error-value].
;;
;; e                               Evaluates the expression [e], returning the
;;                                     result.
(define-syntax (do-block stx)
  (syntax-parse stx
    #:datum-literals (! <- = := extend extend* return return-if)
    ;; (! e) d ...+
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (! expr) exps ...+)
     #'(begin expr (do-block #:error-value errv #:env r #:sto s exps ...))]
    ;; (v <- e) d ...+
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (v <- expr) exps ...+)
     #'(match expr
         [errv
          (displayln-debug "    <- assignment matched errv")
          errv]
         [(cons v s)
          (displayln-debug "    <- assignment matched cons")
          (do-block #:error-value errv #:env r #:sto s exps ...)]
         [_
          (displayln-debug (format "    <- assignment matched nothing: ~a" expr))
          errv])]
    ;; (x = e) d ...+
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (p = expr) exps ...+)
     #'(match expr
         [errv
          (displayln-debug "    = assignment matched errv")
          errv]
         [p
          (displayln-debug "    = assignment matched pattern")
          (do-block #:error-value errv #:env r #:sto s exps ...)]
         [_
          (displayln-debug (format "    = assignment matched nothing: ~a" expr))
          errv])]
    ;; (ls := extend* xs vs) d ...+
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (new-allocated-locations := extend* xs vs) exps ...+)
     #'(begin
         (displayln-debug "%% extend*")
         (displayln-debug (format "%%   xs: ~a" xs))
         (displayln-debug (format "%%   vs: ~a" vs))
         (let-values ([(r s ls) (for/fold ([r r] [s s] [ls '()])
                                          ([xvs (map cons xs vs)])
                                  (displayln-debug (format "%%     r: ~a" r))
                                  (displayln-debug (format "%%     s: ~a" s))
                                  (displayln-debug (format "%%     ls: ~a" ls))
                                  (match xvs
                                    [(cons x v)
                                     (match (extend-sto s v)
                                       [(cons s l)
                                        (let ([r (extend-env r x l)])
                                          (values r s (cons l ls)))])]))])
           (displayln-debug "%%   concluded loop")
           (displayln-debug (format "%%   r: ~a" r))
           (displayln-debug (format "%%   s: ~a" s))
           (displayln-debug (format "%%   ls: ~a" ls))
           (match-let ([new-allocated-locations ls])
             (do-block #:error-value errv #:env r #:sto s exps ...))))]
    ;; (extend* xs vs) d ...+
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (extend* xs vs) exps ...+)
     #'(do-block #:error-value errv #:env r #:sto s (_ := extend* xs vs) exps ...)]
    ;; (l := extend x v) d ...+
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (new-allocated-location := extend x v) exps ...+)
     #'(do-block #:error-value errv #:env r #:sto s ((cons new-allocated-location _) := extend* (list x) (list v)) exps ...)]
    ;; (extend x v) d ...+
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (extend x v) exps ...+)
     #'(do-block #:error-value errv #:env r #:sto s (extend* (list x) (list v)) exps ...)]
    ;; (if c (e1s ...+) (e2s ...+))
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        ((~datum if) c (e1s ...+) (e2s ...+)))
     #'(if c
           (do-block #:error-value errv #:env r #:sto s e1s ...)
           (do-block #:error-value errv #:env r #:sto s e2s ...))]
    ;; (return v:id)
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (return v:id))
     #'(cons v s)]
    ;; (return e)
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (return e:expr))
     #'(cons e s)]
    ;; (return-if c v:id)
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (return-if c v:id))
     #'(if c (cons v s) errv)]
    ;; (return-if c e)
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (return-if c e:expr))
     #'(if c
           (do-block #:error-value errv #:env r #:sto s (return e))
           errv)]
    ;; (return-error)
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        (return-error))
     #'errv]
    ;; e
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s) expr)
     #'expr]))

(define-syntax (match-do stx)
  (syntax-parse stx
    [(_ (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s)
        expr [pat body ...+] ...+)
     #'(match expr
         [pat (do-block #:error-value errv #:env r #:sto s body ...)] ...)]))

(define-syntax (define-match-do stx)
  (syntax-parse stx
    ;; [(_ (name:id left ...+ (~seq #:error-value errv) right ...) clauses ...+)
    ;;  #'(define-match-do (name #:error-value errv left ... right ...) clauses ...)]
    ;; [(_ (name:id (~seq #:error-value errv) left ...+ (~seq #:env r) right ...) clauses ...+)
    ;;  #'(define-match-do (name #:error-value errv #:env r left ... right ...) clauses ...)]
    ;; [(_ (name:id (~seq #:error-value errv) (~seq #:env r) left ...+ (~seq #:sto s) right ...) clauses ...+)
    ;;  #'(define-match-do (name #:error-value errv #:env r #:sto s left ... right ...) clauses ...)]
    ;; [(_ (name:id (~seq #:error-value errv) (~seq #:env r) (~seq #:sto s) left ...+ (~seq #:matching m) right ...) clauses ...+)
    ;;  #'(define-match-do (name #:error-value errv #:env r #:sto s #:matching m left ... right ...) clauses ...)]
    [(_ (name:id (~seq #:error-value errv)
                 (~seq #:env r)
                 (~seq #:sto s)
                 (~seq #:matching m) . args) clauses ...+)
     #'(define (name r s m . args)
         (displayln-debug (symbol->string 'name))
         (displayln-debug (format "    env: ~a" r))
         (displayln-debug (format "    sto: ~a" s))
         (displayln-debug (format "    matching: ~a" m))
         (begin0
             (match-do #:error-value errv #:env r #:sto s m clauses ...)
           (displayln-debug "returning...")))]))
