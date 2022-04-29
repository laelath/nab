#lang racket
(provide (all-defined-out))
(require "ast.rkt"
         "types.rkt"
         "fv.rkt"
         "utils.rkt"
         "compile-expr.rkt"
         a86/ast)

;; [Listof Defn] -> [Listof Id]
(define (define-ids ds)
  (match ds
    ['() '()]
    [(cons (Defn f xs e) ds)
     (cons f (define-ids ds))]))

;; [Listof Defn] -> Asm
(define (compile-defines ds)
  (match ds
    ['() (seq)]
    [(cons d ds)
     (seq (compile-define d)
          (compile-defines ds))]))

;; Defn -> Asm
(define (compile-define d)
  (match d
    [(Defn f xs e)
     (compile-lambda-define (Lam f xs e))]))

;; Defns -> Asm
;; Compile the closures for ds and push them on the stack
(define (compile-defines-values ds)
  (seq (alloc-defines ds 0)
       (init-defines ds (reverse (define-ids ds)) 16)
       (add-rbx-defines ds 0)
       #;(thunkify-defines (length ds))))

(define (thunkify-defines n)
  (if (= n 0)
      (seq)
      (let ([i (* 8 (sub1 n))])
        (seq (Mov rax (Offset rsp i))
             (Mov (Offset rbx 0) rax)
             (Mov (Offset rsp i) rbx)
             (Add rbx 8)
             (thunkify-defines (sub1 n))))))

;; Defns Int -> Asm
;; Allocate closures for ds at given offset, but don't write environment yet
(define (alloc-defines ds off)
  (match ds
    ['() (seq)]
    [(cons (Defn f xs e) ds)
     (let ((fvs (fv (Lam f xs e))))
       (seq (Lea rax (symbol->label f))
            (Mov (Offset rbx (+ off 8)) rax)
            (Mov rax rbx)
            (Add rax off)
            (Push rax)
            (Add rax 8)
            (Or rax type-proc)
            (Mov (Offset rbx off) rax)
            (alloc-defines ds (+ off (* 8 (+ 2 (length fvs)))))))]))

;; Defns CEnv Int -> Asm
;; Initialize the environment for each closure for ds at given offset
(define (init-defines ds c off)
  (match ds
    ['() (seq)]
    [(cons (Defn f xs e) ds)
     (let ((fvs (fv (Lam f xs e))))
       (seq (free-vars-to-heap fvs c off)
            (init-defines ds c (+ off (* 8 (+ 2 (length fvs)))))))]))

;; Defns Int -> Asm
;; Compute adjustment to rbx for allocation of all ds
(define (add-rbx-defines ds n)
  (match ds
    ['() (Add rbx (* n 8))]
    [(cons (Defn f xs e) ds)
     (add-rbx-defines ds (+ n (+ 2 (length (fv (Lam f xs e))))))]))
