#lang racket
(provide (all-defined-out))
(require "ast.rkt"
         "types.rkt"
         "lambdas.rkt"
         "fv.rkt"
         "utils.rkt"
         "compile-define.rkt"
         "compile-expr.rkt"
         "compile-literals.rkt"
         (except-in "compile-ops.rkt" rax rbx rsp rdi)
         a86/ast)

;; Registers used
(define rbx 'rbx) ; heap
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg

;; type CEnv = [Listof Id]

;; Prog -> Asm
(define (compile p [mode 'interp])
  (match p
    [(Prog ds e)
     (prog (externs)
           (Global 'entry)
           (Label 'entry)
           (Mov rbx rdi) ; recv heap pointer
           (init-symbol-table p)
           (compile-defines-values ds)
           (compile-e e (reverse (define-ids ds)) #f)
           (Add rsp (* 8 (length ds))) ;; pop function definitions
           (match mode
             ['interp (Call 'strictify)] ;; call strictify if returning a racket value
             ['file (Mov (Offset 'heap_save 0) rbx)]) ;; save heap pointer if a compiled file
           (Ret)
           (compile-defines ds)
           (compile-lambda-defines (lambdas p))
           (Label 'raise_error_align)
           pad-stack
           (Call 'raise_error)
           (match mode
             ['interp strictify] ;; strictify only needed for interp mode
             ['file (seq)])
           (Global 'eval_thunk)
           (Label 'eval_thunk)
           (Mov rbx (Offset 'heap_save 0))
           (Mov rax rdi)
           (force-thunk)
           (Mov (Offset 'heap_save 0) rbx) ;; save heap pointer
           (Ret)
           (Data)
           (Label 'heap_save)
           (Dq 0)
           (compile-literals p))]))

(define (externs)
  (seq (Extern 'peek_byte)
       (Extern 'read_byte)
       (Extern 'write_byte)
       (Extern 'raise_error)
       (Extern 'intern_symbol)
       (Extern 'symb_cmp)
       (Extern 'memcpy)))
