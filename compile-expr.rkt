#lang racket
(provide (all-defined-out))
(require "ast.rkt"
         "types.rkt"
         "lambdas.rkt"
         "fv.rkt"
         "utils.rkt"
         "compile-ops.rkt"
         "compile-datum.rkt"
         a86/ast)

;; Registers used
(define rax 'rax) ; return
(define rbx 'rbx) ; heap
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg

;; Expr CEnv Bool -> Asm
(define (compile-e e c t?)
  (match e
    [(Quote d)          (compile-datum d)]
    [(Eof)              (seq (Mov rax (imm->bits eof)))]
    [(Var x)            (compile-variable x c)]
    [(Prim p es)        (compile-prim p es c)]
    [(DCons dc fs es)   (compile-dcons dc fs es c)]
    [(If e1 e2 e3)      (compile-if e1 e2 e3 c t?)]
    [(Begin e1 e2)      (compile-begin e1 e2 c t?)]
    [(Let x f e1 e2)    (compile-let x f e1 e2 c t?)]
    [(App e fs es)      (compile-app e fs es c t?)]
    [(Lam f xs e)       (compile-lam f xs e c)]
    [(Match f e ps es)  (compile-match f e ps es c t?)]))

;; Id CEnv -> Asm
(define (compile-variable x c)
  (match (lookup x c)
    [#f (error (format "unbound variable: ~a" x))] ;(seq (Lea rax (symbol->label x)))]
    [i  (seq (Mov rax (Offset rsp i))
             (force-thunk))]))

;; Op (Listof Expr) CEnv -> Asm
(define (compile-prim p es c)
  (seq (compile-es* es c)
       (compile-op p)))

(define (compile-dcons dc fs es c)
  (seq (compile-thunks* fs es c)
       (match dc
         ['make-struct (compile-make-struct (length es))]
         [_ (compile-op dc)])))

;; Expr Expr Expr CEnv Bool -> Asm
(define (compile-if e1 e2 e3 c t?)
  (let ((l1 (gensym 'if))
        (l2 (gensym 'if)))
    (seq (compile-e e1 c #f)
         (Cmp rax val-false)
         (Je l1)
         (compile-e e2 c t?)
         (Jmp l2)
         (Label l1)
         (compile-e e3 c t?)
         (Label l2))))

;; Expr Expr CEnv Bool -> Asm
(define (compile-begin e1 e2 c t?)
  (seq (compile-e e1 c #f) ;; todo: whnfify
       (compile-e e2 c t?)))

;; Id Expr Expr CEnv Bool -> Asm
(define (compile-let x f e1 e2 c t?)
  (seq (compile-thunk f e1 c)
       (Push rax)
       (compile-e e2 (cons x c) t?)
       (Add rsp 8)))

;; Id [Listof Expr] CEnv Bool -> Asm
(define (compile-app e fs es c t?)
  ;(compile-app-nontail f es c)
  (if t?
      (compile-app-tail e fs es c)
      (compile-app-nontail e fs es c)))

;; Expr [Listof Expr] CEnv -> Asm
(define (compile-app-tail e fs es c)
  (seq (compile-e e c #f)
       (assert-proc rax)
       (Push rax)
       (compile-thunks fs es (cons #f c))
       (move-args (add1 (length es)) (length c))
       (Add rsp (* 8 (length c)))
       (Mov rax (Offset rsp (* 8 (length es))))
       (Xor rax type-proc)
       (Mov rax (Offset rax 0))
       (Jmp rax)))

;; Integer Integer -> Asm
(define (move-args i off)
  (cond [(zero? off) (seq)]
        [(zero? i)   (seq)]
        [else
         (seq (Mov r8 (Offset rsp (* 8 (sub1 i))))
              (Mov (Offset rsp (* 8 (+ off (sub1 i)))) r8)
              (move-args (sub1 i) off))]))

;; Expr [Listof Expr] CEnv -> Asm
;; The return address is placed above the arguments, so callee pops
;; arguments and return address is next frame
(define (compile-app-nontail e fs es c)
  (let ((r (gensym 'ret))
        (i (* 8 (length es))))
    (seq (Lea rax r)
         (Push rax)
         (compile-e e (cons #f c) #f)
         (assert-proc rax) ; can move assertion up in CBN
         (Push rax) ; value pushed here is the *forced* proc val
         (compile-thunks fs es (cons #f (cons #f c)))
         (Mov rax (Offset rsp i))
         (Xor rax type-proc)
         (Mov rax (Offset rax 0)) ; fetch the code label
         (Jmp rax)
         (Label r))))

(define (compile-thunks fs es c)
  (match* (fs es)
    [('() '()) (seq)]
    [((cons f fs) (cons e es))
     (seq (compile-thunk f e c)
          (Push rax)
          (compile-thunks fs es (cons #f c)))]))

(define (compile-thunks* fs es c)
  (match* (fs es)
    [((cons f '()) (cons e '()))
     (compile-thunk f e c)]
    [((cons f fs) (cons e es))
     (seq (compile-thunk f e c)
          (Push rax)
          (compile-thunks* fs es (cons #f c)))]))

;; TODO: simple opt, if a var or quote then don't create a new thunk
(define (compile-thunk f e c)
  (match e
    [(Var x) (Mov rax (Offset rsp (lookup x c)))]
    [(Quote d) (seq (compile-datum d)
                    make-resolved-thunk)] ;; TODO: can create a single thunk for this data
    [_ (let ([fvs (fv e)])
         (seq (% "thunk creation")
              (Mov rax val-thunk)
              (Mov (Offset rbx 0) rax)
              (Lea rax (symbol->label f))
              (Mov (Offset rbx 8) rax)
              (free-vars-to-heap fvs c 16)
              (Mov rax rbx)
              (Add rbx (* 8 (+ 2 (length fvs))))))]))

(define make-resolved-thunk
  (seq (% "resolved thunk creation")
       (Mov (Offset rbx 0) rax)
       (Mov rax rbx)
       (Add rbx 8)))

;; Id [Listof Id] Expr CEnv -> Asm
(define (compile-lam f xs e c)
  (let ((fvs (fv (Lam f xs e))))
    (seq (Lea rax (symbol->label f))
         (Mov (Offset rbx 0) rax)
         (free-vars-to-heap fvs c 8)
         (Mov rax rbx) ; return value
         (Or rax type-proc)
         (Add rbx (* 8 (add1 (length fvs)))))))

;; [Listof Id] CEnv Int -> Asm
;; Copy the values of given free variables into the heap at given offset
(define (free-vars-to-heap fvs c off)
  (match fvs
    ['() (seq)]
    [(cons x fvs)
     (seq (Mov r8 (Offset rsp (lookup x c)))
          (Mov (Offset rbx off) r8)
          (free-vars-to-heap fvs c (+ off 8)))]))

;; [Listof Lam] -> Asm
(define (compile-lambda-defines ls)
  (match ls
    ['() (seq)]
    [(cons l ls)
     (seq (compile-lambda-define l)
          (compile-lambda-defines ls))]))

;; Lam -> Asm
(define (compile-lambda-define l)
  (let ((fvs (fv l)))
    (match l
      [(Lam f xs e)
       (let ((env  (append (reverse fvs) (reverse xs) (list #f))))
         (seq (Label (symbol->label f))
              (Mov rax (Offset rsp (* 8 (length xs))))
              (Xor rax type-proc)
              (copy-env-to-stack fvs 8)
              (compile-e e env #t)
              (Add rsp (* 8 (length env))) ; pop env
              (Ret)))])))

;; [Listof Id] Int -> Asm
;; Copy the closure environment at given offset to stack
(define (copy-env-to-stack fvs off)
  (match fvs
    ['() (seq)]
    [(cons _ fvs)
     (seq (Mov r9 (Offset rax off))
          (Push r9)
          (copy-env-to-stack fvs (+ 8 off)))]))

;; [Listof Expr] CEnv -> Asm
(define (compile-es es c)
  (match es
    ['() (seq)]
    [(cons e es)
     (seq (compile-e e c #f)
          (Push rax)
          (compile-es es (cons #f c)))]))

;; [Listof Expr] CEnv -> Asm
;; Like compile-es, but leave last subexpression in rax (if exists)
(define (compile-es* es c)
  (match es
    ['() (seq)]
    [(cons e '())
     (compile-e e c #f)]
    [(cons e es)
     (seq (compile-e e c #f)
          (Push rax)
          (compile-es* es (cons #f c)))]))

;; Expr [Listof Pat] [Listof Expr] CEnv Bool -> Asm
(define (compile-match f e ps es c t?)
  (let ([done (gensym)])
    (seq (compile-thunk f e c)
         (Push rax) ; save away to be restored by each clause
         (compile-match-clauses ps es (cons #f c) done t?)
         (Jmp 'raise_error_align)
         (Label done)
         (Add rsp 8)))) ; pop the saved value being matched

;; [Listof Pat] [Listof Expr] CEnv Symbol Bool -> Asm
(define (compile-match-clauses ps es c done t?)
  (match* (ps es)
    [('() '()) (seq)]
    [((cons p ps) (cons e es))
     (seq (compile-match-clause p e c done t?)
          (compile-match-clauses ps es c done t?))]))

;; Pat Expr CEnv Symbol Bool -> Asm
(define (compile-match-clause p e c done t?)
  (let ((next (gensym)))
    (match (compile-pattern p '() next)
      [(list i f cm)
       (seq (Mov rax (Offset rsp 0)) ; restore value being matched
            i
            (compile-e e (append cm c) t?)
            (Add rsp (* 8 (length cm)))
            (Jmp done)
            f
            (Label next))])))

;; Pat CEnv Symbol -> (list Asm Asm CEnv)
(define (compile-pattern p cm next)
  (match p
    [(PWild)
     (list (seq) (seq) cm)]
    [(PVar x)
     (list (seq (Push rax))
           (seq)
           (cons x cm))]
    [(PStr s)
     (let ((fail (gensym)))
       (list (seq (force-thunk)
                  (Lea rdi (symbol->data-label (string->symbol s)))
                  (Mov r8 rax)
                  (And r8 ptr-mask)
                  (Cmp r8 type-str)
                  (Jne fail)
                  (Xor rax type-str)
                  (Mov rsi rax)
                  pad-stack
                  (Call 'symb_cmp)
                  unpad-stack
                  (Cmp rax 0)
                  (Jne fail))
             (seq (Label fail)
                  (Add rsp (* 8 (length cm)))
                  (Jmp next))
             cm))]
    [(PSymb s)
     (let ((fail (gensym)))
       (list (seq (force-thunk)
                  (Lea r9 (Plus (symbol->data-label s) type-symb))
                  (Cmp rax r9)
                  (Jne fail))
             (seq (Label fail)
                  (Add rsp (* 8 (length cm)))
                  (Jmp next))
             cm))]
    [(PLit l)
     (let ((fail (gensym)))
       (list (seq (force-thunk)
                  (Cmp rax (imm->bits l))
                  (Jne fail))
             (seq (Label fail)
                  (Add rsp (* 8 (length cm)))
                  (Jmp next))
             cm))]
    [(PAnd p1 p2) ; TODO: lazy
     (match (compile-pattern p1 (cons #f cm) next)
       [(list i1 f1 cm1)
        (match (compile-pattern p2 cm1 next)
          [(list i2 f2 cm2)
           (list
            (seq (Push rax)
                 i1
                 (Mov rax (Offset rsp (* 8 (- (sub1 (length cm1)) (length cm)))))
                 i2)
            (seq f1 f2)
            cm2)])])]
    [(PBox p)
     (match (compile-pattern p cm next)
       [(list i1 f1 cm1)
        (let ((fail (gensym)))
          (list
           (seq (force-thunk)
                (Mov r8 rax)
                (And r8 ptr-mask)
                (Cmp r8 type-box)
                (Jne fail)
                (Xor rax type-box)
                (Mov rax (Offset rax 0))
                i1)
           (seq f1
                (Label fail)
                (Add rsp (* 8 (length cm))) ; haven't pushed anything yet
                (Jmp next))
           cm1))])]
    [(PCons p1 p2)
     (match (compile-pattern p1 (cons #f cm) next)
       [(list i1 f1 cm1)
        (match (compile-pattern p2 cm1 next)
          [(list i2 f2 cm2)
           (let ((fail (gensym)))
             (list
              (seq (force-thunk)
                   (Mov r8 rax)
                   (And r8 ptr-mask)
                   (Cmp r8 type-cons)
                   (Jne fail)
                   (Xor rax type-cons)
                   (Mov r8 (Offset rax 0))
                   (Push r8)                ; push cdr
                   (Mov rax (Offset rax 8)) ; mov rax car
                   i1
                   (Mov rax (Offset rsp (* 8 (- (sub1 (length cm1)) (length cm)))))
                   i2)
              (seq f1
                   f2
                   (Label fail)
                   (Add rsp (* 8 (length cm))) ; haven't pushed anything yet
                   (Jmp next))
              cm2))])])]
    [(PStruct n ps)
     (match (compile-struct-patterns ps (cons #f cm) next 1 (add1 (length cm)))
       [(list i f cm1)
        (let ((fail (gensym)))
          (list
           (seq (%%% "struct")
                (force-thunk)
                (Mov r8 rax)
                (And r8 ptr-mask)
                (Cmp r8 type-struct)
                (Jne fail)
                (Xor rax type-struct)
                (Mov r8 (Offset rax 0))
                (Lea r9 (Plus (symbol->data-label n) type-symb))
                (Cmp r8 r9)
                (Jne fail)
                (Push rax)
                i)
           (seq f
                (Label fail)
                (Add rsp (* 8 (length cm)))
                (Jmp next))
           cm1))])]))

;; [Listof Pat] CEnv Symbol Nat Nat -> (list Asm Asm CEnv)
(define (compile-struct-patterns ps cm next i cm0-len)
  (match ps
    ['() (list '() '() cm)]
    [(cons p ps)
     (match (compile-pattern p cm next)
       [(list i1 f1 cm1)
        (match (compile-struct-patterns ps cm1 next (add1 i) cm0-len)
          [(list is fs cmn)
           (list
            (seq (Mov rax (Offset rax (* 8 i)))
                 i1
                 (Mov rax (Offset rsp (* 8 (- (length cm1) cm0-len))))
                 is)
            (seq f1 fs)
            cmn)])])]))
