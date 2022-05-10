#lang racket
(require "test-runner.rkt"
         "../parse.rkt"
         "../compile.rkt"
         "../unload-bits-asm.rkt"
         a86/interp)

;; link with runtime for IO operations
(unless (file-exists? "../runtime.o")
  (system "make -C .. runtime.o"))
(current-objs
 (list (path->string (normalize-path "../runtime.o"))))

(define run (λ p (unload/free (asm-interp (compile (parse p))))))
(define run/io (λ (s . p)
                 (match (asm-interp/io (compile (parse p)) s)
                   ['err 'err]
                   [(cons r o) (cons (unload/free r) o)])))

(test-runner    run)
(test-runner-io run/io)
