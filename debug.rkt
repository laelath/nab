#lang racket

(provide displayln-debug)

(define debug #t)

(define (displayln-debug . args)
  (if debug
      (apply displayln args)
      (void)))
