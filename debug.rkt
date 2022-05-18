#lang racket

(provide displayln-debug)

(define debug #f)

(define (displayln-debug . args)
  (if debug
      (apply displayln args)
      (void)))
