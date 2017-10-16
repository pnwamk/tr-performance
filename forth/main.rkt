#lang typed/racket/base

(require
  "command-types.rkt")
(require "eval.rkt")

;; =============================================================================

(define (main)
  (call-with-input-file* (ann "history.txt" Path-String)
    (lambda ([p : Input-Port])
      (let-values ([(_e _s) (forth-eval* p)]) (void))))
  (void))

(time (main))
