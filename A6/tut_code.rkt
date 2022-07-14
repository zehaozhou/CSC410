#lang rosette/safe
(require rosette/lib/synthax)

(define (poly x) (+ (* x x x x) (* 6 x x x) (* 11 x x) (* 6 x)))

(define (factored x) (* (+ x 1) (+ x 3) (+ x (??)) (+ x (??))))

(define (same p f x) (assert (= (p x) (f x))))

(define-symbolic x integer?)

(define solution
  (synthesize
   #:forall (list x)
   #:guarantee (same poly factored x)))

(if (sat? solution) (print-forms solution) (print "UNSAT"))