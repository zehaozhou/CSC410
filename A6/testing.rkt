#lang rosette/safe

(require rosette/lib/synthax)

(define repr_size 16)

(current-bitwidth repr_size)
(define bvrepr? (bitvector repr_size))

; solution for next-power when repr_size = 16 from handout
(define (next-power i)
  (let ([v (integer->bitvector i (bitvector 16))]) ;; > (bitvector 16) instead of 16 <
    (let ([v (bvsub v (bv 1 16))]) ;; n--
      (let ([v (bvor v (bvashr v (bv 1 16)))]) ;; n = n | n >> 1
        (let ([v (bvor v (bvashr v (bv 2 16)))]) ;; n = n | n >> 2
          (let ([v (bvor v (bvashr v (bv 4 16)))]) ;; n = n | n >> 4
            (let ([v (bvor v (bvashr v (bv 8 16)))]) ;; n = n | n >> 8
              (let ([v (bvadd v (bv 1 16))]) ;; n ++
                (bitvector->integer v)))))))))

(define-symbolic x integer?)

(print (next-power 16383))
(define solution16383
  (synthesize
   #:forall (list x) ;; There is only one universally quantified variable.
   #:assume (assert (= x 16383)) ;; The input satisfies (constraint x).
   #:guarantee (assert (= (next-power x) 16384))))
(sat? solution16383)

(print (next-power 16384))
(define solution16384
  (synthesize
   #:forall (list x) ;; There is only one universally quantified variable.
   #:assume (assert (= x 16384)) ;; The input satisfies (constraint x).
   #:guarantee (assert (= (next-power x) 16384))))
(sat? solution16384)
