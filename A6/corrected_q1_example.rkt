#lang rosette/safe

(define (next-power i)
  (let ([v (integer->bitvector i (bitvector 16))]) ;; > (bitvector 16) instead of 16 <
    (let ([v (bvsub v (bv 1 16))]) ;; n--
      (let ([v (bvor v (bvashr v (bv 1 16)))]) ;; n = n | n >> 1
        (let ([v (bvor v (bvashr v (bv 2 16)))]) ;; n = n | n >> 2
          (let ([v (bvor v (bvashr v (bv 4 16)))]) ;; n = n | n >> 4
            (let ([v (bvor v (bvashr v (bv 8 16)))]) ;; n = n | n >> 8
              (let ([v (bvadd v (bv 1 16))]) ;; n ++
                (bitvector->integer v)))))))))