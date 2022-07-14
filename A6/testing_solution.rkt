#lang rosette/safe

(require rosette/lib/synthax)

(define repr_size 16)

(current-bitwidth repr_size)
(define bvrepr? (bitvector repr_size))

#;(define (next-power i)
   (let ((v (integer->bitvector i bvrepr?)))
     (let ((v (bvadd v (integer->bitvector -1 bvrepr?))))
       (let ((v (bvor v (bvashr v (integer->bitvector 6 bvrepr?)))))
         (let ((v (bvor v (bvashr v (integer->bitvector 2 bvrepr?)))))
           (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
             (let ((v (bvor v (bvashr v (integer->bitvector 4 bvrepr?)))))
               (let ((v (bvsub v (integer->bitvector -1 bvrepr?))))
                 (bitvector->integer v)))))))))

#;(define (next-power i)
   (let ((v (integer->bitvector i bvrepr?)))
     (let ((v (bvsub v (integer->bitvector 1 bvrepr?))))
       (let ((v (bvor v (bvashr v (integer->bitvector 2 bvrepr?)))))
         (let ((v (bvor v (bvashr v (integer->bitvector 3 bvrepr?)))))
           (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
             (let ((v (bvor v (bvashr v (integer->bitvector 4 bvrepr?)))))
               (let ((v (bvadd v (integer->bitvector 1 bvrepr?))))
                 (bitvector->integer v)))))))))

#;(define (next-power i)
   (let ((v (integer->bitvector i bvrepr?)))
     (let ((v (bvsub v (integer->bitvector 1 bvrepr?))))
       (let ((v (bvor v (bvashr v (integer->bitvector 3 bvrepr?)))))
         (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
           (let ((v (bvor v (bvor v (integer->bitvector -128 bvrepr?)))))
             (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
               (let ((v (bvor v (bvor v (integer->bitvector 0 bvrepr?)))))
                 (let ((v (bvsub v (integer->bitvector -65 bvrepr?))))
                   (bitvector->integer v))))))))))

#;(define (next-power i)
   (let ((v (integer->bitvector i bvrepr?)))
     (let ((v (bvsub v (integer->bitvector 1 bvrepr?))))
       (let ((v (bvor v (bvashr v (integer->bitvector 15 bvrepr?)))))
         (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
           (let ((v (bvor v (bvashr v (integer->bitvector 2 bvrepr?)))))
             (let ((v (bvor v (bvashr v (integer->bitvector 4 bvrepr?)))))
               (let ((v (bvor v (bvashr v (integer->bitvector 7 bvrepr?)))))
                 (let ((v (bvsub v (integer->bitvector -1 bvrepr?))))
                   (bitvector->integer v))))))))))

#;(define (next-power i)
   (let ((v (integer->bitvector i bvrepr?)))
     (let ((v (bvsub v (integer->bitvector 1 bvrepr?))))
       (let ((v (bvor v (bvashr v (integer->bitvector 16 bvrepr?)))))
         (let ((v (bvor v (bvashr v (integer->bitvector 4 bvrepr?)))))
           (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
             (let ((v (bvor v (bvashr v (integer->bitvector 8 bvrepr?)))))
               (let ((v (bvor v (bvashr v (integer->bitvector 32 bvrepr?)))))
                 (let ((v (bvor v (bvashr v (integer->bitvector 2 bvrepr?)))))
                   (let ((v (bvsub v (integer->bitvector -1 bvrepr?))))
                     (bitvector->integer v)))))))))))

#;(define (next-power i)
   (let ((v (integer->bitvector i bvrepr?)))
     (let ((v (bvsub v (integer->bitvector 1 bvrepr?))))
       (let ((v (bvor v (bvashr v (integer->bitvector 6 bvrepr?)))))
         (let ((v (bvor v (bvashr v (integer->bitvector 3 bvrepr?)))))
           (let ((v (bvor v (bvashr v (integer->bitvector 11 bvrepr?)))))
             (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
               (let ((v (bvor v (bvashr v (integer->bitvector 2 bvrepr?)))))
                 (let ((v (bvor v (bvashr v (integer->bitvector 24 bvrepr?)))))
                   (let ((v (bvsub v (integer->bitvector -1 bvrepr?))))
                     (bitvector->integer v)))))))))))

#;(define (next-power i)
   (let ((v (integer->bitvector i bvrepr?)))
     (let ((v (bvsub v (integer->bitvector 1 bvrepr?))))
       (let ((v (bvor v (bvashr v (integer->bitvector 16 bvrepr?)))))
         (let ((v (bvor v (bvashr v (integer->bitvector 4 bvrepr?)))))
           (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
             (let ((v (bvor v (bvashr v (integer->bitvector 8 bvrepr?)))))
               (let ((v (bvor v (bvashr v (integer->bitvector 32 bvrepr?)))))
                 (let ((v (bvor v (bvashr v (integer->bitvector 2 bvrepr?)))))
                   (let ((v (bvsub v (integer->bitvector -1 bvrepr?))))
                     (bitvector->integer v)))))))))))

(define (next-power i)
   (let ((v (integer->bitvector i bvrepr?)))
     (let ((v (bvsub v (integer->bitvector 1 bvrepr?))))
       (let ((v (bvor v (bvashr v (integer->bitvector 519 bvrepr?)))))
         (let ((v (bvor v (bvashr v (integer->bitvector 14 bvrepr?)))))
           (let ((v (bvor v (bvashr v (integer->bitvector 2 bvrepr?)))))
             (let ((v (bvor v (bvashr v (integer->bitvector 1 bvrepr?)))))
               (let ((v (bvor v (bvashr v (integer->bitvector 6 bvrepr?)))))
                 (let ((v (bvor v (bvashr v (integer->bitvector 4 bvrepr?)))))
                   (let ((v (bvadd v (integer->bitvector 1 bvrepr?))))
                     (bitvector->integer v)))))))))))