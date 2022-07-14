#lang rosette/safe

(require rosette/lib/synthax)

(define repr_size 60)

(current-bitwidth repr_size)
(define bvrepr? (bitvector repr_size))

;; The two following rules define the operators that are used in the solution.
;;  These rules are a 'choice' rule:
(define-synthax BVLogicOp
  ([(BVLogicOp) (choose bvor bvashr)]))

(define-synthax BVArithOp
  ([(BVArithOp) (choose bvadd bvsub)]))

;; You can only modify the value of repr_size in the code above. All the functions
;; you need to implement should be place below this point.
;; ----------------------------------------------------------------------------
;; - do not use bvadd, bvsub, bvor, bvashr directly below but only the
;;   syntax rules BVLogicOp and BVArithOp.
;; - you can find the documentation for the bitvector operators for Rosette at
;;   the following address:
;;         https://docs.racket-lang.org/rosette-guide/sec_bitvectors.html
;; - repr_size is the size of the current bitvector representation. We will test
;;   your code for different sizes of repr_size, up to 64. You can modify its value
;;   in the code above.
;; - bvrepr? represents the type of bitvectors of size repr_size. For example,
;;   you can define  a bitvector of this type that represents the integer 0:
;;   (bv 0 bvrerpr?)


;; ------- CORRECTNESS SPECIFICATION ------------------------------------------

;; See the instructions in the handout:
;; (specification f x) <=> (f x) is the next larger power of two of x.
;; TODO
(define (specification f x) (and (< (/ (f x) 2) x) (<= x (f x)) (isPowerOfTwo (f x))))

(define (isPowerOfTwo t) (equal? (bvand (integer->bitvector t bvrepr?)
                                        (bvsub (integer->bitvector t bvrepr?) (bv 1 bvrepr?))) (bv 0 bvrepr?)))

;; See the instructions in the handout:
;; (constraint x) <=> x can be represented as a bitvector of type bvrepr?
;; (a bivector of type bvrepr? is a bitvector of size repr_size)
;; TODO
(define (constraint x) (and (> x 0) (<= x (expt 2 (- repr_size 2)))))


;; ------ SKETCH --------------------------------------------------------------
;; This rule generates bitvectors of size reprsize.
(define-synthax BitVector? ([(BitVector?) (integer->bitvector (??) bvrepr?)]))

;; You can use this rule as a helper. It synthesizes an operation on a vector
;; of type (bvop v (bvop' v x)) where bvop and bvop' are two logical bitvector
;; operations (BVLogicOp) and x is a bitvector created the rule you implemented above.
(define-synthax BVLogic?
  ([(BVLogic? v) ((BVLogicOp) v ((BVLogicOp) v (BitVector?)))]))
;; And this rule is a helper to synthesize an arithmetic operation on a bitvector.
(define-synthax BVArith?
  ([(ArithBVConst? v) ((BVArithOp) v (BitVector?))]))

;; This rule represents the sequence of logical bitwise operations. It should
;; use a depth parameter.
(define-synthax (Body? v k)
    #:base (let ([v (BVArith? v)]) (bitvector->integer v))
    #:else (let ([v (BVLogic? v)]) (Body? v (- k 1))))

;; This is the actual sketch.
(define (next-power i) (let ([v (integer->bitvector i bvrepr?)])
                         (let ([v (BVArith? v)])
                           (Body? v 6))))
 

;; ----------------------------------------------------------------------------
;; Do not modify the code below this point!
;; ----------------------------------------------------------------------------
(define-symbolic x integer?)

(define solution
  (synthesize
   #:forall (list x) ;; There is only one universally quantified variable.
   #:assume (assert (constraint x)) ;; The input satisfies (constraint x).
   #:guarantee (assert (specification next-power x))))

(if
 (sat? solution)
 (print-forms solution)
 (core solution))

