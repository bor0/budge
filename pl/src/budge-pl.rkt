#lang racket

(define (budge-eval-go data code)
  (if (null? code)
      data
      (let ([x (car code)]
            [xs (cdr code)])
        (cond ((number? x)
               (letrec ([key (abs x)]
                        [value (hash-ref data key 0)])
                 (budge-eval-go (hash-set data key (max 0 (+ value (sgn x)))) xs)))
              ((list? x) (if (not (= 0 (hash-ref data (abs (car x)) 0)))
                             (budge-eval-go (budge-eval-go data (cdr x)) code)
                             (budge-eval-go data xs)))))))

(define (budge-eval data code)
  (let ([h (budge-eval-go data code)])
    (for/hash ([(k v) (in-hash h)] #:when (> v 0)) (values k (+ 1 v)))))

(define arith-add '((2 -2 1)))
(define arith-sub
  (list
   '[1 -1 3 5]   ; move r1 to r3 r4
   '[2 -2 4 6]   ; move r2 to r5 r6
   '[3 -3 -4]     ; calculate r3 - r4
   '[6 -5 -6]     ; calculate r6 - r5
   '[4 -4 1 3]     ; case x > y: move r4 to r1 and r3 (if it was set)
   '[3 [3 -3] 2]   ; if r3 was set, then set r2 to 1 to indicate flag
   '[5 -5 1]))

(budge-eval (make-immutable-hash (list (cons 1 2) (cons 2 2))) arith-add)
(budge-eval (make-immutable-hash (list (cons 1 3) (cons 2 2))) arith-sub)
