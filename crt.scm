#lang scheme
(define (square x) (* x x))

(define (cube x) (* x x x))

(define (crt-iter guess x)
  (if (good-enough? guess x)
      guess
      (crt-iter (improve guess x)
                 x)))

(define (improve guess x)
  (/ (+ (/ x (square guess))
        (* 2 guess))
     3))

(define (good-enough? guess x)
  (< (abs (- (/ (improve guess x)
                guess)
             1))
     0.001))

(define (crt x)
  (crt-iter 1.0 x))