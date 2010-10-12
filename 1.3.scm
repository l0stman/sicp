#lang scheme
(define (square x) (* x x))

(define (sum-of-squares a b)
  (+ (square a) (square b)))

(define (max a b)
  (if (< a b) b a))

(define (f a b c)
  (sum-of-squares (max a b) (max b c)))