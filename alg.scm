(define (simplify exp)
  (cond ((or (number? exp) (variable? exp)) exp)
        ((sum? exp) exp)
        ((product? exp) exp)
        (else
         (error "unknown expression type -- SIMPLIFY" exp))))

(define (variable? a) (symbol? a))
(define coefficient cadr)
(define rest cddr)

(define (simple sym acc vars lst)
  (if (null? lst)
      (cons sym (cons acc vars))
      (let ((exp (car lst))
            (proc (eval sym))
            (pred (if (eq? sym '+) sum? product?)))
        (cond ((number? exp)
               (simple sym
                       (proc exp acc)
                       vars
                       (cdr lst)))
              ((pred exp)
               (let ((c (coefficient exp)))
                 (if (number? c)
                     (simple sym
                             (proc acc c)
                             (append vars (rest exp))
                             (cdr lst))
                     (simple sym
                             acc
                             (append vars (args exp))
                             (cdr lst)))))
              (else
               (simple  sym acc (cons exp vars) (cdr lst)))))))

(define (make-sum . lst)
  (let* ((s (simple '+ 0 '() lst))
         (c (coefficient s))
         (v (rest s)))
    (cond ((null? v) c)
          ((zero? c)
           (if (null? (cdr v)) (car v) (cons '+ v)))
          (else s))))

(define (make-product . lst)
  (let* ((s (simple '* 1 '() lst))
         (c (coefficient s))
         (v (rest s)))
    (cond ((zero? c) 0)
          ((null? v) c)
          ((= c 1)
           (if (null? (cdr v)) (car v) (cons '* v)))
          (else s))))

(define op car)
(define args cdr)
(define (sum? exp)
  (and (composite? exp) (eq? (op exp) '+)))
(define (product? exp)
  (and (composite? exp) (eq? (op exp) '*)))
(define (composite? exp) (pair? exp))
