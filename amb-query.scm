;;; Use C-c C-r instead of C-c C-l
(load "amb-eval.scm")

;;; Launch the amb evaluator.
(driver-loop)

(define (require p)
  (if (not p) (amb)))

(define (an-element-of items)
  (require (not (null? items)))
  (amb (car items) (an-element-of (cdr items))))

(define (make-table)
  (let ((table (list '*table*)))
    (define (lookup key2 key1)
      (let ((record1 (assoc key1 (cdr table))))
        (if record1
            (let ((record2 (assoc key2 (cdr record1))))
              (if record2
                  (cdr record2)
                  false))
            false)))
    (define (insert! key2 key1 value)
      (let ((record1 (assoc key1 (cdr table))))
        (if record1
            (let ((record2 (assoc key2 (cdr record1))))
              (if record2
                  (set-cdr! record2 value)
                  (set-cdr! record1
                            (cons (cons key2 value) (cdr record1)))))
            (set-cdr! table
                      (cons (list key1 (cons key2 value))
                            (cdr table)))))
      'ok)
    (lambda (msg)
      (cond ((eq? msg 'get) lookup)
            ((eq? msg 'put) insert!)
            (else (error "TABLE -- Unknown message" msg))))))
(define table (make-table))
(define (get key2 key1) ((table 'get) key2 key1))
(define (put key2 key1 value) ((table 'put) key2 key1 value))

(define (assert! q)
  (add-rule-or-assertion! (query-syntax-process q))
  (newline)
  (display "Assertion added to data base")
  'ok)
(define (query q)
  (let ((q (query-syntax-process q)))
    (newline)
    (display
     (instantiate* q
                   (qeval q empty-frame)
                   (lambda (v f)
                     (contract-question-mark v))))
    'ok))

(define (instantiate* exp frame unbound-var-handler)
  (define (copy exp)
    (cond ((var? exp)
           (let ((binding (binding-in-frame exp frame)))
             (if binding
                 (copy (binding-value binding))
                 (unbound-var-handler exp frame))))
          ((pair? exp)
           (cons (copy (car exp)) (copy (cdr exp))))
          (else exp)))
  (copy exp))

(define (qeval query frame)
  (let ((qproc (get (type query) 'qeval)))
    (if qproc
        (qproc (contents query) frame)
        (simple-query query frame))))

(define (simple-query query-pattern frame)
  (amb (find-assertion query-pattern frame)
       (apply-a-rule query-pattern frame)))

(define (conjoin conjuncts frame)
  (if (empty-conjuction? conjuncts)
      frame
      (conjoin (rest-conjuncts conjuncts)
               (qeval (first-conjunct conjuncts)
                      frame))))
(put 'and 'qeval conjoin)

(define (disjoin disjuncts frame)
  (require (not (empty-disjunction? disjuncts)))
  (ramb
   (qeval (first-disjunct disjuncts) frame)
   (disjoin (rest-disjuncts disjuncts) frame)))
(put 'or 'qeval disjoin)

(define (negate operands frame)
  (if-fail-only (qeval (negated-query operands) frame)
                frame))
(put 'not 'qeval negate)

(define (lisp-value call frame)
  (if (execute
       (instantiate* call
                     frame
                     (lambda (v f)
                       (error "Unknown pat var -- LISP-VALUE" v))))
      frame
      (amb)))
(put 'lisp-value 'qeval lisp-value)

(define (execute exp)
  (apply (eval (predicate exp) (interaction-environment))
         (args exp)))

(define (always-true ignore frame) frame)
(put 'always-true 'qeval always-true)


(define (find-assertion pattern frame)
  (let ((assert (an-element-of (fetch-assertions pattern frame))))
    (pattern-match pattern assert frame)))

(define (pattern-match pat dat frame)
  (cond ((equal? pat dat) frame)
        ((var? pat) (extend-if-consistent pat dat frame))
        ((and (pair? pat) (pair? dat))
         (pattern-match (cdr pat)
                        (cdr dat)
                        (pattern-match (car pat)
                                       (car dat)
                                       frame)))
        (else (amb))))

(define (extend-if-consistent var dat frame)
  (let ((binding (binding-in-frame var frame)))
    (if binding
        (pattern-match (binding-value binding) dat frame)
        (extend var dat frame))))

(define (apply-a-rule query-pattern query-frame)
  (let ((rule (an-element-of (fetch-rules query-pattern query-frame))))
    (let ((clean-rule (rename-variables-in rule)))
      (let ((unify-result
             (unify-match query-pattern
                          (conclusion clean-rule)
                          query-frame)))
        (qeval (rule-body clean-rule) unify-result)))))

(define (rename-variables-in rule)
  (let ((rule-application-id (new-rule-application-id)))
    (define (tree-walk exp)
      (cond ((var? exp)
             (make-new-variable exp rule-application-id))
            ((pair? exp)
             (cons (tree-walk (car exp))
                   (tree-walk (cdr exp))))
            (else exp)))
    (tree-walk rule)))

(define (unify-match p1 p2 frame)
  (cond ((equal? p1 p2) frame)
        ((var? p1) (extend-if-possible p1 p2 frame))
        ((var? p2) (extend-if-possible p2 p1 frame))
        ((and (pair? p1) (pair? p2))
         (unify-match (cdr p1)
                      (cdr p2)
                      (unify-match (car p1)
                                   (car p2)
                                   frame)))
        (else (amb))))

(define (extend-if-possible var val frame)
  (let ((binding (binding-in-frame var frame)))
    (cond (binding
           (unify-match
            (binding-value binding) val frame))
          ((var? val)
           (let ((binding (binding-in-frame val frame)))
             (if binding
                 (unify-match
                  var (binding-value binding) frame)
                 (extend var val frame))))
          (else
           (require (not (depends-on? val var frame)))
           (extend var val frame)))))

(define (depends-on? exp var frame)
  (define (tree-walk e)
    (cond ((var? e)
           (if (equal? var e)
               true
               (let ((b (binding-in-frame e frame)))
                 (if b
                     (tree-walk (binding-value b))
                     false))))
          ((pair? e)
           (or (tree-walk (car e))
               (tree-walk (cdr e))))
          (else false)))
  (tree-walk exp))

(define THE-ASSERTIONS '())
(define (fetch-assertions pattern frame)
  (if (use-index? pattern)
      (get-indexed-assertions pattern)
      (get-all-assertions)))
(define (get-all-assertions) THE-ASSERTIONS)
(define (get-indexed-assertions pattern)
  (get-or-null (index-key-of pattern) 'assertions))

(define (get-or-null key1 key2)
  (let ((s (get key1 key2)))
    (if s s '())))

(define THE-RULES '())
(define (fetch-rules pattern frame)
  (if (use-index? pattern)
      (get-indexed-rules pattern)
      (get-all-rules)))
(define (get-all-rules) THE-RULES)
(define (get-indexed-rules pattern)
  (append
   (get-or-null (index-key-of pattern) 'rules)
   (get-or-null '? 'rules)))

(define (add-rule-or-assertion! assertion)
  (if (rule? assertion)
      (add-rule! assertion)
      (add-assertion! assertion)))
(define (add-assertion! assertion)
  (store-assertion-in-index assertion)
  (set! THE-ASSERTIONS (cons assertion THE-ASSERTIONS))
  'ok)
(define (add-rule! rule)
  (store-rule-in-index rule)
  (set! THE-RULES (cons rule THE-RULES))
  'ok)

(define (store-assertion-in-index assertion)
  (if (indexable? assertion)
      (let ((key (index-key-of assertion)))
        (put key
             'assertions
             (cons assertion
                   (get-or-null key 'assertions))))))
(define (store-rule-in-index rule)
  (let ((pattern (conclusion rule)))
    (if (indexable? pattern)
        (let ((key (index-key-of pattern)))
          (put key
               'rules
               (cons rule
                     (get-or-null key 'rules)))))))

(define (indexable? pat)
  (or (constant-symbol? (car pat))
      (var? (car pat))))
(define (index-key-of pat)
  (let ((key (car pat)))
    (if (var? key) '? key)))

(define (use-index? pat)
  (constant-symbol? (car pat)))

(define (type exp)
  (if (pair? exp)
      (car exp)
      (error "Unknown expression TYPE" exp)))
(define (contents exp)
  (if (pair? exp)
      (cdr exp)
      (error "Unknown expression CONTENTS" exp)))

(define (empty-conjuction? exps) (null? exps))
(define (first-conjunct exps) (car exps))
(define (rest-conjuncts exps) (cdr exps))
(define (empty-disjunction? exps) (null? exps))
(define (first-disjunct exps) (car exps))
(define (rest-disjuncts exps) (cdr exps))
(define (negated-query exps) (car exps))
(define (predicate exps) (car exps))
(define (args exps) (cdr exps))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      false))
(define (rule? statement)
  (tagged-list? statement 'rule))
(define (conclusion rule) (cadr rule))
(define (rule-body rule)
  (if (null? (cddr rule))
      '(always-true)
      (caddr rule)))

(define (query-syntax-process exp)
  (map-over-symbols expand-question-mark exp))
(define (map-over-symbols proc exp)
  (cond ((pair? exp)
         (cons (map-over-symbols proc (car exp))
               (map-over-symbols proc (cdr exp))))
        ((symbol? exp) (proc exp))
        (else exp)))
(define (expand-question-mark symbol)
  (let ((chars (symbol->string symbol)))
    (if (string=? (substring chars 0 1) "?")
        (list '?
              (string->symbol
               (substring chars 1 (string-length chars))))
        symbol)))

(define (var? exp)
  (tagged-list? exp '?))
(define (constant-symbol? exp) (symbol? exp))
(define rule-counter 0)
(define (new-rule-application-id)
  (set! rule-counter (+ 1 rule-counter))
  rule-counter)
(define (make-new-variable var rule-application-id)
  (cons '? (cons rule-application-id (cdr var))))
(define (contract-question-mark variable)
  (string->symbol
   (string-append "?"
                  (if (number? (cadr variable))
                      (string-append (symbol->string (caddr variable))
                                     "-"
                                     (number->string (cadr variable)))
                      (symbol->string (cadr variable))))))
(define (make-binding variable value)
  (cons variable value))
(define (binding-variable binding)
  (car binding))
(define (binding-value binding)
  (cdr binding))
(define (binding-in-frame variable frame)
  (assoc variable frame))
(define empty-frame '())
(define (extend variable value frame)
  (cons (make-binding variable value) frame))