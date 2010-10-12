(require r5rs/init)
(load "eval.scm")

(define (ambeval exp env succeed fail)
  ((analyze exp) env succeed fail))

(define (analyze exp)
  (cond ((self-evaluating? exp)
         (analyze-self-evaluating exp))
        ((quoted? exp) (analyze-quoted exp))
        ((variable? exp) (analyze-variable exp))
        ((assignment? exp) (analyze-assignment exp))
        ((assign-car? exp) (analyze-assign-pair exp car set-car!))
        ((assign-cdr? exp) (analyze-assign-pair exp car set-cdr!))
        ((permanent-assignment? exp) (analyze-perm-assign exp))
        ((definition? exp) (analyze-definition exp))
        ((if? exp) (analyze-if exp))
        ((if-fail? exp) (analyze-if-fail exp))
        ((if-fail-only? exp) (analyze-if-fail-only exp))
        ((if-succeed-only? exp) (analyze-if-succeed-only exp))
        ((lambda? exp) (analyze-lambda exp))
        ((begin? exp) (analyze-sequence (begin-actions exp)))
        ((cond? exp) (analyze (cond->if exp)))
        ((let? exp) (analyze (let->combination exp)))
        ((and? exp) (analyze-and (logic-actions exp)))
        ((or? exp) (analyze-or (logic-actions exp)))
        ((amb? exp) (analyze-amb exp))
        ((ramb? exp) (analyze-ramb exp))
        ((application? exp) (analyze-application exp))
        (else
         (error "Unknown expression type -- ANALYZE" exp))))

(define (amb? exp) (tagged-list? exp 'amb))
(define (ramb? exp) (tagged-list? exp 'ramb))
(define (amb-choices exp) (cdr exp))

(define (analyze-self-evaluating exp)
  (lambda (env succeed fail)
    (succeed exp fail)))

(define (analyze-quoted exp)
  (let ((qval (text-of-quotation exp)))
    (lambda (env succeed fail)
      (succeed qval fail))))

(define (analyze-variable exp)
  (lambda (env succeed fail)
    (succeed (lookup-variable-value exp env)
             fail)))

(define (analyze-lambda exp)
  (let ((vars (lambda-parameters exp))
        (bproc (analyze-sequence (lambda-body exp))))
    (lambda (env succeed fail)
      (succeed (make-procedure vars bproc env)
               fail))))

(define (analyze-if exp)
  (let ((pproc (analyze (if-predicate exp)))
        (cproc (analyze (if-consequent exp)))
        (aproc (analyze (if-alternative exp))))
    (lambda (env succeed fail)
      (pproc env
             ;; success continuation for evaluating the predicate to
             ;; obtain pred-value
             (lambda (pred-value fail2)
               (if (true? pred-value)
                   (cproc env succeed fail2)
                   (aproc env succeed fail2)))
             ;; failure continuation for evaluating the predicate
             fail))))

(define (if-fail? exp) (tagged-list? exp 'if-fail))
(define if-fail-action cadr)
(define if-fail-alternative caddr)

(define (analyze-if-fail exp)
  (let ((act-proc (analyze (if-fail-action exp)))
        (alt-proc (analyze (if-fail-alternative exp))))
    (lambda (env succeed fail)
      (act-proc env
                succeed
                (lambda ()
                  (alt-proc env succeed fail))))))

(define (if-fail-only? exp) (tagged-list? exp 'if-fail-only))
(define if-fail-only-test cadr)
(define if-fail-only-result caddr)

(define (analyze-if-fail-only exp)
  (let ((test-proc (analyze (if-fail-only-test exp)))
        (res-proc (analyze (if-fail-only-result exp))))
    (lambda (env succeed fail)
      (test-proc env
                 (lambda (test fail2)
                   (fail))
                 (lambda ()
                   (res-proc env
                             (lambda (res fail2)
                               (succeed res fail2))
                             fail))))))

(define (if-succeed-only? exp) (tagged-list? exp 'if-succeed-only))
(define if-succeed-only-test cadr)
(define if-succeed-only-result caddr)

(define (analyze-if-succeed-only exp)
  (let ((test-proc (analyze (if-succeed-only-test exp)))
        (res-proc (analyze (if-succeed-only-result exp))))
    (lambda (env succeed fail)
      (test-proc env
                 (lambda (test fail2)
                   (res-proc env
                             (lambda (res fail3)
                               (succeed res fail3))
                             fail2))
                 fail))))

(define (analyze-sequence exps)
  (define (sequentially a b)
    (lambda (env succeed fail)
      (a env
         ;; success continuation for calling a
         (lambda (a-value fail2)
           (b env succeed fail2))
         ;; failure continuation for calling a
         fail)))
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
        first-proc
        (loop (sequentially first-proc (car rest-procs))
              (cdr rest-procs))))
  (let ((procs (map analyze exps)))
    (when (null? procs)
      (error "Empty sequence -- ANALYZE"))
    (loop (car procs) (cdr procs))))

(define (and? exp) (tagged-list? exp 'and))
(define (or? exp) (tagged-list? exp 'or))
(define (logic-actions exps) (cdr exps))

(define (analyze-logic exps stop? init)
  (define (sequentially a b)
    (lambda (env succeed fail)
      (a env
         (lambda (a-value fail2)
           (if (stop? a-value)
               (b env succeed fail2)
               (succeed (not init) fail2)))
         fail)))
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
        first-proc
        (loop (sequentially first-proc (car rest-procs))
              (cdr rest-procs))))
  (loop (lambda (env succeed fail)
          (succeed init fail))
        (map analyze exps)))

(define (analyze-and exps)
  (analyze-logic exps (lambda (x) x) true))

(define (analyze-or exps)
  (analyze-logic exps not false))

(define (analyze-definition exp)
  (let ((var (definition-variable exp))
        (vproc (analyze (definition-value exp))))
    (lambda (env succeed fail)
      (vproc env
             (lambda (val fail2)
               (define-variable! var val env)
               (succeed 'ok fail2))
             fail))))

(define (analyze-assignment exp)
  (let ((var (assignment-variable exp))
        (vproc (analyze (assignment-value exp))))
    (lambda (env succeed fail)
      (vproc env
             (lambda (val fail2)        ; *1*
               (let ((old-value (lookup-variable-value var env)))
                 (set-variable-value! var val env)
                 (succeed 'ok
                          (lambda ()    ; *2*
                            (set-variable-value! var
                                                 old-value
                                                 env)
                            (fail2)))))
             fail))))

(define (analyze-assign-pair exp access assign!)
  (let ((varproc (analyze (assignment-variable exp)))
        (valproc (analyze (assignment-value exp))))
    (lambda (env succeed fail)
      (valproc env
               (lambda (val fail2)
                 (varproc env
                          (lambda (pair fail3)
                            (let ((old-val (access pair)))
                              (assign! pair val)
                              (succeed 'ok
                                       (lambda ()
                                         (assign! pair old-val)
                                         (fail3)))))
                          fail2))
               fail))))

(define (permanent-assignment? exp)
  (tagged-list? exp 'permanent-set!))

(define (analyze-perm-assign exp)
  (let ((var (assignment-variable exp))
        (vproc (analyze (assignment-value exp))))
    (lambda (env succeed fail)
      (vproc env
             (lambda (val fail2)
               (set-variable-value! var val env)
               (succeed 'ok fail2))
             fail))))

(define (analyze-application exp)
  (let ((fproc (analyze (operator exp)))
        (aprocs (map analyze (operands exp))))
    (lambda (env succeed fail)
      (fproc env
             (lambda (proc fail2)
               (get-args aprocs
                         env
                         (lambda (args fail3)
                           (execute-application
                            proc args succeed fail3))
                         fail2))
             fail))))

(define (get-args aprocs env succeed fail)
  (if (null? aprocs)
      (succeed '() fail)
      ((car aprocs)
       env
       ;; success continuation for this aproc
       (lambda (arg fail2)
         (get-args (cdr aprocs)
                   env
                   ;; success continuation for recursive
                   ;; call to get-args
                   (lambda (args fail3)
                     (succeed (cons arg args)
                              fail3))
                   fail2))
       fail)))

(define (execute-application proc args succeed fail)
  (cond ((primitive-procedure? proc)
         (succeed (apply-primitive-procedure proc args)
                  fail))
        ((compound-procedure? proc)
         ((procedure-body proc)
          (extend-environment (procedure-parameters proc)
                              args
                              (procedure-environment proc))
          succeed
          fail))
        (else
         (error
          "Unknown procedure type -- EXECUTE-APPLICATION"
          proc))))

(define (analyze-amb exp)
  (let ((cprocs (map analyze (amb-choices exp))))
    (lambda (env succeed fail)
      (define (try-next choices)
        (if (null? choices)
            (fail)
            ((car choices)
             env
             succeed
             (lambda ()
               (try-next (cdr choices))))))
      (try-next cprocs))))

(define (analyze-ramb exp)
  (let* ((cprocs (map analyze (amb-choices exp)))
         (len (length cprocs)))
    (define (choose! i head-ptr)
      (if (zero? i)
          (let ((choice (cadr head-ptr)))
            (set-cdr! head-ptr (cddr head-ptr))
            (set! len (- len 1))
            choice)
          (choose! (- i 1) (cdr head-ptr))))
    (lambda (env succeed fail)
      (define (try-next)
        (if (zero? len)
            (fail)
            (let ((i (random len)))
              (if (zero? i)
                  (let ((c (car cprocs)))
                    (set! cprocs (cdr cprocs))
                    (set! len (- len 1))
                    (c env succeed try-next))
                  ((choose! (- i 1) cprocs) env succeed try-next)))))
      (try-next))))

(define input-prompt ";;; Amb-Eval input:")
(define output-prompt ";;; Amb-Eval value:")

(define (driver-loop)
  (define (internal-loop try-again)
    (prompt-for-input input-prompt)
    (let ((input (read)))
      (if (eq? input 'try-again)
          (try-again)
          (begin
            (newline)
            (display ";;; Starting a new problem ")
            (ambeval input
                     the-global-environment
                     ;; ambeval success
                     (lambda (val next-alternative)
                       (announce-output output-prompt)
                       (user-print val)
                       (internal-loop next-alternative))
                     ;; ambeval failure
                     (lambda ()
                       (announce-output
                        ";;; There are no more values of")
                       (user-print input)
                       (driver-loop)))))))
  (internal-loop
   (lambda ()
     (newline)
     (display ";;; There is no current problem")
     (driver-loop))))