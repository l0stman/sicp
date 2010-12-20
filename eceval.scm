;;; Explicit-control evaluator
(require r5rs/init)
(load "eval.scm")
(load "regm.scm")

(define (empty-arglist) '())

(define (adjoin-arg arg arglist)
  (append arglist (list arg)))

(define (last-operand? ops)
  (null? (cdr ops)))

(define the-global-environment (setup-environment))
(define (get-global-environment)
  the-global-environment)

(define (make-lex-add frame-num disp-num)
  (list frame-num disp-num))
(define (frame-num lex-add) (car lex-add))
(define (disp-num lex-add) (cadr lex-add))

(define (lexical-address-lookup lex-add env)
  (define (err)
    (error "unbound address -- LEXICAL-ADDRESS-LOOKUP"
           lex-add))
  (define (nth n lst)
    (cond ((null? lst) (err))
          ((zero? n) (car lst))
          (else (nth (- n 1) (cdr lst)))))
  (let* ((frame (nth (frame-num lex-add) env))
         (val
          (nth (disp-num lex-add)
               (frame-values frame))))
    (if (eq? val '*unassigned*) (err) val)))

(define (lexical-address-set! lex-add val env)
  (define (nthcdr n lst)
    (cond ((null? lst)
           (error
            "unbound address -- LEXICAL-ADDRESS-SET!"
            lex-add))
          ((zero? n) lst)
          (else (nthcdr (- n 1) (cdr lst)))))
  (let ((frame
         (car (nthcdr (frame-num lex-add) env))))
    (set-car!
     (nthcdr (disp-num lex-add)
             (frame-values frame))
     val)))

(define open-coded-primitives '(+ - * /))
(define (open-coded-primitive? op)
  (memq op open-coded-primitives))
(define (drop-open-coded-primitive op)
  (define (drop lst)
    (cond ((null? lst) '())
          ((eq? (car lst) op) (drop (cdr lst)))
          (else (cons (car lst)
                      (drop (cdr lst))))))
  (set! open-coded-primitives
        (drop open-coded-primitives)))

(define (lookup-in-globenv var)
  (lookup-variable-value var the-global-environment))

(define (set-global-environment! var val)
  (set-variable-value! var val the-global-environment))

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (when (and (eq? env the-global-environment)
                        (open-coded-primitive? var))
               (drop-open-coded-primitive var))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (when (and (eq? env the-global-environment)
                        (open-coded-primitive? var))
               (drop-open-coded-primitive var))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (make-compiled-procedure entry env)
  (list 'compiled-procedure entry env))
(define (compiled-procedure? proc)
  (tagged-list? proc 'compiled-procedure))
(define (compiled-procedure-entry c-proc) (cadr c-proc))
(define (compiled-procedure-env c-proc) (caddr c-proc))

(define (user-print object)
  (cond ((compound-procedure? object)
         (display (list 'compound-procedure
                        (procedure-parameters object)
                        (procedure-body object)
                        '<procedure-env>)))
        ((compiled-procedure? object)
         (display '<compiled-procedure>))
        (else (display object))))

(define eceval-operations
  (list (list 'prompt-for-input prompt-for-input)
        (list 'read read)
        (list 'get-global-environment get-global-environment)
        (list 'announce-output announce-output)
        (list 'user-print user-print)
        (list 'self-evaluating? self-evaluating?)
        (list 'variable? variable?)
        (list 'quoted? quoted?)
        (list 'assignment? assignment?)
        (list 'definition? definition?)
        (list 'if? if?)
        (list 'lambda? lambda?)
        (list 'begin? begin?)
        (list 'application? application?)
        (list 'lookup-variable-value lookup-variable-value)
        (list 'text-of-quotation text-of-quotation)
        (list 'lambda-parameters lambda-parameters)
        (list 'lambda-body lambda-body)
        (list 'make-procedure make-procedure)
        (list 'operands operands)
        (list 'operator operator)
        (list 'empty-arglist empty-arglist)
        (list 'no-operands? no-operands?)
        (list 'first-operand first-operand)
        (list 'last-operand? last-operand?)
        (list 'adjoin-arg adjoin-arg)
        (list 'rest-operands rest-operands)
        (list 'adjoin-arg adjoin-arg)
        (list 'primitive-procedure? primitive-procedure?)
        (list 'compound-procedure? compound-procedure?)
        (list 'procedure-parameters procedure-parameters)
        (list 'procedure-environment procedure-environment)
        (list 'extend-environment extend-environment)
        (list 'procedure-body procedure-body)
        (list 'begin-actions begin-actions)
        (list 'first-exp first-exp)
        (list 'last-exp? last-exp?)
        (list 'rest-exps rest-exps)
        (list 'if-predicate if-predicate)
        (list 'true? true?)
        (list 'false? false?)
        (list 'if-alternative if-alternative)
        (list 'if-consequent if-consequent)
        (list 'assignment-variable assignment-variable)
        (list 'assignment-value assignment-value)
        (list 'set-variable-value! set-variable-value!)
        (list 'definition-variable definition-variable)
        (list 'definition-value definition-value)
        (list 'define-variable! define-variable!)
        (list 'user-print user-print)
        (list 'apply-primitive-procedure apply-primitive-procedure)
        (list 'cond? cond?)
        (list 'cond->if cond->if)
        (list 'let? let?)
        (list 'let->combination let->combination)
        (list 'lexical-address-lookup lexical-address-lookup)
        (list 'lexical-address-set! lexical-address-set!)
        (list 'lookup-in-globenv lookup-in-globenv)
        (list 'set-global-environment! set-global-environment!)
        (list 'make-compiled-procedure make-compiled-procedure)
        (list 'compiled-procedure? compiled-procedure?)
        (list 'compiled-procedure-entry compiled-procedure-entry)
        (list 'compiled-procedure-env compiled-procedure-env)
        (list 'list list)
        (list 'cons cons)
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '/ /)))

(define eceval
  (make-machine
   eceval-operations
   '((assign compapp (label COMPOUND-APPLY))
     (branch (label EXTERNAL-ENTRY))    ; branches if flag is set
     READ-EVAL-PRINT-LOOP
     (perform (op initialize-stack))
     (perform (op prompt-for-input) (const ";;; EC-EVAL input:"))
     (assign exp (op read))
     (assign env (op get-global-environment))
     (assign continue (label PRINT-RESULT))
     (goto (label EVAL-DISPATCH))
     PRINT-RESULT
     (perform (op print-statistics))
     (perform (op announce-output) (const ";;; EC-Eval value:"))
     (perform (op user-print) (reg val))
     (goto (label READ-EVAL-PRINT-LOOP))

     EXTERNAL-ENTRY
     (perform (op initialize-stack))
     (assign env (op get-global-environment))
     (assign continue (label PRINT-RESULT))
     (goto (reg val))

     EVAL-DISPATCH
     (test (op self-evaluating?) (reg exp))
     (branch (label EV-SELF-EVAL))
     (test (op variable?) (reg exp))
     (branch (label EV-VARIABLE))
     (test (op quoted?) (reg exp))
     (branch (label EV-QUOTED))
     (test (op assignment?) (reg exp))
     (branch (label EV-ASSIGNMENT))
     (test (op definition?) (reg exp))
     (branch (label EV-DEFINITION))
     (test (op if?) (reg exp))
     (branch (label EV-IF))
     (test (op lambda?) (reg exp))
     (branch (label EV-LAMBDA))
     (test (op begin?) (reg exp))
     (branch (label EV-BEGIN))
     (test (op cond?) (reg exp))
     (branch (label EV-COND))
     (test (op let?) (reg exp))
     (branch (label EV-LET))
     (test (op application?) (reg exp))
     (branch (label EV-APPLICATION))
     (goto (label UNKNOWN-EXPRESSION-TYPE))

     EV-SELF-EVAL
     (assign val (reg exp))
     (goto (reg continue))

     EV-VARIABLE
     (assign val (op lookup-variable-value) (reg exp) (reg env))
     (goto (reg continue))

     EV-QUOTED
     (assign val (op text-of-quotation) (reg exp))
     (goto (reg continue))

     EV-LAMBDA
     (assign unev (op lambda-parameters) (reg exp))
     (assign exp (op lambda-body) (reg exp))
     (assign val (op make-procedure) (reg unev) (reg exp) (reg env))
     (goto (reg continue))

     EV-APPLICATION
     (save continue)
     (assign unev (op operands) (reg exp))
     (assign exp (op operator) (reg exp))
     (test (op variable?) (reg exp))
     (branch (label EV-OPERATOR-VARIABLE))
     (save env)
     (save unev)
     (assign continue (label EV-APPL-DID-OPERATOR))
     (goto (label EVAL-DISPATCH))
     EV-OPERATOR-VARIABLE
     (assign proc (op lookup-variable-value) (reg exp) (reg env))
     (goto (label EV-APPL-PROC-ASSIGNED))
     EV-APPL-DID-OPERATOR
     (restore unev)                     ; the operands
     (restore env)
     (assign proc (reg val))            ; the operator
     EV-APPL-PROC-ASSIGNED
     (assign argl (op empty-arglist))
     (test (op no-operands?) (reg unev))
     (branch (label APPLY-DISPATCH))
     (save proc)
     EV-APPL-OPERAND-LOOP
     (save argl)
     (assign exp (op first-operand) (reg unev))
     (test (op last-operand?) (reg unev))
     (branch (label EV-APPL-LAST-ARG))
     (save env)
     (save unev)
     (assign continue (label EV-APPL-ACCUMULATE-ARG))
     (goto (label EVAL-DISPATCH))
     EV-APPL-ACCUMULATE-ARG
     (restore unev)
     (restore env)
     (restore argl)
     (assign argl (op adjoin-arg) (reg val) (reg argl))
     (assign unev (op rest-operands) (reg unev))
     (goto (label EV-APPL-OPERAND-LOOP))
     EV-APPL-LAST-ARG
     (assign continue (label EV-APPL-ACCUM-LAST-ARG))
     (goto (label EVAL-DISPATCH))
     EV-APPL-ACCUM-LAST-ARG
     (restore argl)
     (assign argl (op adjoin-arg) (reg val) (reg argl))
     (restore proc)
     (goto (label APPLY-DISPATCH))

     APPLY-DISPATCH
     (test (op primitive-procedure?) (reg proc))
     (branch (label PRIMITIVE-APPLY))
     (test (op compound-procedure?) (reg proc))
     (branch (label COMPOUND-APPLY))
     (test (op compiled-procedure?) (reg proc))
     (branch (label COMPILED-APPLY))
     (goto (label UNKNOWN-PROCEDURE-TYPE))

     PRIMITIVE-APPLY
     (assign val (op apply-primitive-procedure) (reg proc) (reg argl))
     (restore continue)
     (goto (reg continue))

     COMPOUND-APPLY
     (assign unev (op procedure-parameters) (reg proc))
     (assign env (op procedure-environment) (reg proc))
     (assign env (op extend-environment) (reg unev) (reg argl) (reg env))
     (assign unev (op procedure-body) (reg proc))
     (goto (label EV-SEQUENCE))

     COMPILED-APPLY
     (restore continue)
     (assign val (op compiled-procedure-entry) (reg proc))
     (goto (reg val))

     EV-BEGIN
     (assign unev (op begin-actions) (reg exp))
     (save continue)
     (goto (label EV-SEQUENCE))

     EV-SEQUENCE
     (assign exp (op first-exp) (reg unev))
     (test (op last-exp?) (reg unev))
     (branch (label EV-SEQUENCE-LAST-EXP))
     (save unev)
     (save env)
     (assign continue (label EV-SEQUENCE-CONTINUE))
     (goto (label EVAL-DISPATCH))
     EV-SEQUENCE-CONTINUE
     (restore env)
     (restore unev)
     (assign unev (op rest-exps) (reg unev))
     (goto (label EV-SEQUENCE))
     EV-SEQUENCE-LAST-EXP
     (restore continue)
     (goto (label EVAL-DISPATCH))

     EV-IF
     (save exp)                         ; save expression for later
     (save env)
     (save continue)
     (assign continue (label EV-IF-DECIDE))
     (assign exp (op if-predicate) (reg exp))
     (goto (label EVAL-DISPATCH))       ; evaluate the predicate
     EV-IF-DECIDE
     (restore continue)
     (restore env)
     (restore exp)
     (test (op true?) (reg val))
     (branch (label EV-IF-CONSEQUENT))
     EV-IF-ALTERNATIVE
     (assign exp (op if-alternative) (reg exp))
     (goto (label EVAL-DISPATCH))
     EV-IF-CONSEQUENT
     (assign exp (op if-consequent) (reg exp))
     (goto (label EVAL-DISPATCH))

     EV-ASSIGNMENT
     (assign unev (op assignment-variable) (reg exp))
     (save unev)                        ; save variable for later
     (assign exp (op assignment-value) (reg exp))
     (save env)
     (save continue)
     (assign continue (label EV-ASSIGNMENT-1))
     (goto (label EVAL-DISPATCH))       ; evaluate he assignment value
     EV-ASSIGNMENT-1
     (restore continue)
     (restore env)
     (restore unev)
     (perform
      (op set-variable-value!) (reg unev) (reg val) (reg env))
     (assign val (const ok))
     (goto (reg continue))

     EV-DEFINITION
     (assign unev (op definition-variable) (reg exp))
     (save unev)                        ; save variable for later
     (assign exp (op definition-value) (reg exp))
     (save env)
     (save continue)
     (assign continue (label EV-DEFINITION-1))
     (goto (label EVAL-DISPATCH))      ; evaluate the definition value
     EV-DEFINITION-1
     (restore continue)
     (restore env)
     (restore unev)
     (perform
      (op define-variable!) (reg unev) (reg val) (reg env))
     (assign val (const ok))
     (goto (reg continue))

     EV-COND
     (assign exp (op cond->if) (reg exp))
     (goto (label EVAL-DISPATCH))

     EV-LET
     (assign exp (op let->combination) (reg exp))
     (goto (label EVAL-DISPATCH))

     UNKNOWN-EXPRESSION-TYPE
     (assign val (const unknown-expression-type-error))
     (goto (label signal-error))
     UNKNOWN-PROCEDURE-TYPE
     (restore continue)         ; clean up stack (from apply-dispatch)
     (assign val (const unknown-procedure-type-error))
     (goto (label SIGNAL-ERROR))
     SIGNAL-ERROR
     (perform (op user-print) (reg val))
     (goto (label READ-EVAL-PRINT-LOOP)))))

(define (start-eceval)
  (set! the-global-environment (setup-environment))
  (set-register-contents! eceval 'flag #f)
  (start eceval))