;;; Lazy Explicit-control evaluator
(require r5rs/init)
(load "lazy-eval.scm")
(load "regm.scm")

(define (empty-arglist) '())

(define (adjoin-arg arg arglist)
  (append arglist (list arg)))

(define (last-operand? ops)
  (null? (cdr ops)))

(define the-global-environment (setup-environment))
(define (get-global-environment)
  the-global-environment)

(define lazy-eceval-operations
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
        (list 'cond? cond?)
        (list 'let? let?)
        (list 'application? application?)
        (list 'thunk? thunk?)
        (list 'evaluated-thunk? evaluated-thunk?)
        (list 'thunk-exp thunk-exp)
        (list 'thunk-env thunk-env)
        (list 'set-car! set-car!)
        (list 'cdr cdr)
        (list 'set-car! set-car!)
        (list 'set-cdr! set-cdr!)
        (list 'thunk-value thunk-value)
        (list 'delay-it delay-it)
        (list 'lookup-variable-value lookup-variable-value)
        (list 'text-of-quotation text-of-quotation)
        (list 'lambda-parameters lambda-parameters)
        (list 'lambda-body lambda-body)
        (list 'make-procedure make-procedure)
        (list 'operands operands)
        (list 'operator operator)
        (list 'primitive-procedure? primitive-procedure?)
        (list 'compound-procedure? compound-procedure?)
        (list 'apply-primitive-procedure apply-primitive-procedure)
        (list 'procedure-parameters procedure-parameters)
        (list 'procedure-environment procedure-environment)
        (list 'extend-environment extend-environment)
        (list 'procedure-body procedure-body)
        (list 'empty-arglist empty-arglist)
        (list 'no-operands? no-operands?)
        (list 'first-operand first-operand)
        (list 'last-operand? last-operand?)
        (list 'adjoin-arg adjoin-arg)
        (list 'rest-operands rest-operands)
        (list 'adjoin-arg adjoin-arg)
        (list 'begin-actions begin-actions)
        (list 'first-exp first-exp)
        (list 'last-exp? last-exp?)
        (list 'rest-exps rest-exps)
        (list 'if-predicate if-predicate)
        (list 'true? true?)
        (list 'if-alternative if-alternative)
        (list 'if-consequent if-consequent)
        (list 'assignment-variable assignment-variable)
        (list 'assignment-value assignment-value)
        (list 'set-variable-value! set-variable-value!)
        (list 'definition-variable definition-variable)
        (list 'definition-value definition-value)
        (list 'define-variable! define-variable!)
        (list 'cond->if cond->if)
        (list 'let->combination let->combination)
        (list 'user-print user-print)))

(define lazy-eceval
  (make-machine
   lazy-eceval-operations
   '(READ-EVAL-PRINT-LOOP
     (perform (op initialize-stack))
     (perform (op prompt-for-input) (const ";;; LEC-EVAL input:"))
     (assign exp (op read))
     (assign env (op get-global-environment))
     (assign continue (label PRINT-RESULT))
     (goto (label ACTUAL-VALUE))
     PRINT-RESULT
     (perform (op announce-output) (const ";;; LEC-Eval value:"))
     (perform (op user-print) (reg val))
     (goto (label READ-EVAL-PRINT-LOOP))

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

     ACTUAL-VALUE
     (save continue)
     (assign continue (label FORCE-IT))
     (goto (label EVAL-DISPATCH))
     FORCE-IT
     (test (op thunk?) (reg val))
     (branch (label FORCE-IT-THUNK))
     (test (op evaluated-thunk?) (reg val))
     (branch (label THUNK-VALUE))
     (restore continue)
     (goto (reg continue))
     FORCE-IT-THUNK
     (save val)
     (assign exp (op thunk-exp) (reg val))
     (assign env (op thunk-env) (reg val))
     (assign continue (label FORCE-IT-GOT-VALUE))
     (goto (label ACTUAL-VALUE))
     FORCE-IT-GOT-VALUE
     (restore exp)                      ; object to force
     (perform (op set-car!) (reg exp) (const evaluated-thunk))
     (assign exp (op cdr) (reg exp))
     (perform (op set-car!) (reg exp) (reg val))
     (perform (op set-cdr!) (reg exp) (reg ()))
     (restore continue)
     (goto (reg continue))
     THUNK-VALUE
     (assign val (op thunk-value) (reg val))
     (restore continue)
     (goto (reg continue))

     DELAY-IT
     (assign val (op delay-it) (reg exp) (reg env))
     (goto (reg continue))

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
     (save env)
     (assign unev (op operands) (reg exp))
     (save unev)
     (assign exp (op operator) (reg exp))
     (assign continue (label EV-APPL-DID-OPERATOR))
     (goto (label ACTUAL-VALUE))
     EV-APPL-DID-OPERATOR
     (restore unev)                     ; the operands
     (restore env)
     (assign proc (reg val))            ; the operator
     (test (op primitive-procedure?) (reg proc))
     (branch (label PRIMITIVE-APPLY))
     (test (op compound-procedure?) (reg proc))
     (branch (label COMPOUND-APPLY))
     (goto (label UNKNOWN-PROCEDURE-TYPE))

     PRIMITIVE-APPLY
     (assign continue (label PRIM-APPLY-TO-ARGS))
     (assign exp (label ACTUAL-VALUE))
     (goto (label EV-APPL-OPERANDS))
     PRIM-APPLY-TO-ARGS
     (assign val (op apply-primitive-procedure) (reg proc) (reg argl))
     (restore continue)
     (goto (reg continue))

     COMPOUND-APPLY
     (assign continue (label COMP-APPL-TO-ARGS))
     (assign exp (label DELAY-IT))
     (goto (label EV-APPL-OPERANDS))
     COMP-APPL-TO-ARGS
     (assign unev (op procedure-parameters) (reg proc))
     (assign env (op procedure-environment) (reg proc))
     (assign env (op extend-environment) (reg unev) (reg argl) (reg env))
     (assign unev (op procedure-body) (reg proc))
     (goto (label EV-SEQUENCE))

     EV-APPL-OPERANDS
     (assign argl (op empty-arglist))
     (test (op no-operands?) (reg unev))
     (branch (label EV-APPL-NO-ARGS))
     (save continue)
     (save proc)
     (save exp)
     EV-APPL-OPERAND-LOOP
     (restore proc)                ; procedure to apply to the operand
     (assign exp (op first-operand) (reg unev))
     (test (op last-operand?) (reg unev))
     (branch (label EV-APPL-LAST-ARG))
     (save proc)
     (save argl)
     (save env)
     (save unev)
     (assign continue (label EV-APPL-ACCUMULATE-ARG))
     (goto (reg proc))
     EV-APPL-ACCUMULATE-ARG
     (restore unev)
     (restore env)
     (restore argl)
     (assign argl (op adjoin-arg) (reg val) (reg argl))
     (assign unev (op rest-operands) (reg unev))
     (goto (label EV-APPL-OPERAND-LOOP))
     EV-APPL-LAST-ARG
     (save argl)
     (assign continue (label EV-APPL-ACCUM-LAST-ARG))
     (goto (reg proc))
     EV-APPL-ACCUM-LAST-ARG
     (restore argl)
     (assign argl (op adjoin-arg) (reg val) (reg argl))
     (restore proc)
     (restore continue)
     EV-APPL-NO-ARGS
     (goto (reg continue))

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
     (goto (label ACTUAL-VALUE))        ; evaluate the predicate
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