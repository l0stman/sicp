;;; Register machine simulator with garbage collector.
(require r5rs/init)

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

(define (make-machine ops controller-text)
  (let ((machine (make-new-machine)))
    ((machine 'install-operations) ops)
    ((machine 'install-instruction-sequence)
     (assemble controller-text machine))
    machine))

(define (make-register name)
  (let ((contents '*unassigned*))
    (define (dispatch message)
      (cond ((eq? message 'get) contents)
            ((eq? message 'set)
             (lambda (value) (set! contents value)))
            (else
             (error "Unknown request -- REGISTER" message))))
    dispatch))

(define (get-contents register) (register 'get))
(define (set-contents! register value)
  ((register 'set) value))

(define (make-new-machine)
  (let ((register-table '())
        (memsiz 1024))
    (define (allocate-register name)
      (if (assoc name register-table)
          (error "Multiply defined register: " name)
          (let ((reg (make-register name)))
            (set! register-table
                  (cons (list name reg) register-table))
            reg)))
    (define (lookup-register name)
      (let ((val (assoc name register-table)))
        (if val
            (cadr val)
            (allocate-register name))))
    (let ((pc (allocate-register 'pc))
          (flag (allocate-register 'flag))
          (the-stack (allocate-register 'the-stack))
          (the-cars (make-vector memsiz))
          (the-cdrs (make-vector memsiz))
          (new-cars (make-vector memsiz))
          (new-cdrs (make-vector memsiz))
          (free 0))
      (define (index-to-pair index)
        (list 'pointer-to-pair index))
      (define (pointer-to-pair? p)
        (tagged-list? p 'pointer-to-pair))
      (define (pair-index p)
        (if (pointer-to-pair? p)
            (cadr p)
            (error "Not a pair" p)))
      (define (gc)
        ;; Stop and copy garbage collector
        (define (broken-heart? x) (eq? x 'broken-heart))
        (define (check-overflow)
          (when (= free memsiz)
            (error "Heap overflow -- GC")))
        (define (relocate old)
          (if (pointer-to-pair? old)
              (let* ((old-index (pair-index old))
                     (oldcar (vector-ref the-cars old-index)))
                (if (broken-heart? oldcar)
                    (vector-ref the-cdrs old-index)
                    (begin
                      (check-overflow)
                      (let ((new (index-to-pair free)))
                        (vector-set! new-cars free oldcar)
                        (vector-set! new-cdrs
                                     free
                                     (vector-ref the-cdrs old-index))
                        (vector-set! the-cars old-index 'broken-heart)
                        (vector-set! the-cdrs old-index new)
                        (set! free (+ free 1))
                        new))))
              old))
        (define (gc-loop scan)
          (when (< scan free)
            (vector-set! new-cars
                         scan
                         (relocate (vector-ref new-cars scan)))
            (vector-set! new-cdrs
                         scan
                         (relocate (vector-ref new-cdrs scan)))
            (gc-loop (+ scan 1))))
        (set! free 0)
        (for-each (lambda (entry)
                    (let ((root (cadr entry))
                          (scan free))
                      (set-contents! root (relocate (get-contents root)))
                      (gc-loop scan)))
                  register-table)
        (check-overflow)
        (let ((tmp the-cdrs))
          (set! the-cdrs new-cdrs)
          (set! new-cdrs tmp)
          (set! tmp the-cars)
          (set! the-cars new-cars)
          (set! new-cars tmp)))
      (define (new-pair car cdr)
        (when (= free memsiz) (gc))
        (vector-set! the-cars free car)
        (vector-set! the-cdrs free cdr)
        (set! free (+ free 1))
        (index-to-pair (- free 1)))
      (define (first pair)
        (vector-ref the-cars (pair-index pair)))
      (define (rest pair)
        (vector-ref the-cdrs (pair-index pair)))
      (let ((the-instruction-sequence '())
            (the-ops
             (list (list 'initialize-stack
                         (lambda () (set-contents! the-stack '())))
                   (list 'car first)
                   (list 'cdr rest)
                   (list 'set-car!
                         (lambda (pair val)
                           (vector-set! the-cars
                                        (pair-index pair)
                                        val)))
                   (list 'set-cdr!
                         (lambda (pair val)
                           (vector-set! the-cdrs
                                        (pair-index pair)
                                        val)))
                   (list 'cons new-pair)
                   (list 'pair? pointer-to-pair?))))
        (define (execute)
          (let ((insts (get-contents pc)))
            (if (null? insts)
                'done
                (begin
                  ((instruction-execution-proc (car insts)))
                  (execute)))))
        (define (dispatch message)
          (cond ((eq? message 'start)
                 (set-contents! pc the-instruction-sequence)
                 (set! free 0)
                 (execute))
                ((eq? message 'install-instruction-sequence)
                 (lambda (seq) (set! the-instruction-sequence seq)))
                ((eq? message 'allocate-register) allocate-register)
                ((eq? message 'get-register) lookup-register)
                ((eq? message 'install-operations)
                 (lambda (ops) (set! the-ops (append the-ops ops))))
                ((eq? message 'push)
                 (lambda (val)
                   (set-contents! the-stack
                                  (new-pair val
                                            (get-contents the-stack)))))
                ((eq? message 'pop)
                 (let ((s (get-contents the-stack)))
                   (if (null? s)
                       (error "empty stack -- POP")
                       (let ((top (first s)))
                         (set-contents! the-stack (rest s))
                         top))))
                ((eq? message 'operations) the-ops)
                ((eq? message 'dump-memory)
                 (let loop ((i 0))
                   (when (< i free)
                     (display (format "~a: ~a ~a~%"
                                      i
                                      (vector-ref the-cars i)
                                      (vector-ref the-cdrs i)))
                     (loop (+ i 1)))))
                (else (error "Unknown request -- MACHINE" message))))
        dispatch))))

(define (start machine)
  (machine 'start))
(define (get-register-contents machine register-name)
  (get-contents (get-register machine register-name)))
(define (set-register-contents! machine register-name value)
  (set-contents! (get-register machine register-name) value)
  'done)

(define (get-register machine reg-name)
  ((machine 'get-register) reg-name))

(define (assemble controller-text machine)
  (extract-labels controller-text
                  (lambda (insts labels)
                    (update-insts! insts labels machine)
                    insts)))

(define (extract-labels text receive)
  (if (null? text)
      (receive '() '())
      (extract-labels
       (cdr text)
       (lambda (insts labels)
         (let ((next-inst (car text)))
           (cond ((not (symbol? next-inst))
                  (receive (cons (make-instruction next-inst)
                                 insts)
                           labels))
                 ((assoc next-inst labels)
                  (error "label indicates two different locations"
                         next-inst))
                 (else
                  (receive insts
                      (cons (make-label-entry next-inst
                                              insts)
                            labels)))))))))

(define (update-insts! insts labels machine)
  (let ((pc (get-register machine 'pc))
        (flag (get-register machine 'flag))
        (ops (machine 'operations)))
    (for-each
     (lambda (inst)
       (set-instruction-execution-proc!
        inst
        (make-execution-procedure
         (instruction-text inst) labels machine
         pc flag ops)))
     insts)))

(define (make-instruction text)
  (cons text '()))
(define (instruction-text inst)
  (car inst))
(define (instruction-execution-proc inst)
  (cdr inst))
(define (set-instruction-execution-proc! inst proc)
  (set-cdr! inst proc))

(define (make-label-entry label-name insts)
  (cons label-name insts))

(define (lookup-label labels label-name)
  (let ((val (assoc label-name labels)))
    (if val
        (cdr val)
        (error "Undefined label -- ASSEMBLE" label-name))))

(define (make-execution-procedure inst labels machine
                                  pc flag ops)
  (cond ((eq? (car inst) 'assign)
         (make-assign inst machine labels ops pc))
        ((eq? (car inst) 'test)
         (make-test inst machine labels ops flag pc))
        ((eq? (car inst) 'branch)
         (make-branch inst machine labels flag pc))
        ((eq? (car inst) 'goto)
         (make-goto inst machine labels pc))
        ((eq? (car inst) 'save)
         (make-save inst machine pc))
        ((eq? (car inst) 'restore)
         (make-restore inst machine pc))
        ((eq? (car inst) 'perform)
         (make-perform inst machine labels ops pc))
        (else (error "Unknown instruction type -- ASSEMBLE"
                     inst))))

(define (make-assign inst machine labels operations pc)
  (let ((target (get-register machine (assign-reg-name inst)))
        (value-exp (assign-value-exp inst)))
    (let ((value-proc
           (if (operation-exp? value-exp)
               (make-operation-exp
                value-exp machine labels operations)
               (make-primitive-exp
                (car value-exp) machine labels))))
      (lambda ()                        ; execution procedure for assign
        (set-contents! target (value-proc))
        (advance-pc pc)))))

(define (assign-reg-name assign-instruction)
  (cadr assign-instruction))
(define (assign-value-exp assign-instruction)
  (cddr assign-instruction))

(define (advance-pc pc)
  (set-contents! pc (cdr (get-contents pc))))

(define (make-test inst machine labels operations flag pc)
  (let ((condition (test-condition inst)))
    (if (operation-exp? condition)
        (let ((condition-proc
               (make-operation-exp
                condition machine labels operations)))
          (lambda ()
            (set-contents! flag (condition-proc))
            (advance-pc pc)))
        (error "Bad TEST instruction -- ASSEMBLE" inst))))

(define (test-condition test-instruction)
  (cdr test-instruction))

(define (make-branch inst machine labels flag pc)
  (let ((dest (branch-dest inst)))
    (if (label-exp? dest)
        (let ((insts
               (lookup-label labels (label-exp-label dest))))
          (lambda ()
            (if (get-contents flag)
                (set-contents! pc insts)
                (advance-pc pc))))
        (error "Bad BRANCH instruction -- ASSEMBLE" inst))))

(define (branch-dest branch-instruction)
  (cadr branch-instruction))

(define (make-goto inst machine labels pc)
  (let ((dest (goto-dest inst)))
    (cond ((label-exp? dest)
           (let ((insts
                  (lookup-label labels
                                (label-exp-label dest))))
             (lambda () (set-contents! pc insts))))
          ((register-exp? dest)
           (let ((reg
                  (get-register machine
                                (register-exp-reg dest))))
             (lambda ()
               (set-contents! pc (get-contents reg)))))
          (else (error "Bad GOTO instruction -- ASSEMBLE"
                       inst)))))
(define (goto-dest goto-instruction)
  (cadr goto-instruction))

(define (make-save inst machine pc)
  (let ((reg (get-register machine
                           (stack-inst-reg-name inst))))
    (lambda ()
      ((machine 'push) (get-contents reg))
      (advance-pc pc))))
(define (make-restore inst machine pc)
  (let ((reg (get-register machine
                           (stack-inst-reg-name inst))))
    (lambda ()
      (set-contents! reg (machine 'pop))
      (advance-pc pc))))
(define (stack-inst-reg-name stack-instruction)
  (cadr stack-instruction))

(define (make-perform inst machine labels operations pc)
  (let ((action (perform-action inst)))
    (if (operation-exp? action)
        (let ((action-proc
               (make-operation-exp
                action machine labels operations)))
          (lambda ()
            (action-proc)
            (advance-pc pc)))
        (error "Bad PERFORM instruction -- ASSEMBLE" inst))))
(define (perform-action inst) (cdr inst))

(define (make-primitive-exp exp machine labels)
  (cond ((constant-exp? exp)
         (let ((c (constant-exp-value exp)))
           (lambda () c)))
        ((label-exp? exp)
         (let ((insts
                (lookup-label labels
                              (label-exp-label exp))))
           (lambda () insts)))
        ((register-exp? exp)
         (let ((r (get-register machine
                                (register-exp-reg exp))))
           (lambda () (get-contents r))))
        (else
         (error "Unknown expression type -- ASSEMBLE" exp))))

(define (register-exp? exp) (tagged-list? exp 'reg))
(define (register-exp-reg exp) (cadr exp))
(define (constant-exp? exp) (tagged-list? exp 'const))
(define (constant-exp-value exp) (cadr exp))
(define (label-exp? exp) (tagged-list? exp 'label))
(define (label-exp-label exp) (cadr exp))

(define (make-operation-exp exp machine labels operations)
  (let ((op (lookup-prim (operation-exp-op exp) operations))
        (aprocs
         (map (lambda (e)
                (if (label-exp? e)
                    (error "Can't operate on labels -- MAKE-OPERATION-EXP" exp)
                    (make-primitive-exp e machine labels)))
              (operation-exp-operands exp))))
    (lambda ()
      (apply op (map (lambda (p) (p)) aprocs)))))

(define (operation-exp? exp)
  (and (pair? exp) (tagged-list? (car exp) 'op)))
(define (operation-exp-op operation-exp)
  (cadr (car operation-exp)))
(define (operation-exp-operands operation-exp)
  (cdr operation-exp))

(define (lookup-prim symbol operations)
  (let ((val (assoc symbol operations)))
    (if val
        (cadr val)
        (error "Unknown operation -- ASSEMBLE" symbol))))