;;; file: s450.scm
;;;
;;; Metacircular evaluator from chapter 4 of STRUCTURE AND
;;; INTERPRETATION OF COMPUTER PROGRAMS (2nd edition)
;;;
;;; Modified by kwn, 3/4/97
;;; Modified and commented by Carl Offner, 10/21/98 -- 10/12/04
;;; Modified and commented by J Tan, 10/24/17
;;;
;;; This code is the code for the metacircular evaluator as it appears
;;; in the textbook in sections 4.1.1-4.1.4, with the following
;;; changes:
;;;
;;; 1.  It uses #f and #t, not false and true, to be Scheme-conformant.
;;;
;;; 2.  Some function names were changed to avoid conflict with the
;;; underlying Scheme:
;;;
;;;       eval => xeval
;;;       apply => xapply
;;;       extend-environment => xtend-environment
;;;
;;; 3.  The driver-loop is called s450.
;;;
;;; 4.  The booleans (#t and #f) are classified as self-evaluating.
;;;
;;; 5.  These modifications make it look more like UMB Scheme:
;;;
;;;        The define special form evaluates to (i.e., "returns") the
;;;          variable being defined.
;;;        No prefix is printed before an output value.
;;;
;;; 6.  I changed "compound-procedure" to "user-defined-procedure".
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 xeval and xapply -- the kernel of the metacircular evaluator
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (xeval exp env)
  (let ((action (lookup-action (type-of exp))))
    (if (and (lookup-action (type-of exp))
             (pair? exp)) ;don't lookup ==> <special-form>; i.e: ==> if
        (action exp env)
        (cond ((self-evaluating? exp) exp)
              ((variable? exp)
               (cond ((to-be-ref? (lookup-variable-value exp env))
                      (ref-it (lookup-variable-value exp env)))
                     (else
                      (lookup-variable-value exp env))))
              ((application? exp)
               (xapply (xeval (operator exp) env)
                       (operands exp) 
                       env))
              (else
               (error "Unknown expression type -- XEVAL " exp))))))

(define (xapply procedure arguments env)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure
                                    (list-of-values arguments env)))
        ((user-defined-procedure? procedure)
         ;copy params into a new list so original params don't get modified
         (let ((new-params (list-copy (procedure-parameters procedure))))
           (scan-params new-params arguments env) ;scan for tagged params
           (eval-sequence                         ;and untag it
            (procedure-body procedure)
            (xtend-environment
             new-params
             (list-of-values arguments env)
             (procedure-environment procedure)))))
        (else
         (error "Unknown procedure type -- XAPPLY " procedure))))

;;; Handling procedure arguments

(define (list-of-values exps env)
  (cond ((no-operands? exps) '())
        ((or (thunk? (first-operand exps))
             (to-be-ref? (first-operand exps)))
         (cons (first-operand exps) ;don't eval if tagged
               (list-of-values (rest-operands exps) env)))
        (else
         (cons (xeval (first-operand exps) env)
               (list-of-values (rest-operands exps) env)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;    Special-forms handling
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; For inserting into the special-forms table

(define (insert! key value table)
  (let ((record (assoc key (cdr table))))
    (if record
        (set-cdr! record value)
        (set-cdr! table
                  (cons (cons key value) (cdr table)))))
  key)

;;; ==>((lookup 'define special-forms-table) '(define x 5)
;;;                                the-global-environment)
;;; x

(define (lookup key table)
  (let ((record (assoc key (cdr table))))
    (if record
        (cdr record)
        #f)))

;;; Make table function
;;; ==>(define test-table (make-table))

(define (make-table)
  (list '*table*))

;;;; Create the special-forms table

(define special-forms-table (make-table))

;;; These functions, called from install-special-form-packages, do
;;; the work of evaluating some of the special forms:

(define (eval-if exp env)
  (if (true? (xeval (if-predicate exp) env))
      (xeval (if-consequent exp) env)
      (xeval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps)
         (let ((last-value (xeval (first-exp exps) env)))
           (cond ((not (null? (cdr the-dynamic-environment)))
                  (set! the-dynamic-environment
                        (cdr the-dynamic-environment))))
           last-value))
        (else (xeval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (let ((name (assignment-variable exp))
        (to-be-ref (lookup-variable-value (assignment-variable exp) env)))
    (cond ((to-be-ref? to-be-ref) ;check if ref container
           (set-variable-value!
            (ref-exp to-be-ref)
            (xeval (assignment-value exp) env)
            (ref-env to-be-ref)))
          (else
           (set-variable-value!
            name
            (xeval (assignment-value exp) env)
            env)))
    name))    

(define (eval-definition exp env)
  (let ((name (definition-variable exp)))  
    (define-variable! name
      (xeval (definition-value exp) env)
      env)
  name))    

;;; Stream special-form
(define (elmt exp)
  (car (cdr exp)))
(define (strm exp)
  (car (cdr (cdr exp))))

(define (stream-car stream)
  (car stream))
(define (stream-cdr stream)
  (eval-thunk (cdr stream)))
(define (stream-null? stream)
  (null? stream))

(define the-empty-stream '())

;;; Let special-form
;;; (let ((<var1> <exp1>) (<var2> <exp2>)...(<varn> <expn>)) <body>)
;;; = ((lambda (<var1> ...<varn>) <body>) <exp1> ...<expn>)

(define (var-exp l)
    (cadr l))

(define (proc-body l)
    (cddr l))

(define (collect-vars ve) ;ve = variable-exp
  (cond ((null? ve) '())
        (else
         (cons (caar ve) (collect-vars (cdr ve))))))

(define (collect-exps ve)
  (cond ((null? ve) '())
        (else
         (cons (cadar ve) (collect-exps (cdr ve))))))

(define (let->lambda exp)
  (cons (cons 'lambda (cons (collect-vars (var-exp exp))
                            (proc-body exp)))
        (collect-exps (var-exp exp))))

;;; Check if var already defined.
;;; defined? is defined not as a lambda within install-special-forms-packages
;;; because it's used for install-special-form too

(define (defined? var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars)) #t)
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        #f
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Takes in quoted special-form and lambda expression in the form
;;; (lambda (exp env)..) as input and insert it on to the table
;;; IFF it's not already installed or name of the special-form not
;;; already defined.

(define (install-special-form special-form action)
  (if (or (lookup special-form special-forms-table)
          (defined? special-form the-global-environment))
      (error special-form " is already defined")
      (insert! special-form action special-forms-table)))

;;; Package up the special-forms to be pre-installed.
;;; Calling (install-special-form-packages) would install everything
;;; in the body.

(define (install-special-form-packages)
  (install-special-form 'define
                        (lambda (exp env)
                          (eval-definition exp env)))
  (install-special-form 'let
                        (lambda (exp env)
                          (xeval (let->lambda exp) env)))
  (install-special-form 'lambda
                        (lambda (exp env)
                          (make-procedure (lambda-parameters exp)
                                          (lambda-body exp) env)))
  (install-special-form 'set!
                        (lambda (exp env)
                          (eval-assignment exp env)))
  (install-special-form 'cond
                        (lambda (exp env)
                          (xeval (cond->if exp) env)))
  (install-special-form 'quote
                        (lambda (exp env)
                          (text-of-quotation exp)))
  (install-special-form 'if
                        (lambda (exp env)
                          (eval-if exp env)))
  (install-special-form 'begin
                        (lambda (exp env)
                          (eval-sequence (begin-actions exp) env)))
  (install-special-form 'load
                        (lambda (exp env)
                          (define (filename exp) (cadr exp))
                          (define thunk (lambda ()
                                          (readfile)
                                          ))
                          (define readfile (lambda()
                                             (let ((item (read)))
                                               (if
                                                (not
                                                 (eof-object? item))
                                                (begin
                                                  (xeval item env)
                                                  (readfile))))
                                             ))
                          (with-input-from-file (filename exp) thunk)
                          (filename exp)
                          ))
  (install-special-form 'defined?
                        (lambda (exp env)      
                          (defined? (cadr exp) env)))
  (install-special-form 'locally-defined?
                        (lambda (exp env)
                          (define (env-loop env)
                            (define (scan vars vals)
                              (cond ((null? vars) #f)
                                    ((equal? (cadr exp) (car vars)) #t)
                                    (else (scan (cdr vars) (cdr vals)))))
                            (if (eq? env the-empty-environment)
                                #f
                                (let ((frame (first-frame env)))
                                  (scan (frame-variables frame)
                                        (frame-values frame)))))
                          (env-loop env)))
  (install-special-form 'make-unbound!
                        (lambda (exp env) ;exp = (make-unbound! x)
                          (define (env-loop env)
                            (define (scan vars vals)
                              (cond ((null? vars)  
                                     (env-loop (enclosing-environment env)))
                                    ((eq? (cadr exp) (car vars))
                                     (set-car! vars '())
                                     (env-loop (enclosing-environment env)))
                                    (else (scan (cdr vars) (cdr vals)))))
                            (if (eq? env the-empty-environment) ;root
                                "unbounded"
                                (let ((frame (first-frame env)))
                                  (scan (frame-variables frame)
                                        (frame-values frame)))))
                          (env-loop env)))
  (install-special-form 'locally-make-unbound!
                        (lambda (exp env)
                          (define (env-loop env)
                            (define (scan vars vals)
                              (cond ((null? vars)
                                     "unbounded")
                                    ((eq? (cadr exp) (car vars))
                                     (set-car! vars '()))
                                    (else (scan (cdr vars) (cdr vals)))))
                            (if (eq? env the-empty-environment) ;root
                                "unbounded"
                                (let ((frame (first-frame env)))
                                  (scan (frame-variables frame)
                                        (frame-values frame)))))
                          (env-loop env)))
  (install-special-form 'cons-stream
                        (lambda (exp env)
                          (cons (xeval (elmt exp) env) 
                                (make-thunk (strm exp) env))))
  )

;;; lookup-action and type-of are created to hide the lookup table
;;; implementation
;;; lookup-action lookup the specal-form table and return the lambda
;;; expression if found else #f

(define (lookup-action special-form)
  (lookup special-form special-forms-table))

;;; takes the expression and extract the first thing on the list
;;; or return exp if it's not a list

(define (type-of exp)
  (if (list? exp)
      (car exp)
      exp))

;;; for when
;;; ==>if
;;; Special from: if

(define (special-form? var)
  (cond ((lookup-action var)
         (display "Special form: "))
        (else
         #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing expressions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Numbers, strings, and booleans are all represented as themselves.
;;; (Not characters though; they don't seem to work out as well
;;; because of an interaction with read and display.)

(define (self-evaluating? exp)
  (or (number? exp)
      (string? exp)
      (boolean? exp)
      (special-form? exp)
      ))

;;; variables -- represented as symbols

(define (variable? exp) (symbol? exp))

;;; quote -- represented as (quote <text-of-quotation>)

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

;;; assignment -- represented as (set! <var> <value>)

(define (assignment? exp) 
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

;;; definitions -- represented as
;;;    (define <var> <value>)
;;;  or
;;;    (define (<var> <parameter_1> <parameter_2> ... <parameter_n>) <body>)
;;;
;;; The second form is immediately turned into the equivalent lambda
;;; expression.

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

;;; lambda expressions -- represented as (lambda ...)
;;;
;;; That is, any list starting with lambda.  The list must have at
;;; least one other element, or an error will be generated.

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;;; conditionals -- (if <predicate> <consequent> <alternative>?)

(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      #f))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))


;;; sequences -- (begin <list of expressions>)

(define (begin? exp) (tagged-list? exp 'begin))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))


;;; procedure applications -- any compound expression that is not one
;;; of the above expression types.

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


;;; Derived expressions -- the only one we include initially is cond,
;;; which is a special form that is syntactically transformed into a
;;; nest of if expressions.

(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      #f                          ; no else clause -- return #f
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF "
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Truth values and procedure objects
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Truth values

(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))


;;; Procedures

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (user-defined-procedure? p)
  (tagged-list? p 'procedure))


(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;       Handling various methods of argument passing
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; delayed tagged parameters -- (delayed <var>)

(define (delayed? exp)
  (tagged-list? exp 'delayed))

(define (make-thunk exp env)
  (list 'thunk exp env))

(define (thunk-exp thunk) (cadr thunk))
(define (thunk-env thunk) (caddr thunk))

(define (eval-thunk thunk)
  (xeval (thunk-exp thunk) (thunk-env thunk)))

(define (thunk? exp)
  (tagged-list? exp 'thunk))

;; reference tagged parameters

(define (reference? exp)
  (tagged-list? exp 'reference))  

(define (to-be-ref exp env)
  (list 'to-be-ref exp env))

(define (ref-exp obj) (cadr obj))
(define (ref-env obj) (caddr obj))

(define (ref-it obj)
  (cond ((and (symbol? (ref-exp obj))
              (defined? (ref-exp obj) (ref-env obj)))
         (lookup-variable-value (ref-exp obj) (ref-env obj)))
        (else
         (s450error (ref-exp obj) " must be predefined"))))

(define (to-be-ref? exp)
  (tagged-list? exp 'to-be-ref))

;;; dynamic tagged

(define (dynamic? exp)
  (tagged-list? exp 'dynamic))

;;; Takes in a parameter as input and check if the parameter is tagged
;;; ==>(tagged-param? '(delayed x))
;;; #t

(define (tagged-param? param)
  (or (delayed? param)
      (reference? param)))

;;; Scan the whole params for tagged params. If a param is tagged,
;;; removed the tag and update the corresponding argument's value
;;; depending on what tag the param is.
;;; ==>(define l1 '( x (delayed y) z (delayed v)))
;;; ==>(define l2 '(1 2 3 4))
;;; ==>(scan-params l1 l2 'env)
;;; ==>l1
;;; ==>(x y z v)
;;; ==>l2
;;; ==>(1 (thunk 2 env) 3 (thunk 4 env))

(define (scan-params params args env)
      (cond ((< (length params) (length args))
             (s450error "Too many arguments supplied " params args))
            ((> (length params) (length args))
             (s450error "Too few arguments supplied " params args))
            ((null? params) '())
            ((list? (car params))
             (cond ((delayed? (car params))
                    (set-car! params (cadar params)) ;untag it
                    (set-car! args (make-thunk (car args) env))
                    (scan-params (cdr params) (cdr args) env))
                   ((reference? (car params))
                    (set-car! params (cadar params)) ;untag it
                    (set-car! args (to-be-ref (car args) env))
                    (scan-params (cdr params) (cdr args) env))
                   ((dynamic? (car params))
                    (set-car! params (cadar params)) ;untag it
                    (set-car! args        ;get value from dynamic
                              (xeval      ;and set (car args) to that val
                               (car args)
                               the-dynamic-environment))
                    (scan-params (cdr params) (cdr args) env))))
            (else (scan-params (cdr params) (cdr args) env))))

;;; For copying the parameter list of a function into a new list so
;;; set-car! won't affect the original parameter while the updated
;;; parameter list gets inserted into the frame.

(define (list-copy list)
  (if (null? list) '() (cons (car list) (list-copy (cdr list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing environments
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An environment is a list of frames.

(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment '())

;;; Each frame is represented as a pair of lists:
;;;   1.  a list of the variables bound in that frame, and
;;;   2.  a list of the associated values.

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

;;; Extending an environment

(define (xtend-environment vars vals base-env)
  (cond ((= (length vars) (length vals))
         (let ((new-frame (make-frame vars vals)))
           (set! the-dynamic-environment
                 (cons new-frame the-dynamic-environment))
           (cons new-frame base-env)))
         (else
          (cond ((< (length vars) (length vals))
                 (s450error "Too many arguments supplied " vars vals))
                (else
                 (s450error "Too few arguments supplied " vars vals))))))

;;; Looking up a variable in an environment

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (cond ((thunk? (car vals)) ;force promise
                    (eval-thunk (car vals)))
                   (else
                    (car vals))))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (s450error "Unbound variable " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Setting a variable to a new value in a specified environment.
;;; Note that it is an error if the variable is not already present
;;; (i.e., previously defined) in that environment.

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (s450error "Unbound variable -- SET! " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (cond ((lookup-action var)     ;check if var is special-form
         (s450error "Var cannot be special-form " var))
        ((to-be-ref? (lookup-variable-value var env)) ;check if var is ref
          (set-variable-value! (ref-exp (lookup-variable-value var env))
                               val
                               (ref-env (lookup-variable-value var env))))
        (else
         (env-loop env))))

;;; Defining a (possibly new) variable.  First see if the variable
;;; already exists.  If it does, just change its value to the new
;;; value.  If it does not, define the new variable in the current
;;; frame.

(define (define-variable! var val env)
  (cond ((lookup-action var) ;check if var is special-form
         (s450error "Var cannot be special-form " var))
        (else
         (let ((frame (first-frame env)))
           (define (scan vars vals)
             (cond ((null? vars)
                    (add-binding-to-frame! var val frame))
                   ((eq? var (car vars))
                    (set-car! vals val))
                   (else (scan (cdr vars) (cdr vals)))))
           (scan (frame-variables frame)
                 (frame-values frame))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The initial environment
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is initialization code that is executed once, when the the
;;; interpreter is invoked.
(define (setup-environment)
  (let ((initial-env
         (xtend-environment '()
                            '()
                            the-empty-environment)))
    initial-env))

;;; Define the primitive procedures

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

;;; Takes in the name of the procedure and action and define it
;;; in the global-evironment iff the name of the procedure is not
;;; already taken by a special-form

(define (install-primitive-procedure name action)
  (cond ((lookup-action name)
         (error "Procedure cannot be special-form " name))
      (else
       (define-variable! name
         (list 'primitive action)
         the-global-environment)
       name)))

;;; Package up the primitive procs to be pre-installed
;;; (install-primitive-proc-packages) will install everything in
;;; the body

(define (install-primitive-proc-packages)
  (install-primitive-procedure 'car car)
  (install-primitive-procedure 'cdr cdr)
  (install-primitive-procedure 'cadr cadr)
  (install-primitive-procedure 'caddr caddr)
  (install-primitive-procedure 'cadddr cadddr)
  (install-primitive-procedure 'cons cons)
  (install-primitive-procedure 'null? null?)
  (install-primitive-procedure 'list? list?)
  (install-primitive-procedure 'map map)
  (install-primitive-procedure 'length length)
  (install-primitive-procedure '+ +)
  (install-primitive-procedure '- -)
  (install-primitive-procedure '= =)
  (install-primitive-procedure '> >)
  (install-primitive-procedure '< <)
  (install-primitive-procedure '>= >=)
  (install-primitive-procedure '* *)
  (install-primitive-procedure '/ /)
  (install-primitive-procedure 'modulo modulo)
  (install-primitive-procedure 'expt expt)
  (install-primitive-procedure 'quotient quotient)
  (install-primitive-procedure 'remainder remainder)
  (install-primitive-procedure 'display display)
  (install-primitive-procedure 'newline newline)
  (install-primitive-procedure 'equal? equal?)
  (install-primitive-procedure 'not not)
  (install-primitive-procedure 'exit exit)
  (install-primitive-procedure 's450error s450error)
  (install-primitive-procedure 'stream-cdr stream-cdr)
  (install-primitive-procedure 'stream-car stream-car)
  (install-primitive-procedure 'stream-null? stream-null?)
  (install-primitive-procedure 'char->integer char->integer)
  (install-primitive-procedure 'string->list string->list)
  (install-primitive-procedure 'number->string number->string))

;;; For pre-defining variables
(define (install-obj name value)
  (cond ((lookup-action name)
         (error "Procedure cannot be special-form " name))
      (else
       (define-variable!
         name
         value
         the-global-environment)
       name)))

(define (install-obj-packages)
  (install-obj 'the-empty-stream '())
  (install-obj 'nil '()))

;;; Here is where we rely on the underlying Scheme implementation to
;;; know how to apply a primitive procedure.

(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;       Error and exit handling
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Stores the state where s450 is just called.
;;; (restart) effectively restarts s450.

(define restart '())

;;; Display the error and immediately go back to listening for another
;;; input

(define (s450error . args)
  (display "ERROR: ")
  (for-each display args)
  (newline)
  (restart args))

;;; Stores the state that (s450) is not called yet
;;; Calling (end <anything>) will effectly exit s450.

(define get-out '())

;;; Assign the state that (s450) is not called yet to variable end.

(begin
  (call-with-current-continuation
   (lambda (here)
     (set! get-out here)))
  ;calling (end <anything>) gets you back here
  )  

(define (exit)
  (display "Exiting s450...")
  (get-out '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The main driver loop
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that (read) returns an internal representation of the next
;;; Scheme expression from the input stream.  It does NOT evaluate
;;; what is typed in -- it just parses it and returns an internal
;;; representation.  It is the job of the scheme evaluator to perform
;;; the evaluation.  In this case, our evaluator is called xeval.

(define input-prompt "s450==> ")

(define (s450)
  (call-with-current-continuation 
   (lambda (here)
     (set! restart here)))
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (cond ((eof-object? input)
	   (display "Exiting s450...")
	   (newline))
	  (else
	   (let ((output (xeval input the-global-environment)))
	     (user-print output))
	   (s450)))))

(define (prompt-for-input string)
  (newline) (newline) (display string))

;;; Note that we would not want to try to print a representation of the
;;; <procedure-env> below -- this would in general get us into an
;;; infinite loop.

(define (user-print object)
  (if (user-defined-procedure? object)
      (display (list 'user-defined-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Here we go:  define the environments and invite the
;;;        user to run the evaluator.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define the-dynamic-environment '()) 
(define the-global-environment (setup-environment))

(install-special-form-packages)
(install-primitive-proc-packages)
(install-obj-packages)

(display "... loaded the metacircular evaluator. (s450) runs it. ctrl-d 
exits it.")
(newline)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;                     TESTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;((lambda (x) (car x)) '(3))
;(define x 5)
;(define (double x) (+ x x))
;(double x)
;(define f (lambda (a b) (defined? a)))
;(define (e? x) (cond ((= x 2) "#t") (else "f")))
;(define (f x (delayed y) z) (if (= x 5) x y))
;(f 1 (/ 0 3) 3)
;(f 5 (/ 3 0) 6)
;(define s (cons-stream the-empty-stream the-empty-stream))
