#lang racket/load
;(load "simpleParser.scm")
(load "functionParser.scm")
(load "statecontrol.scm")
(load "lex.scm")

;Team: Callum Grant (chg33), Jiawei Wu (jxw585), John Donnelly (jed126)

;-------------------------start-----------------------------

;usage: ex: (interpret "test1.txt")

(define interpret (lambda (file)
      (boolean_filter (m_call_func '(funcall main) (interpreter_global (parser file) (newstate))))
      ))

;filtering boolean results to display nicely
(define boolean_filter (lambda (val)
    (cond
      ((and (not (number? val)) (not val)) (display 'false))
      ((and (not (number? val)) val)       (display 'true))
      (else (display val))
      )))

;read list directly, for debugging
(define interpret2 (lambda (text)
      (boolean_filter (m_call_func '(funcall main) (interpreter_global text (newstate))))
      ))

;Interpretation method, runs through each sublist within the list of lists returned by parser, effectively going through the original text line-by-line.

(define interpreter
    (lambda (parsed s break continue throw return)
        ;intializing a state variable 
        (cond
          ((null? parsed) s) ;if parsed to the end, evaluate main
          (else (interpreter (cdr parsed) (perform (car parsed) s break continue throw return) break continue throw return))
        )
      )
 )

(define interpreter_global 
  (lambda (parsed state)
    (interpreter
      parsed
      state
      (lambda (v) (error "break error"))
        (lambda (v) (error "continue error"))
        (lambda (v) (error "throw error"))
        (lambda (v) (error "return error"))
      )))

;-------------------------end-----------------------------

(define layered
  (lambda (state)
    (cond 
      ((void? state) #f)
      ((empty? state) #f)
      ((empty? (car state)) #f)
      (else (list? (caar state))))
  )
)

;assign in execution space
(define assignhandler (lambda (line state)
    (m_state (operand1 line) (m_value (operand2 line) state) state)
    ))

(define declarehandler (lambda (line state)
    (if (null? (operand2 line))
      (m_declare (operand1 line) state)
      (m_state (operand1 line) (m_value (operand2 line) state) (m_declare (operand1 line) state))
      )))


;Modified version of the basic expression evaluator from class (update: adjusted to perform functions)
(define m_value
  (lambda (expression s)
      (cond
        ((null? expression) '())
        ((number? expression) expression)
        ((boolean? expression) expression)
        ((eq? 'null expression) 'null)
        ; ((eq? 'true expression) #t)
        ; ((eq? 'false expression) #f)
        
        ;((symbol? expression) (if (eq? (lookup expression s) "undefined") (error 'error "undefined") (lookup expression s)))
        ((not (list? expression)) (lookup expression s))
        ((null? (cdr expression)) (m_value (car expression) s))
        ((eq? (operator expression) 'var) (declarehandler expression s))
        ((eq? 'function (operator expression)) (m_declare_func expression s))  ;Functions
        ((eq? 'funcall  (operator expression)) (m_call_func expression s))
        ((eq? 'static-function (operator expression)) (m_declare))


        ((eq? 'class (operator expression)) (m_declare_class expression s))
        ((eq? 'new (operator expression)) (m_new_class expression s)) 
        ((eq? 'dot (operator expression)) (m_dot_handler expression s)) ;(m_dot_handler expression (scope of the expression goes here))

        ((eq? '= (operator expression)) (if (eq? "undefined" operand2) (error 'error "undefined") (m_value (m_value (operand2 expression) s) (assignhandler expression s))))
        ((eq? '+ (operator expression)) (+ (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '- (operator expression)) (if (null? (cddr expression))
                                            (- 0 (m_value (operand1 expression) s))
                                            (- (m_value (operand1 expression) s) (m_value (operand2 expression) s))))
        ((eq? '* (operator expression)) (* (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '/ (operator expression)) (quotient (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '% (operator expression)) (remainder (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '== (operator expression)) (eq? (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '!= (operator expression)) (not (eq? (m_value (operand1 expression) s) (m_value (operand2 expression) s))))
        ((eq? '> (operator expression)) (> (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '>= (operator expression)) (>= (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '< (operator expression)) (< (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '<= (operator expression)) (<= (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '&& (operator expression)) (and (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '|| (operator expression)) (or (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
        ((eq? '! (logicsymbol expression)) (not (m_value (operand1 expression) s)))
        (else (error 'unknown "unknown")))
    ;)

      ))




; Whilehandler addresses situations of the while loop. If the condition is not met, it performs the clause and then recurs.
; state - the state. line - the line that the while occurs in (i.e. the segment enclosed by parentheses, starting with "while")
; (cadr line) - gets the element that is second in the provided line, which should be the clause for the while loop.
; (caddr line) gets the third element in the provided line, which should be the procedure for the while loop.
(define whilehandler
  (lambda (line state throw return)
    (call/cc (lambda (break)
          (if (not (m_value (cadr line) state))
            (break state)
            (whilehandler line (call/cc (lambda (continue) (perform (caddr line) state break continue throw return))) throw return))))))



;Abstractions

;prefix parser
(define operator
  (lambda (input)
    (if (null? input)  '() (car  input))))

(define logicsymbol
  (lambda (input)
    (operator input)))

(define operand1
  (lambda (input)
    (if (null? (cdr input)) '() (cadr input))))

(define operand2
  (lambda (input)
    (if (null? (cddr  input)) '() (caddr  input))))

;Performs the task of a given line, by calling the method that pertains to the line's opening.
(define perform
  (lambda (line state break continue throw return)
      (cond
        
        ;((eq? (cadr line) 'state) (return state))
        ((eq? (operator line) 'throw) (throwhandler line state throw))
        ((eq? (operator line) '=) (assignhandler line state))
        ;return needs revamp (immediate break)
        ((eq? (operator line) 'return)
                            (cond
                                    ((eq? (cadr line) 'state) (return (display state)))
                                    (else (return (m_value (operand1 line) state)))
                                    ))

        ((eq? (operator line) 'if) (ifhandler line state break continue throw return))
        ((eq? (operator line) 'while) (whilehandler line state throw return)) 

        ((eq? (car line) 'begin) 
           (blockhandler line state break continue throw return))
            ;block handler rewrote
        ((eq? (car line) 'continue)
            (cond
              ((not (layered state)) (error 'error "Continue must be inside a block"))
              ;if continue is encountered, restart the block it is within.
              (else (continue state)) 
            ))

        ((eq? (operator line) 'break)
            (cond 
              ;break must be in a block
              ((not (layered state)) (error 'error "Break must be inside a block"))
              ;if break is encountered, throw away current layer immediately, 
              (else (break state)) 
            ))
        ;try catch handling
        ((eq? (operator line) 'try) (tcfhandler line state break continue throw return))

        (else (m_value line state))) ;functions will be dealt here to M_value

      ))




;Ifhandler - does its clause if the condition is met. If condition is not met, AND an else clause is present, performs the else clause.
(define ifhandler
  (lambda (line state break continue throw return)
    (cond
      ((eq? (m_value (cadr line) state) #t) (perform (caddr line) state break continue throw return))
      ((null? (itemn line 4)) state)
      (else (perform (itemn line 4) state break continue throw return)))))



(define blockhandler
  (lambda (line s break continue throw return)
    (poplayer
      (interpreter
        (cdr line)
        (pushlayer s)
        (lambda (v)
          (break (poplayer v)))
        (lambda (v)
          (continue (poplayer v)))
        (lambda (v)
          (throw (poplayer v)))
        return
        ))    

    )
  )




;--------------------------- copied code --------------------

(define breakhandler (lambda (state break) (break state)))

(define continuehandler (lambda (state continue) (continue state)))

(define throwhandler
  (lambda (line state throw)
    (throw (cadr line) state)))


(define tcfhandler
  (lambda (statement state break continue throw return)
    (call/cc
     (lambda (try-break)
       (letrec ((finally (lambda (s)
                    (cond
                      ((null? (finally-stmt statement)) s)
                      ((list? (car (finally-body statement))) (interpreter (finally-body statement) s break continue throw return))
                      (else (perform (finally-body statement) s break continue throw return)))))

                (try (lambda (s try-throw)
                       (if (list? (car (try-body statement)))
                           (finally (interpreter (try-body statement) s break continue try-throw return))
                           (finally (perform (try-body statement) s break continue try-throw return)))))

                (catch (lambda (e s)
                         (if (list? (car (catch-body statement)))
                             (finally (interpreter (replace*-cps (catch-err statement) e (catch-body statement) (lambda (v) v)) s break continue throw return))
                             (finally (perform (replace*-cps (catch-err statement) e (catch-body statement) (lambda (v) v)) s break continue throw return))))))
         (try state (lambda (e s) (try-break (catch e s)))) )))))

(define replace*-cps
  (lambda (old new l return)
    (cond
      ((null? l) (return l))
      ((pair? (car l)) (replace*-cps old new (cdr l) (lambda (v) (replace*-cps old new (car l) (lambda (v2) (return (cons v2 v)))))))
      ((eq? (car l) old) (replace*-cps old new (cdr l) (lambda (v) (return (cons new v)))))
      (else (replace*-cps old new (cdr l) (lambda (v) (return (cons (car l) v))))))))

  ; (try body (catch (e) body) (finally body))
(define try-body cadr)
(define catch-body (lambda (t) (if (null? (cddr (caddr t)))  '()  (car (cddr (caddr t))))))
(define catch-err (lambda (t) (car (cadr (caddr t)))))
(define finally-stmt (lambda (t) (car (cdddr t))))
(define finally-body (lambda (t) (cadr (car (cdddr t)))))




;------------------------------------- Functions
;functions would be stored as ((name) ())

;function is parsed as:
;(function name (parameter) body)
(define m_declare_func
  (lambda (line state)
    (m_state 
      (itemn line 2) ;the name of the function
      (makeclosure line state) ;the function is stored as a closure with its scope, formal param list and its body
      (m_declare (itemn line 2) state) 
      )
    )
  )


;function construting the function closure that would be stored
(define makeclosure 
  (lambda (line state)
    (cons (itemn line 3) (cons (itemn line 4) (cons (lambda () state) '())))
  )
)


;function call line would be parsed as '(funcall fib (- a 1))








;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite
;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite
(define m_call_func
  (lambda (line state)
    (call/cc (lambda (return)
      (perform_func 
        (cadr (lookup (operand1 line) state))
        (set_formal_params
          (cddr line)
          (car (lookup (operand1 line) state))
          state
          ((caddr (lookup (operand1 line) state))))
        return)
      )
    )
  )
)



;running the body of func, it would create a new frame of state and pop off when finishing
(define perform_func 
  (lambda (body state return)
    (poplayer
      (interpreter
        body
        (pushlayer state)
        (lambda (v) (error "break error"))
        (lambda (v) (error "continue error"))
        (lambda (v) (error "throw error")) ;implement function throw later
        return
      )
    )
  )
)


;help function that counts number of element in a list
(define howmany (lambda (list) (foldl (lambda (v a) (+ 1 a))  0 list)))
;






;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite
;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite
;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite;rewrite



(define set_formal_params (lambda (params formals state funcscope)
    (cond
      ((and (null? params) (null? formals)) state) ;no parameter operation involved, just pass through
      ((not (eq?  (howmany params) (howmany formals))) (error 'set_formal_params "arguments error"))
      ((or (null? (cdr params)) (null? (cdr formals))) 
        (m_state
          (car formals)
          (m_value (car params) state)
          (m_declare (car formals) funcscope)
          ))
      (else (m_state
        (car formals)
        (m_value (car params) state)
        (m_declare
         (car formals)
          (set_formal_params
            (cdr params)
            (cdr formals)
            state
            funcscope)
          )))
      )))





; ---------------------------classes------------------------------

(define newclass
  (lambda (v) v)
  )