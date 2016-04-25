#lang racket/load
(load "lex.scm")
(load "classParser.scm")


;Team: Callum Grant (chg33), Jiawei Wu (jxw585), John Donnelly (jed126)

;-------------------------start-----------------------------

;usage: ex: (interpret "test1.txt")

(define interpret
  (lambda (filename)
    (call/cc (lambda (return)
    (m_run_main (process_classes (interpreter (parser filename) newstate newbreak newcontinue newthrow return))))
    ))
  )

(define interpret2
  (lambda (parsed)
    (call/cc (lambda (return)
    (interpreter parsed newstate newbreak newcontinue newthrow return)))
    )
  )

;Interpretation method, runs through each sublist within the list of lists returned by parser, effectively going through the original text line-by-line.

(define interpreter
    (lambda (parsed s break continue throw return)
        ;intializing a state variable 
        (cond
          ((null? parsed) s) ;if parsed to the end, evaluate main
          ((layered s) (interpreter (cdr parsed) (cons (perform (car parsed) (car s) break continue throw return) (cdr s)) break continue throw return))
          ((pair? (car parsed)) (interpreter (cdr parsed) (perform (car parsed) s break continue throw return) break continue throw return))
          (else (interpreter (cdr parsed) (perform parsed s break continue throw return) break continue throw return))
        )
      )
 )
;-------------------------end-----------------------------

;initializations
(define newstate  '(()()))
(define newbreak (lambda (v) v))
(define newcontinue (lambda (v) v))
(define newthrow (lambda (e s) (error 'throw "No catch")))

;helper to determine whether a state is layered (currently in a block)
(define layered
  (lambda (state)
    (cond 
      ((void? state) #f)
      ((empty? state) #f)
      ((empty? (car state)) #f)
      (else (list? (caar state))))
  )
)


;helpers for state operations
(define extract     
  (lambda (m)
    (cond ((not (pair? m)) '())
          (else (cons (car (car m)) (extract (cdr m)))))
  )
)

(define remain
  (lambda (m)
    (cond ((not (pair? m)) '())
          (else (cons (cdr (car m)) (remain (cdr m)))))
  )
)

(define combine
  (lambda (m1 m2)
      (cons (cons (car m1) (car m2)) (list (flatten (cons (cdr m1) (cdr m2)))))
  )
)



(define m_insert
  (lambda (name value s)
    (if (layered s)
      (cons (m_insert name value (car s)) (cdr s))
      (append (list (append (car s) (list name))) (list (append (cadr s) (list (box (m_value value s))))))
      )
  )
)

(define m_insert_func
  (lambda (name value s)
      (append (list (append (car s) (list name))) (list (append (cadr s) (list (box value)))))
  )
)



; m_remove has a bug in second inner list that requires a flatten, maybe to be fixed for elegance?
(define flatten
  (lambda (l)
    (cond
      ((null? l) '())
      ((list? (car l)) (append (flatten (car l)) (flatten (cdr l))))
      (else (cons (car l) (flatten (cdr l)))))))

(define m_remove
  (lambda (name s)
    (if (layered s)
      (cons (m_remove name (car s)) (cdr s))
      (cond
        ((null? s) s)
        ((empty? (car s)) '())
        ((eq? name (caar s)) (remain s))
        (else (append (list (append (list (car (extract s))) (car (m_remove name (remain s))))) (list (flatten (append (cdr (extract s)) (cdr (m_remove name (remain s))))))))
      ))
  )
)

;Finds the value of a variable of a given name within our state.
(define lookup
    (lambda (name s)
      (if (not (layered s))
        (cond 
          ((null? s) "undefined")
          ;((void? s) "undefined")
          ((empty? (car s)) "undefined")
          ((eq? name (caar s)) (unbox (caadr s)))
          ;(else (lookup name (remain s)))
          (else (lookup name (remain s)))
      )

        (if (eq? "undefined" (lookup name (car s)))
          (lookup name (getrootlayer s))
          (lookup name (car s))))
  )
)

;the lookup version that returns the box rather than the value
(define lookupbox
    (lambda (name s)
      (if (not (layered s))
        (cond 
          ((null? s) "undefined")
          ;((void? s) "undefined")
          ((empty? (car s)) "undefined")
          ((eq? name (caar s)) (caadr s))
          (else (lookupbox name (remain s)))
      )

        (if (eq? "undefined" (lookupbox name (car s)))
          (lookupbox name (cdr s))
          (lookupbox name (car s))))
  )
)

(define lookupfieldbox
    (lambda (name instance s)
      (if (inscope? instance s)
        (lookupbox name (unbox (getinstancefieldlist instance s)))
        (lookupfieldbox name instance (cdr s))
      )
  )
)


;lookup cdr until state where func is declread in
(define lookupforfunc
    (lambda (name s funcname)
      (if (not (layered s))
        (cond 
          ((null? s) "undefined")
          ;((void? s) "undefined")
          ((empty? (car s)) "undefined")
          ((eq? name (caar s)) (unbox (caadr s)))
          ;(else (lookup name (remain s)))
          (else (lookup name (remain s)))
      )
        (cond
          ((inscope? name s) (lookup name s))
          (else (locate_func_var name s funcname))
        )

        )
  )
)


(define locate_func_var
  (lambda (name s funcname)
    (cond
      ((not (layered s)) (lookup name s))
      ((inscope? funcname s) (lookup name (car s)))    
      (else (locate_func_var name (cdr s) funcname))
    )
  )
)

;return the state where the func is defined in

;(define func_state
;  (lambda (func_name allstate)
;    (if (inscope? func_name allstate)
;      (car state)
;      (func_state func_name (cdr state))
;    )
;  )
;)

(define isfunc
  (lambda (name s)
    (> (howmany (lookup name s)) 1)
  )
)



; Assigns a value to a variable, and modifies our state accordingly.


(define m_state
  (lambda (expression s)
        (if (eq? (lookup (cadr expression) s) "undefined")
          (error expression "Use before declaration")
          (if (layered s)
            (begin (set-box! (lookupbox (cadr expression) s) (m_value (caddr expression) (car s))) s)
            (begin (set-box! (lookupbox (cadr expression) s) (m_value (caddr expression) s)) s)
          )
        )
      )
  )

;wtf can't setbox, have to do it manually
(define m_state_funcscope
  (lambda (expression s name instance)
    (if (eq? name null)
      (m_state expression s)
      (if (eq? (caadr expression) 'dot)
        (begin (set-box! (lookupfieldbox (itemn (cadr expression) 3) instance s) (m_value_scope (caddr expression) s name instance)) s)
        (if (eq? (lookupforfunc (cadr expression) s name) "undefined")
          (error (cadr expression) "Use before declaration")
          (begin (set-box! (lookupbox (cadr expression) s) (m_value_scope (caddr expression) s name instance)) s)
        )
      )
    )
  )
)

(define set_func_scope
  (lambda (funcname scope s)
    (begin (set-box! (car (lookup funcname s)) scope) s)))


;manually update a state
(define m_manual_state
  (lambda (name exp s)
        (if (eq? (lookup name s) "undefined")
          (error 'error "Use before declaration")
          (if (layered s)
            ;(if (isfunc exp s)
              ;(begin (set-box! (lookupbox name s) exp) s)
            (begin (set-box! (lookupbox name s) (m_value exp (car s))) s)
            (begin (set-box! (lookupbox name s) (m_value exp s)) s))
          )
        )
      )
  ;)

; Declares a given variable
; (var x) or (var x 3)
(define m_declare
  (lambda (expression s)
    (if (layered s)
      (cons (if (eq? (car expression) 'var)
          (if (not (null? (cddr expression)))
            (def_with_value (cadr expression) (m_value (caddr expression) s) s) ;parse "var x (things)" 
            (def_null (cadr expression) s);else parse "var x"
          )
          "not valid declare"
        ) (cdr s))
        (if (eq? (car expression) 'var)
          (if (not (null? (cddr expression)))
            (def_with_value (cadr expression) (m_value (caddr expression) s) s) ;parse "var x (things)" 
            (def_null (cadr expression) s);else parse "var x"
          )
          "not valid declare"
        )
      )
  )
)

;declare a variable in current layer specifically (Do we really need it?)
 (define m_declare_inscope
   (lambda (expression s name instance)
       (if (eq? (car expression) 'var)
          (if (not (null? (cddr expression)))
             (def_with_value_local (cadr expression) (m_value_scope (caddr expression) s name instance) s) ;parse "var x (things)" 
             (def_null_local (cadr expression) s);else parse "var x"
           )
           "not valid declare"
         )
       )
   )




; If the defined variable is defined with a value, this helper assigns it a value.
(define def_with_value
  (lambda (var expression s) 
    (cond ((not (eq? (lookup var s) "undefined")) (begin (error 'error "no re-declaring") (s))) ;no re-declaring
          (else (m_insert var expression s)))
  )
)

(define def_with_value_local
  (lambda (var expression s) 
    (cond ((not (eq? (lookup var (car s)) "undefined")) (begin (error 'error "no re-declaring") (s))) ;no re-declaring
          (else (cons (m_insert var expression (car s)) (cdr s))))
  )
)

(define def_with_func
  (lambda (var expression s) 
    (cond ((not (eq? (lookup var s) "undefined")) (begin (error 'error "no re-declaring") (s))) ;no re-declaring
          (else (m_insert_func var expression s)))
  )
)

(define def_null_local
  (lambda (var s) 
    (cond ((not (eq? (lookup var (car s)) "undefined")) (begin (error 'error "no re-declaring") (s))) ;no re-declaring
          (else (cons (m_insert var 'newvar (car s)) (cdr s))))
  )
)

; If the defined variable has no value, this helper sets it up with a null value.
(define def_null
  (lambda (var s)
    (cond ((not (eq? (lookup var s) "undefined")) (begin (error 'error "no re-declaring") (s))) ;no re-declaring
          (else (m_insert var 'newvar s)))
  )
)


;Modified version of the basic expression evaluator from class.
(define m_value
  (lambda (expression s)
    ;(if (layered s) (m_value expression (car s))
      (cond
        ((eq? 'newvar expression) 'null) ;for declaration of a new variable
        ((eq? 'true expression) #t)
        ((eq? 'false expression) #f)
        ((symbol? expression) (if (eq? (lookup expression s) "undefined") (error expression "undefined") (lookup expression s)))
        ((number? expression) expression)
        ((boolean? expression) expression)

        ((eq? 'function (operator expression)) (m_declare_func expression s))  ;Functions
        ((eq? 'static-function (operator expression)) (m_declare_func expression s))
        ((eq? 'funcall  (operator expression)) (m_call_func 'main expression s 'lmao))
        ((eq? 'class  (operator expression)) (m_declare_class expression s))
        ((eq? 'dot (operator expression)) (dothandler expression s 'null))
        ((eq? 'new (operator expression)) (create_object expression 'null s))


        ((eq? '= (operator expression)) (if (eq? "undefined" operand2) (error 'error "undefined") (m_value (m_value (operand2 expression) s) (m_state expression s))))
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
        (else expression)) 
        ;(else (error expression "unknown"))) 
    ;)
      ))

;name tracking version
(define m_value_scope
  (lambda (expression s name instance)
    ;(if (layered s) (m_value_scope expression (car s))
      (cond
        ((eq? 'newvar expression) 'null) ;for declaration of a new variable
        ((eq? 'true expression) #t)
        ((eq? 'false expression) #f)
        ((symbol? expression) (if (eq? (lookupforfunc expression s name) "undefined") (error expression "undefined") (lookupforfunc expression s name)))
        ((number? expression) expression)
        ((boolean? expression) expression)

        ((eq? 'function (operator expression)) (m_declare_func expression s))  ;Functions
        ((eq? 'funcall  (operator expression)) (m_call_func name expression s instance))
        ((eq? 'static-function (operator expression)) (m_declare_func expression s))
        ((eq? 'dot (operator expression)) (dothandler expression s instance))
        ((eq? 'new (operator expression)) (create_object expression 'null s))

        ((eq? '= (operator expression)) (if (eq? "undefined" operand2) (error 'error "undefined") (m_value_scope (m_value_scope (operand2 expression) s name instance) (m_state_funcscope expression s name instance) name instance)))
        ((eq? '+ (operator expression)) (+ (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '- (operator expression)) (if (null? (cddr expression))
                                            (- 0 (m_value_scope (operand1 expression) s name instance))
                                            (- (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance))))
        ((eq? '* (operator expression)) (* (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '/ (operator expression)) (quotient (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '% (operator expression)) (remainder (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '== (operator expression)) (eq? (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '!= (operator expression)) (not (eq? (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance))))
        ((eq? '> (operator expression)) (> (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '>= (operator expression)) (>= (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '< (operator expression)) (< (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '<= (operator expression)) (<= (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '&& (operator expression)) (and (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '|| (operator expression)) (or (m_value_scope (operand1 expression) s name instance) (m_value_scope (operand2 expression) s name instance)))
        ((eq? '! (logicsymbol expression)) (not (m_value_scope (operand1 expression) s name instance)))
        (else expression)) 
        ;(else (error expression "unknown"))) 
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

(define whilehandler_scope
  (lambda (name line state throw return instance)
    (call/cc (lambda (break)
          (if (not (m_value_scope (cadr line) state name instance))
            (break state)
            (whilehandler_scope name line (call/cc (lambda (continue) (perform (caddr line) state break continue throw return))) throw return instance))))))



;Abstractions

;prefix parser
(define operator
  (lambda (input)
    (car input)))

(define logicsymbol
  (lambda (input)
    (car input)))

(define operand1
  (lambda (input)
    (cadr input)))

(define operand2
  (lambda (input)
    (caddr input)))

;Performs the task of a given line, by calling the method that pertains to the line's opening.
(define perform
  (lambda (line state break continue throw return)
      (cond
        
        ((eq? (cadr line) 'state) (return state))


        ((eq? (operator line) 'var) (m_declare line state))
        ((eq? (operator line) 'throw) (throwhandler line state throw))
        ((eq? (operator line) '=) (m_state line state))
        ;return needs revamp (immediate break)
        ((or (eq? (operator line) 'return) (eq? (operator line) 'throw)) 
                            (cond
                                    ((eq? (cadr line) 'state) (return state))
                                    ;above line is for debugging
                                    ((eq? (return (m_value (cadr line) state)) #t) (display 'true))
                                    ((eq? (return (m_value (cadr line) state)) #f) (display 'false))
                                    (else (display (return (m_value (cadr line) state))))
                                    ))


        ((eq? (operator line) 'if) (ifhandler line state break continue throw return))
        ((eq? (operator line) 'while) (whilehandler line state throw return)) 

        ((eq? (car line) 'begin) 
           (cdr (blockhandler (cdr line) (cons state state) break continue throw return))
           ) ;block handler  
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

        (else (m_value line state)) ;functions will be dealt here to M_value

      )))

(define perform_with_scope
  ;state here is current scope
  (lambda (name line state break continue throw return instance)
      (cond
        ((eq? (cadr line) 'state)
         (return (display state)))
        
        ((eq? (operator line) 'var) (m_declare_inscope line state name instance))
        ((eq? (operator line) 'throw) (throwhandler line state throw))
        ;x = a in a function scope, if x doesn't exist in func scope, goto global
        ((eq? (operator line) '=) (m_state_funcscope line state name instance))
        ;return needs revamp (immediate break)
        ((or (eq? (operator line) 'return) (eq? (operator line) 'throw)) 
                            (cond
                                    ((eq? (cadr line) 'state) (return state))
                                    ;above line is for debugging
                                    ((eq? (return (m_value_scope (cadr line) state name instance)) #t) (display 'true))
                                    ((eq? (return (m_value_scope (cadr line) state name instance)) #f) (display 'false))
                                    (else (display (return (m_value_scope (cadr line) state name instance))))
                                    ))


        ((eq? (operator line) 'if) (ifhandler_scope name line state break continue throw return instance))
        ((eq? (operator line) 'while) (whilehandler_scope name line state throw return instance)) 

        ((eq? (car line) 'begin) 
           (cdr (blockhandler (cdr line) (cons state state) break continue throw return))
           ) ;block handler  
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

        (else (m_value_scope line state name instance)) ;functions will be dealt here to M_value

      )))





;Ifhandler - does its clause if the condition is met. If condition is not met, AND an else clause is present, performs the else clause.
(define ifhandler
  (lambda (line state break continue throw return)
    (cond
      ((eq? (m_value (cadr line) state) #t) (perform (caddr line) state break continue throw return))
      ((null? (itemn line 4)) state)
      (else (perform (itemn line 4) state break continue throw return)))))

(define ifhandler_scope
  (lambda (name line state break continue throw return)
    (cond
      ((eq? (m_value_scope (cadr line) state name instance) #t) (perform_with_scope name (caddr line) state break continue throw return))
      ((null? (itemn line 4)) state)
      (else (perform_with_scope name (itemn line 4) state break continue throw return)))))



;find the nth item in a list
 (define itemn
   (lambda (l n) 
      (cond
        ((null? l) '())
        ((eq? n 0) '())
        ((eq? n 1) (car l))
        (else (itemn (cdr l) (- n 1))))))



;block is handled via continuation of break and continue
(define blockhandler
  (lambda (line s break continue throw return)

            (cond 
              ((empty? (cdr line)) (perform (car line) s (lambda (v) (break (cdr v))) (lambda (v) (continue (cdr v))) (lambda (v) (throw (cdr v))) return)) 
              (else 
                (blockhandler (cdr line) (perform (car line) s (lambda (v) (break (cdr v))) (lambda (v) (continue (cdr v))) (lambda (v) (throw (cdr v))) return) break continue throw return)))
    
    )
  )


;try to perform in the scope
(define func_blockhandler
  (lambda (name line s break continue throw return instance)
            (cond 
              ((empty? (cdr line)) (perform_with_scope name (car line)  s (lambda (v) (break (cdr v))) (lambda (v) (continue (cdr v))) (lambda (v) (throw (cdr v))) return instance)) 
              (else 
                (func_blockhandler name (cdr line) (perform_with_scope name (car line)  s (lambda (v) (break (cdr v))) (lambda (v) (continue (cdr v))) (lambda (v) (throw (cdr v))) return instance) break continue throw return instance)))
    
    )
  )
        


;--------------------------- sample solution --------------------

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

;this will return the state layer with global vars and function defs
(define getrootlayer
  (lambda (currentlayer)
    (cond 
      ((empty? currentlayer) currentlayer)
      ((empty? (cddr currentlayer)) currentlayer)
      (else (getrootlayer (cdr currentlayer)))
      )
  ))    

(define getotherlayers
  (lambda (currentlayer)
    (cond 
      ((empty? currentlayer) currentlayer)
      ((empty? (cddr currentlayer)) '())
      (else (cons (car currentlayer) (getotherlayers (cdr currentlayer))))
      )
  ))

(define getfirstlayer
  (lambda (currentlayer)
    (cond 
      ((empty? currentlayer) currentlayer)
      ((empty? (cddr currentlayer)) currentlayer)
      (else (car currentlayer))
      )
  ))


(define def_in_root
  (lambda (state name val)
    (append (getotherlayers state) (def_with_func name val (getrootlayer state)))
    )
  )

(define def_in_scope
  (lambda (state name val)
    (if (not (layered state)) (def_with_func name val state)
    (cons (def_with_func name val (car state)) (cdr state)))
    ))


;function is parsed as:
;(function name (parameter) body)
(define m_declare_func
  (lambda (line state)
    (def_in_scope
      state 
      (itemn line 2) ;the name of the function/class
      (cond
        ((empty? (itemn line 3)) (makeclosure (intialize_formal_params (itemn line 3) '(()())) (itemn line 3) (itemn line 4)))
        ((eq? (car (itemn line 3)) 'extends) (makeclosure '(()()) (cadr (itemn line 3)) (itemn line 4)))
        (else (makeclosure (intialize_formal_params (itemn line 3) '(()())) (itemn line 3) (itemn line 4)))
        ) ;the function is stored as a closure with its scope, formal param list and its body
      )
    )
  )

;initializing the formal parameters to null in the function scope
(define intialize_formal_params 
  (lambda (lis state)
    (cond 
      ((empty? lis) state)
      (else (intialize_formal_params (cdr lis) (def_null (car lis) state)))
      ) 
    )
  )


;function construting the function closure that would be stored
(define makeclosure 
  (lambda (environment paramlist body)
    (if (or (empty? paramlist) (empty? environment))
      (cons (box environment) (append (list paramlist) (list body)))
      (cons (box environment) (append (list paramlist) (list body)))
    )
  )
)


;function call line would be parsed as '(funcall fib (- a 1))
;(define m_call_func
;  (lambda (line state)
;    (call/cc 
;      (lambda (return)
;        (perform_func
;          (itemn line 2)
;          (caddr (lookup (itemn line 2) state))
;          ;(set_func_scope (itemn line 2)
;           (set_formal_params ;we evaluate the formal parameters
;            (cddr line)
;            (cadr (lookup (itemn line 2) state))
;            state
;            (unbox (car (lookup (itemn line 2) state))))
;          ;state)
;            return
;        )      
;      )
;    )
;  )
;)

;now line item 2 would not be the name of the func, but body of the func
;not implemented correctly
(define m_call_func
  (lambda (name line state instance)
    (call/cc 
      (lambda (return)
        (perform_func
          name
          (caddr (dothandler (itemn line 2) state (getobject (cadr (itemn line 2)) instance state)))
          ;(set_func_scope (itemn line 2)
           (set_formal_params ;we evaluate the formal parameters
            (cddr line)
            (cadr (dothandler (itemn line 2) state (getobject (cadr (itemn line 2)) instance state)))
            state
            (unbox (car (dothandler (itemn line 2) state (getobject (cadr (itemn line 2)) instance state)))))
          ;state)
            return
            (getobject (cadr (itemn line 2)) instance state) ;instance name
            
        )      
      )
    )
  )
)

(define getobject
  (lambda (nominalname instance state)
      (cond
        ((eq? 'this nominalname) instance) ; like calling this.xxx in instance a
        ((eq? 'null instance) nominalname) ; like calling a.getX() in main 
        ((eq? 'super nominalname) (error 'ayy "lmao"))
        (else instance)
        )
    )
  )

;running the body of func, it would create a new frame of state and pop off when finishing
(define perform_func 
  (lambda (name body state return instance)
    (cdr 
      (func_blockhandler
        name
        body
        ; (cons '(()()) state)
        state
        ;(cons '(()()) state)
        (lambda (v) (error "break error"))
        (lambda (v) (error "continue error"))
        (lambda (v) (error "throw error")) 
        return
        instance
      )
    )
  )
)


;help function that counts number of element in a list
(define howmany (lambda (list) 
  (if (pair? list)
    (foldl (lambda (v a) (+ 1 a))  0 list)
    0
  )
))

;

(define set_formal_params (lambda (params formals state funcscope)
    (cond
      ((and (null? params) (null? formals)) (cons '(()()) state)) ;no parameter operation involved, just pass through
      ((not (eq?  (howmany params) (howmany formals))) (error 'set_formal_params "arguments error"))
      ((or (null? (cdr params)) (null? (cdr formals))) 
        (cons (m_manual_state
          (car formals)
          (m_value (car params) state)
          funcscope
          ) state))
      (else (m_manual_state
        (car formals)
        (m_value (car params) state)
          (set_formal_params
            (cdr params)
            (cdr formals)
            state
            funcscope)
          ))
      )))




(define inscope?
  (lambda (name entirestates)

      (not (eq? (lookup name (getfirstlayer entirestates)) "undefined"))
    )
  )



;-----------------------------------------------------------------------------------------------------------
;----------------------------------------------class-------------------------------------------------------
;-----------------------------------------------------------------------------------------------------------


; (class class_name extends body)

(define m_declare_class
  (lambda (line state)

    (m_declare_func line state)
  )
)


; classes parsed after toplevel runthrough:
; test1: '((A) (#&(#&(() ()) () ((var x 5) (var y 10) (static-function main () ((var a (new A)) (return (+ (dot a x) (dot a y)))))))))
; then we run the body of the classes to a state ((x y main) (5 10 mainfuncbody))
; '((A) (#&(#&(() ()) () ((x y main) (5 10 (.....))))))
; then run the main similar in Part 3
; after a=new A(); it should gives something like '((A a) (#&(#&(() ()) () ((x y main) (5 10 (.....))))  #&(("truetype is A") ((x y )) (5 10))) ))


; top level of the state: Raw classes and New objects, no variables; vars must be in a class now.

(define process_classes
  (lambda (state)
    (cond 
      ((empty? (car state)) state)
      ((isfunc (caar state) state) (if (box? (itemn (lookup (caar state) state) 3))
        (combine (extract state) (process_classes (remain state)))
        (begin (set-box! (lookupbox (caar state) state) 
          (cons (itemn (lookup (caar state) state) 1) 
          (cons (itemn (lookup (caar state) state) 2) 
          (list (box (interpret2 (itemn (lookup (caar state) state) 3))))))) (combine (extract state) (process_classes (remain state))))
      ))
      (else (combine (extract state) (process_classes (remain state))))
    )
  )
)

;run the main func in last defined class (has to be the case)

;scoping not quite right yet
(define m_run_main
  (lambda (state)
    (call/cc (lambda (return)
      (perform_func
          'main
          (caddr (lookup 'main (unbox (itemn (lookup (last (car state)) state) 3)))) ;body of main
          ;(set_func_scope (itemn line 2)
          ;(cons '(()())
            (set_formal_params ;we evaluate the formal parameters
            '()
            (cadr (lookup 'main (unbox (itemn (lookup (last (car state)) state) 3))))
            state
            (unbox (car (lookup 'main (unbox (itemn (lookup (last (car state)) state) 3))))))
            ;)
          ;state)
            return
            (last (car state)) ;instance class of main
          )
    ))
    ;(begin (set-box! (itemn (lookup (last (car state)) state) 3) (callmain (unbox (itemn (lookup (last (car state)) state) 3)))) state)))
  )
)


(define m_run_class
  (lambda (state)
    ;(lookup)
    1
  )
)

;no constructor yet (new A)
(define create_object
  (lambda (line objectname state)
    (makeclosure_object (cadr line) objectname (caddr (lookup (cadr line) state)))
  )
)

(define makeclosure_object
  (lambda (truetype objectname instancefields)
    (cons (list truetype) (append (list objectname) (list instancefields)))
  )
)

(define getinstancefieldlist
  (lambda (objname state) 
    (if (eq? "undefined" (lookup objname state))
      (getinstancefieldlist objname (cdr state))
     (caddr (lookup objname state)))
  )
)


; (dot a x)
; works on fields
; operand2 line : field/method   add/x
; operand1 line : objname     a

(define dothandler
  (lambda (line state instance)
    (cond 
      ((eq? 'this (operand1 line)) (lookup (operand2 line)  (unbox (getinstancefieldlist instance state)) )) ;bypass to class field ;not implemented correctly yet
      ;((eq? 'new (car (operand1 line))) (lookup (operand2 line)  () ))
      ((eq? 'super (operand1 line)) (lookup (operand2 line)  (unbox (getinstancefieldlist instance state)) ))
      ((isfunc (operand2 line) (unbox (getinstancefieldlist (operand1 line) state))) (lookup (operand2 line) (unbox (getinstancefieldlist (operand1 line) state))))
      (else (lookup (operand2 line) (unbox (caddr (lookup (operand1 line) state)))))
    )
  )
)

;this
;"this" is almost correct, the variable set-box! set to all of the instances of the same class regardless, might want to do a manual state update rather than set-box!

;super





