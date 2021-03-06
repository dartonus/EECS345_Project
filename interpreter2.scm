#lang racket/load
(load "simpleParser.scm")
(load "lex.scm")

;Team: Callum Grant (chg33), Jiawei Wu (jxw585), John Donnelly (jed126)

;-------------------------start-----------------------------

;usage: ex: (interpret "test1.txt")

(define interpret
  (lambda (filename)
    (call/cc (lambda (return)
    (interpreter (parser filename) newstate newbreak newcontinue return)))
    )
  )

;Interpretation method, runs through each sublist within the list of lists returned by parser, effectively going through the original text line-by-line.

(define interpreter
    (lambda (parsed s break continue return)
        ;intializing a state variable 
        (cond
          ((null? parsed) s)
          ((layered s) (interpreter (cdr parsed) (cons (perform (car parsed) (car s) break continue return) (cdr s)) break continue return))
          ((pair? (car parsed)) (interpreter (cdr parsed) (perform (car parsed) s break continue return) break continue return))
          (else (interpreter (cdr parsed) (perform parsed s break continue return) break continue return))
        )
      )
 )
;-------------------------end-----------------------------

;initializations
(define newstate '(()()))
(define newbreak (lambda (v) v))
(define newcontinue (lambda (v) v))

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



(define m_insert
  (lambda (name value s)
    (if (layered s)
      (cons (m_insert name value (car s)) (cdr s))
      (append (list (append (car s) (list name))) (list (append (cadr s) (list (box (m_value value s))))))
      )
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
          (else (lookup name (remain s)))
      )

        (if (eq? "undefined" (lookup name (car s)))
          (lookup name (cdr s))
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



; Assigns a value to a variable, and modifies our state accordingly.


(define m_state
  (lambda (expression s)
        (if (eq? (lookup (cadr expression) s) "undefined")
          (error 'error "Use before declaration")
          (if (layered s)
            (begin (set-box! (lookupbox (cadr expression) s) (m_value (caddr expression) (car s))) s)
            (begin (set-box! (lookupbox (cadr expression) s) (m_value (caddr expression) s)) s)
          )
        )
      )
  )

; Declares a given variable
(define m_declare
  (lambda (expression s)
    (if (layered s)
      (cons (m_declare expression (car s)) (cdr s))
        (if (eq? (car expression) 'var)
          (if (not (null? (cddr expression)))
            (def_with_value (cadr expression) (m_value (caddr expression) s) s) ;parse "var x (things)" (what about declare booleans?)
            (def_null (cadr expression) s);else parse "var x"
          )
          "not valid declare"
        )
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

; If the defined variable has no value, this helper sets it up with a null value.
(define def_null
  (lambda (var s)
    (cond ((not (eq? (lookup var s) "undefined")) (begin (error 'error "no re-declaring") (s))) ;no re-declaring
          (else (m_insert var 'null s)))
  )
)


;Modified version of the basic expression evaluator from class.
(define m_value
  (lambda (expression s)
    (if (layered s) (m_value expression (car s))
      (cond
        ((eq? 'null expression) 'null) ;for declaration of a new variable
        ((eq? 'true expression) #t)
        ((eq? 'false expression) #f)
        ((symbol? expression) (lookup expression s))
        ((number? expression) expression)
        ((boolean? expression) expression)
        ((eq? '= (operator expression)) (m_value (m_value (operand2 expression) s) (m_state expression s)))
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
        ((eq? '&& (operator expression)) (and (evaluate (operand1 expression) s) (evaluate (operand2 expression) s)))
        ((eq? '|| (operator expression)) (or (evaluate (operand1 expression) s) (evaluate (operand2 expression) s)))
        (else (error 'unknown "unknown"))))

      ))

;prefix parser
(define operator
  (lambda (input)
    (car input)))


; Whilehandler addresses situations of the while loop. If the condition is not met, it performs the clause and then recurs.
; state - the state. line - the line that the while occurs in (i.e. the segment enclosed by parentheses, starting with "while")
; (cadr line) - gets the element that is second in the provided line, which should be the clause for the while loop.
; (caddr line) gets the third element in the provided line, which should be the procedure for the while loop.
(define whilehandler
  (lambda (line state return)
    (call/cc (lambda (break)
          (if (not (evaluate (cadr line) state))
            (break state)
            (whilehandler line (call/cc (lambda (continue)(perform (caddr line) state break continue return))) return))))))
;while with call/cc of break and continue passed from perform

; Evaluate is a shortened version of the earlier expression evaluator, intended for use with logical clauses such as those used by If and While.
(define evaluate
  (lambda (line state)
    (cond
      ((number? line) line)
      ((symbol? line) (lookup line state))
      ((eq? '== (logicsymbol line)) (eq? (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '!= (logicsymbol line)) (not (eq? (m_value (operand1 line) state) (m_value (operand2 line) state))))
      ((eq? '> (logicsymbol line)) (> (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '>= (logicsymbol line)) (>= (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '< (logicsymbol line)) (< (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '<= (logicsymbol line)) (<= (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '&& (logicsymbol line)) (and (evaluate (operand1 line) state) (evaluate (operand2 line) state)))
      ((eq? '|| (logicsymbol line)) (or (evaluate (operand1 line) state) (evaluate (operand2 line) state)))
      ((eq? '! (logicsymbol line)) (not (m_value (operand1 line) state)))
      (else (error 'unknown "unknown")))))

;Definitions to avoid having to repeatedly type "car", "cadr", and "caddr" for Evaluate, and make it clear what is being grabbed in each case.
;Abstractions
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
  (lambda (line state break continue return)
      (cond
        ( (eq? (operator line) 'var) (m_declare line state))
        ((eq? (operator line) 'throw) (m_declare (cons 'var line) state))
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


        ((eq? (operator line) 'if) (ifhandler line state break continue return))
        ((eq? (operator line) 'while) (whilehandler line state return)) 

        ((eq? (car line) 'begin) 
           (cdr (blockhandler (cdr line) (cons state state) break continue return))
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
        ; try catch block all contains braces, so adding and stripping layers of states are present
        ((eq? (operator line) 'try) (cdr (tryhandler line (cons state state) break continue return)))
        ((eq? (operator line) 'catch) (cdr (catchhandler line (cons state state) break continue return)))
        ((eq? (operator line) 'finally) (cdr (perform (cadr line) (cons state state) break continue return)))
        (else state)

      )))



;Ifhandler - does its clause if the condition is met. If condition is not met, AND an else clause is present, performs the else clause.
(define ifhandler
  (lambda (line state break continue return)
    (cond
      ((eq? (evaluate (cadr line) state) #t) (perform (caddr line) state break continue return))
      ((null? (itemn line 4)) state)
      (else (perform (itemn line 4) state break continue return)))))


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
  (lambda (line s break continue return)

            (cond 
              ((empty? (cdr line)) (perform (car line) s (lambda (v) (break (cdr v))) (lambda (v) (continue (cdr v))) return)) 
              (else 
                (blockhandler (cdr line) (perform (car line) s (lambda (v) (break (cdr v))) (lambda (v) (continue (cdr v))) return) break continue return)))
    
    )
  )
        

(define tryhandler 
  (lambda (line s break continue return) 
    (cond 
      ((empty? (itemn line 2)) (error 'error "Not a valid try block")) ;try body empty : ???
      ((empty? (itemn line 3)) (interpreter (itemn line 4) (interpreter (itemn line 2) s break continue return) break continue return)) ;no catch, perform try body then finally
      ((empty? (itemn line 4)) (interpreter (itemn line 3) (interpreter (itemn line 2) s break continue return) break continue return)) ;no finally, perform try body then catch
      (else (interpreter (itemn line 4) (interpreter (itemn line 3) (interpreter (itemn line 2) s break continue return) break continue return) break continue return))
      ;normal try catch block, gets run sequentially
      )
  )
)

; intepreting catch, assign thrown to the variable
(define catchhandler 
  (lambda (line s break continue return) 
    (interpreter (caddr line) (def_with_value (caadr line) (lookup 'throw s) s) break continue return) 
    )
<<<<<<< HEAD
  )
=======
  )
>>>>>>> ae7966252347fc8e8f0fe3bb479d2e03837aa5cf
