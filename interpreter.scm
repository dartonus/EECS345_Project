#lang racket/load
(load "simpleParser.scm")
(load "lex.scm")

;write a procedural interpreter here that go through the parsed list (test.txt) using our functions
;or I got the idea wrong?

(define sstate '(() ()))

;this might be something we want?
;might need set! for the state s somewhere along the line
;-------------------------start-----------------------------
(define interpret
  (lambda (parsed s)
    (begin
      ;intializing a state variable 
      (if (not (null? (cdr parsed))) ;if the parsed list is not empty
        (begin (perform (car parsed) s) (interpret (cdr parsed) s)) ;perform (car list) and go interpret (cdr list)
        (begin ("done") (set! sstate '(() ())))
      )
    )
  )
 )
;-------------------------end-----------------------------





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
    (append (list (append (car s) (list name))) (list (append (cadr s) (list (m_value value s)))))
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
    (cond
      ((null? s) s)
      ((empty? (car s)) '())
      ((eq? name (caar s)) (remain s))
      (else (append (list (append (list (car (extract s))) (car (m_remove name (remain s))))) (list (flatten (append (cdr (extract s)) (cdr (m_remove name (remain s))))))))
    )
  )
)


(define lookup
    (lambda (name s)
      (cond 
        ((null? s) "undefined")
        ((empty? (car s)) "undefined")
        ((eq? name (caar s)) (caadr s))
        (else (lookup name (remain s)))
    )
  )
)


;I don't think we need m_name functionally, since the x  in x = 5 is parsed as 'x already
;Maybe declaration needs it?

#|
(define m_name
  (lambda name
    (list name))
)
|#


; expressions like '(= x 5) inplementation (assignment)

(define m_state
  (lambda (expression s)
    (if (eq? (lookup (cadr expression) s) "undefined")
    "error"
      (begin (set! s (m_insert (cadr expression) (m_value (caddr expression) s) (m_remove (cadr expression) s)))
        (lookup (cadr expression) s)
      )
    )
  )
)

;skeleton for declaration parse, working on it

(define m_declare
  (lambda (expression s)
    (if (eq? (car expression) 'var)
      (if (not (null? (cddr expression)))
        (begin (set! sstate (def_with_value (cadr expression) (m_value (caddr expression) s)))
          (lookup (cadr expression) sstate)) ;parse "var x (things)" (what about declare booleans?)
        (begin (set! sstate (def_null (cadr expression) s)) 
          (lookup (cadr expression) sstate));else parse "var x"
      )
      "not valid declare"
    )
  )
)

(define def_with_value
  (lambda (var expression s) 
    (cond ((not (eq? (lookup var s) "undefined")) (begin (error 'error "no re-declaring") (s))) ;no re-declaring
          (else (m_insert var expression s)))
  )
)

(define def_null
  (lambda (var s)
    (cond ((not (eq? (lookup var s) "undefined")) (begin (error 'error "no re-declaring") (s))) ;no re-declaring
          (else (m_insert var 'null s)))
  )
)


;basic expression evaluator used in class

;doesn't have hierachy yet
(define m_value
  (lambda (expression s)
    (cond
      ((eq? 'null expression) 'null) ;for declaration of a new variable
      ((symbol? expression) (lookup expression s))
      ((number? expression) expression)
      ((eq? '+ (operator expression)) (+ (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
      ((eq? '- (operator expression)) (- (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
      ((eq? '* (operator expression)) (* (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
      ((eq? '/ (operator expression)) (quotient (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
      ((eq? '% (operator expression)) (remainder (m_value (operand1 expression) s) (m_value (operand2 expression) s)))
      (else (error 'unknown "unknown")))))

;prefix parser

(define operator
  (lambda (input)
    (car input)))

#|
(define operand1
  (lambda (input)
    (cadr input)))

(define operand2
  (lambda (input)
    (caddr input)))
|#


; state - the state. line - the line that the while occurs in (i.e. the segment enclosed by parentheses, starting with "while")
; (cadr line) - gets the element that is second in the provided line, which should be the clause for the while loop.
; (caddr line) gets the third element in the provided line, which should be the procedure for the while loop.


(define whilehandler
  (lambda (line state)
    (cond
      ((not (eq (evaluate (cadr line) state))) (begin (perform (caddr line)) (whilehandler line state))))))

;assumed functions: "evaluate" - checks a logical equation. "perform" - performs the action of the segment (e.g., defines a variable if an "(= x 10)" segment.)


(define evaluate
  (lambda (line state)
    (cond
      ((number? line) line)
      ((eq? '= (logicsymbol line)) (eq? (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '!= (logicsymbol line)) (not (eq? (m_value (operand1 line) state) (m_value (operand2 line) state))))
      ((eq? '> (logicsymbol line)) (> (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '>= (logicsymbol line)) (>= (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '< (logicsymbol line)) (< (m_value (operand1 line) state) (m_value (operand2 line) state)))
      ((eq? '<= (logicsymbol line)) (<= (m_value (operand1 line) state) (m_value (operand2 line) state)))
      (else (error 'unknown "unknown")))))

(define logicsymbol
  (lambda (input)
    (car input)))

(define operand1
  (lambda (input)
    (cadr input)))

(define operand2
  (lambda (input)
    (caddr input)))

(define perform
  (lambda (line state)
    (cond
      ((eq? (car line) 'var) (m_declare line state))
      ((eq? (car line) '=) (m_state line state))
      ((eq? (car line) 'return) )
      ((eq? (car line) 'if) (ifhandler state line))
      ((eq? (car line) 'while) (whilehandler line state)))))



;work on if
;assumed functions: "evaluate" - checks a logical equation. "perform" - performs the action of the segment
;If the condition is true the first statement needs to be evaluated.
;If it's false then the else must be evaluated
;However the fact that its optional may be an issue

(define ifhandler
  (lambda (state line)
    (cond
      ((eq? (evaluate (cadr line)) #t) (perform (state (caddr line))))
      (else (perform (itemn (line 3)))))))


;find the nth item in a list
 (define itemn
   (lambda (l n) 
      (cond
        ((eq? n 0) '())
        ((eq? n 1) (car l))
        (else (itemn (cdr l) (- n 1))))))
        