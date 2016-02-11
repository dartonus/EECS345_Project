#lang racket
(load "simpleParser.scm")
(load "lex.scm")

#|

;basic expression evaluator used in class

(define returnx
  (lambda (returnx)
    (cond
      ((number? returnx) returnx)
      ((eq? '+ (operator returnx)) (+ (mvalue (operand1 returnx)) (mvalue (operand2 returnx))))
      ((eq? '- (operator returnx)) (- (mvalue (operand1 returnx)) (mvalue (operand2 returnx))))
      ((eq? '* (operator returnx)) (* (mvalue (operand1 returnx)) (mvalue (operand2 returnx))))
      ((eq? '/ (operator returnx)) (quotient (mvalue (operand1 returnx)) (mvalue (operand2 returnx))))
      ((eq? '% (operator returnx)) (remainder (mvalue (operand1 returnx)) (mvalue (operand2 returnx))))
      (else (error 'unknown "unknown")))))

;infix parser

(define operator
  (lambda (input)
    (cadr input)))

(define operand1
  (lambda (input)
    (car input)))

(define operand2
  (lambda (input)
    (caddr input)))


|#

; state - the state. line - the line that the while occurs in (i.e. the segment enclosed by parentheses, starting with "while")
; (cadr line) - gets the element that is second in the provided line, which should be the clause for the while loop.
; (caddr line) gets the third element in the provided line, which should be the procedure for the while loop.
#|(define whilehandler
  (lambda (state line)
    (cond
      ((!eq (evaluate (cadr line)) #t) (begin (perform (caddr line)) (whilehandler state line))))))|#
;assumed functions: "evaluate" - checks a logical equation. "perform" - performs the action of the segment (e.g., defines a variable if an "(= x 10)" segment.)
(define evaluate
  (lambda (state line)
    (cond
      ((number? line) line)
      ((eq? '= (logicsymbol line)) (eq? (mvalue (operand1 line)) (mvalue (operand2 line))))
      ((eq? '!= (logicsymbol line)) (if (eq? (mvalue (operand1 line)) (mvalue (operand2 line)))
                                           #f
                                           #t))
      ((eq? '> (logicsymbol line)) (> (mvalue (operand1 line)) (mvalue (operand2 line))))
      ((eq? '>= (logicsymbol line)) (>= (mvalue (operand1 line)) (mvalue (operand2 line))))
      ((eq? '< (logicsymbol line)) (< (mvalue (operand1 line)) (mvalue (operand2 line))))
      ((eq? '<= (logicsymbol line)) (<= (mvalue (operand1 line)) (mvalue (operand2 line))))
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