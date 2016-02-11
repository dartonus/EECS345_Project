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