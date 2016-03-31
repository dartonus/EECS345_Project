;State manipulations and controls


;initializations

(define newbreak (lambda (v) v))
(define newcontinue (lambda (v) v))
(define newthrow (lambda (e s) (error 'throw "No catch")))
; State layers would be boxed
(define newlayer (lambda () '(()())))
(define newstate (lambda () (box (cons (newlayer) '()))))


;abstractions
(define (names l)  (car l))                 (define (values l)  (cadr l))
(define (currentlayer state) (car state))   (define (restlayers state) (cdr state))

(define pushlayer (lambda (env)     (begin (set-box! env (cons (newlayer) (unbox env))) env)))
(define poplayer  (lambda (env)     (begin (set-box! env (cdr (unbox env))) env)))



;find the nth item in a list
 (define itemn
   (lambda (l n) 
      (cond
        ((null? l) '())
        ((eq? n 0) '())
        ((eq? n 1) (car l))
        (else (itemn (cdr l) (- n 1))))))

;find the nth item in a list, starting from 0.
(define itemn0 (lambda (i l)
    (if (= i 0)
      (car l)
      (itemn0 (- i 1) (cdr l))
      )))

; Removes the item in list l.
(define removen (lambda (i l)
    (if (= i 0)
      (cdr l)
      (cons (car l) (removen (- i 1) (cdr l)))
      )))

; Replaces the item n in a list.
(define replacen (lambda (name i l)
    (if (= i 0)
      (cons name (cdr l))
      (cons (car l) (replacen name (- i 1) (cdr l)))
      )))

(define getindex
  (lambda (e lst)
    (if (null? lst)
      -1
      (if (eq? (car lst) e)
        0
        (if (= (getindex e (cdr lst)) -1) 
          -1
          (+ 1 (getindex e (cdr lst))))))))


(define getval 
  (lambda (name layer) 

    (itemn0 (getindex name (names layer)) (values layer))))

(define inscope?  
  (lambda (name layer) 
    (not (eq? -1 (getindex name (names layer))))))

; Declares a new variable in the current layer
(define m_declare (lambda (name state)
    (begin
      (if (not (inscope? name (currentlayer (unbox state))))
        (set-box! state (cons
          (cons (cons name (names (currentlayer (unbox state))))
            (cons (cons (box 0) (values (currentlayer (unbox state)))) '()))
          (restlayers (unbox state))
          ))
        (error "No redeclaration" name))
      state
      )))

; Boolean of whether a var is declared already
(define declared? (lambda (name state)
    (cond
      ((null? state) #f)
      ((inscope? name (currentlayer state)) #t)
      (else (declared? name (restlayers state)))
      )))

; Update a variable in the current layer
(define m_state (lambda (name val state)
    (begin
      (cond
        ((declared? name (unbox state)) (set-box! (lookupbox name state) val))
        (else (error "Undeclared variable:" name)))
      state
      )))

; ; Returns the reference to the given variable.
; (define lookupbox (lambda (name state)
;     (letrec ((search (lambda (name state)
;         (if (inscope? name (currentlayer state))
;           (getval name (currentlayer state))
;           (search name (restlayers state))))))
;       (search name (unbox state)))))

; ; Returns the value of the given variable.
; (define lookup (lambda (name state) (unbox (lookupbox name state))))

