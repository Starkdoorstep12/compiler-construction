(define (f [x : Integer]) : Integer
  (+ x 1))

(define (g [y : Integer]) : Integer
  (f y))

(g 41)
