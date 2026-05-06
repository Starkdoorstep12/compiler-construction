(define (id [x : Integer]) : Integer
  x)

(define (add1 [x : Integer]) : Integer
  (+ (id x) 1))

(add1 41)
