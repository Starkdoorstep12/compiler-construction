(define (add1 [x : Integer]) : Integer
  (+ x 1))

(define (sub1 [x : Integer]) : Integer
  (- x 1))

(define (compose [f : (Integer -> Integer)]
                 [g : (Integer -> Integer)]
                 [x : Integer]) : Integer
  (f (g x)))

(compose add1 sub1 42)
