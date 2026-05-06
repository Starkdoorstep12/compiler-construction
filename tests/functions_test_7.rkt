(define (id [x : Integer]) : Integer x)

(define (compose
          [f : (Integer -> Integer)]
          [g : (Integer -> Integer)]
          [x : Integer]) : Integer
  (f (g x)))

(compose id id 42)
