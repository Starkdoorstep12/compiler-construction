(define (add1 [x : Integer]) : Integer
  (+ x 1))

(define (sub1 [x : Integer]) : Integer
  (- x 1))

(define (twice [f : (Integer -> Integer)]
               [x : Integer]) : Integer
  (f (f x)))

(define (compose [f : (Integer -> Integer)]
                 [g : (Integer -> Integer)]
                 [x : Integer]) : Integer
  (f (g x)))

(+ (twice add1 10)
   (compose add1 sub1 42))
