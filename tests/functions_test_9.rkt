(define (add1 [x : Integer]) : Integer
  (+ x 1))

(define (sub1 [x : Integer]) : Integer
  (- x 1))

(define (apply_twice [f : (Integer -> Integer)]
                     [x : Integer]) : Integer
  (f (f x)))

(+ (apply_twice add1 40)
   (apply_twice sub1 44))
