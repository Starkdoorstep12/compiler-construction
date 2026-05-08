(define (countdown [n : Integer]) : Integer
  (let ([acc 0])
    (begin
      (while (>= n 0)
        (begin
          (set! acc (+ acc n))
          (set! n (- n 1))))
      acc)))

(countdown 5)
