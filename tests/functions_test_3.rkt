(define (sum_to [n : Integer]) : Integer
  (let ([acc 0])
    (let ([i 0])
      (begin
        (while (< i n)
          (begin
            (set! acc (+ acc i))
            (set! i (+ i 1))))
        acc))))

(sum_to 5)
