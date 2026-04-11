(let ([v (vector 0)])
  (let ([i 0])
    (while (< i 5)
      (begin
        (vector-set! v 0 (+ (vector-ref v 0) 1))
        (set! i (+ i 1))))
    (vector-ref v 0)))
