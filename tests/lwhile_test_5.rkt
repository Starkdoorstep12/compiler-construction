(let ([x 0])
  (let ([y 0])
    (begin
      (while (< x 3)
        (begin
          (set! y (+ y x))
          (set! x (+ x 1))))
      (while (< y 10)
        (set! y (+ y 2)))
      y)))
