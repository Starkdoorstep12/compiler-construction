(let ([x 1])
  (let ([y 2])
    (while (< x 5)
      (begin
        (set! y (+ y x))
        (set! x (+ x 1))))
    y))
