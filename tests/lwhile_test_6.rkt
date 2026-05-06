(let ([x 0])
  (let ([y 0])
    (begin
      (while (< x 4)
        (begin
          (let ([z 0])
            (while (< z x)
              (begin
                (set! y (+ y z))
                (set! z (+ z 1)))))
          (set! x (+ x 1))))
      y)))
