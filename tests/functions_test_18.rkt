(define (clamp [x : Integer] [lo : Integer] [hi : Integer]) : Integer
  (if (< x lo)
      lo
      (if (> x hi)
          hi
          x)))

(clamp 10 0 5)
