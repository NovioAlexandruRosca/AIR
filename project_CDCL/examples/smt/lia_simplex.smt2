; LIA: a Simplex conflict. x + y must reach 10, but x <= 3 and y <= 6.
; The explanation is the Simplex row of the slack s = x + y and the
; bounds that block it (a Farkas certificate).
(declare-const x Int)
(declare-const y Int)
(assert (>= (+ x y) 10))
(assert (<= x 3))
(assert (or (<= y 6) (< (+ x y) 0)))
(check-sat)
