; LIA: branch and bound. 2x + 3y = 1 has rational solutions in the box
; [0,3] x [0,3] (x = 1/2, y = 0), but no integer ones. gcd(2,3) = 1, so
; only branching (splits on x <= k) proves it.
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 2 x) (* 3 y)) 1))
(assert (and (>= x 0) (<= x 3) (>= y 0) (<= y 3)))
(check-sat)
