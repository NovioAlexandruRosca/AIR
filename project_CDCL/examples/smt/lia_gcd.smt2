; LIA: the GCD test. 2x - 2y = 1 has no integer solution: dividing by
; gcd(2,2) = 2 turns the bounds into x - y <= 0 and x - y >= 1.
(declare-const x Int)
(declare-const y Int)
(assert (= (- (* 2 x) (* 2 y)) 1))
(check-sat)
