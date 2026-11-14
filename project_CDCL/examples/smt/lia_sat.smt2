; LIA with Boolean structure: a satisfiable schedule.
; Two tasks of length 3 and 2 on one machine, in [0, 6), not overlapping.
(declare-const a Int)
(declare-const b Int)
(assert (and (>= a 0) (>= b 0) (<= (+ a 3) 6) (<= (+ b 2) 6)))
(assert (or (<= (+ a 3) b) (<= (+ b 2) a)))
(assert (> a b))
(check-sat)
