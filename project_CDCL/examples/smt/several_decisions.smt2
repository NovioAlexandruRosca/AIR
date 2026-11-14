; Several decisions, two theory conflicts, two learned clauses (Playground).
; A path to try:  x > y := true,  x + z >= 10 := false,  w > x := false
;   -> x <= 3 and z >= 4 are forced; LIA: x > y > z >= 4 needs x >= 6. Conflict.
; Backtrack (keeps the learned clause, which forces w > x), then z >= 4 := true
;   -> LIA: x > y > z >= 4 needs x + z >= 10. Conflict.
; Backtrack again: z < 4 is forced and every assertion is true: sat.
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (or (> x y) (>= z 4) (< w 0)))
(assert (or (not (> x y)) (> y z) (>= (+ x z) 10)))
(assert (or (not (> y z)) (<= x 3) (> w x)))
(assert (or (not (>= z 4)) (<= (+ y z) 2) (<= x 3) (< w 0)))
(assert (or (not (<= x 3)) (> w x) (>= z 4)))
(assert (or (> w x) (< w 0) (>= (+ x z) 10) (> y z)))
(assert (or (not (>= (+ x z) 10)) (<= x 3) (< w 0)))
(check-sat)
