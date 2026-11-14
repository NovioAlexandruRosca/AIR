; Step-by-step example: deciding x > y forces x + 1 < y (F2), which LIA
; rejects. Conflict analysis learns not(x > y); after backtracking it
; propagates x > y to false, then F1 and F3 force x > z and z > y, which LIA
; also rejects: unsatisfiable.
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (or (> x y) (> x z)))
(assert (or (< (+ x 1) y) (not (> x y))))
(assert (or (> x y) (> z y)))
(check-sat)
