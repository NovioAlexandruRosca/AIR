; Non-convex combination (Nelson–Oppen needs case splits on the arrangement).
; DT: three singleton lists must be pairwise different, so their heads must be.
; LIA: the heads only range over {1, 2}. Neither theory alone derives an
; equality between x, y, z, but every arrangement fails.
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (and (>= x 1) (<= x 2) (>= y 1) (<= y 2) (>= z 1) (<= z 2)))
(assert (distinct (cons x nil) (cons y nil) (cons z nil)))
(check-sat)
