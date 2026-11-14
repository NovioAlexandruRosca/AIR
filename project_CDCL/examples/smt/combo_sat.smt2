; LIA + DT, satisfiable. A two-element list whose elements sum to 8, the
; second one being 5, and a second list that differs from the first.
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-const l List)
(declare-const r List)
(declare-const x Int)
(declare-const y Int)
(assert (= l (cons x (cons y nil))))
(assert (= (head (tail l)) 5))
(assert (= (+ x y) 8))
(assert (or (= r nil) (> (head r) (+ x y))))
(assert (not (= r nil)))
(check-sat)
