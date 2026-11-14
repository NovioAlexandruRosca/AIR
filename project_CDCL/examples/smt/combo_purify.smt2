; LIA + DT, purification. head(l) = x + 1 mixes a DT selector with
; arithmetic: it becomes head(l) = k1 (DT) with the definition k1 = x + 1 (LIA).
; With l = cons(y, nil), DT derives k1 = y; LIA then sees y = x + 1 > x.
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-const l List)
(declare-const x Int)
(declare-const y Int)
(assert (= (head l) (+ x 1)))
(assert (= l (cons y nil)))
(assert (> x y))
(check-sat)
