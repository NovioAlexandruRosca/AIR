; Nelson-Oppen with decisions: two one-element lists and their sum.
;   l = [x],  m = [y],  x + y = 10,  head(m) >= 1,
;   (l = m  or  x > y),  (x > 6  or  y < 3)
; Suggested path in the Playground:
;   l = m := true   -> DT (injectivity) derives x = y and gives it to LIA
;   x > 6 := true   -> LIA: x = y and x + y = 10 force x = 5. Conflict.
;   Backtrack       -> learned clause forces x <= 6, then y < 3. Conflict again.
;   Backtrack       -> x > 6 and x != y now hold at level 0.
;   l = m := false  -> x > y; satisfiable: l = [9], m = [1].
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-const l List)
(declare-const m List)
(declare-const x Int)
(declare-const y Int)
(assert (= l (cons x nil)))
(assert (= m (cons y nil)))
(assert (= (+ x y) 10))
(assert (>= (head m) 1))
(assert (or (= l m) (> x y)))
(assert (or (> x 6) (< y 3)))
(check-sat)
