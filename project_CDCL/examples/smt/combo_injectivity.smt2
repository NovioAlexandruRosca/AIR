; LIA + DT, Nelson-Oppen equality exchange.
; DT: cons(x, nil) = cons(y, nil) implies x = y (injectivity).
; LIA receives x = y through the shared constants and refutes x < y.
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-const x Int)
(declare-const y Int)
(assert (= (cons x nil) (cons y nil)))
(assert (< x y))
(check-sat)
