; DT introduction: colours and lists of colours.
; cons(x, nil) = cons(y, z) gives x = y and z = nil (constructors are
; injective), so x = green. Then x = red is false and x != y is false:
; the second assertion fails, UNSAT.
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((List 0)) (((nil) (cons (head Color) (tail List)))))
(declare-const x Color)
(declare-const y Color)
(declare-const z List)
(assert (= y green))
(assert (or (= x red) (not (= x y))))
(assert (= (cons x nil) (cons y z)))
(check-sat)
