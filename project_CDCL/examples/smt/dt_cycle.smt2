; DT: acyclicity. A list cannot be its own tail: l = cons(1, l) is UNSAT.
; The numeral 1 is an LIA term inside a DT term, so purification
; replaces it by a fresh constant k1 with k1 = 1.
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-const l List)
(assert (= l (cons 1 l)))
(check-sat)
