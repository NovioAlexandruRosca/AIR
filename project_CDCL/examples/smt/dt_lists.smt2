; DT: lists with selectors. tail(l) must be a non-empty list whose head is 5.
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-const l List)
(declare-const m List)
(assert ((_ is cons) l))
(assert (= (tail l) m))
(assert (not (= m nil)))
(assert (= (head m) 5))
(check-sat)
