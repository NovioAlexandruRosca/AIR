; DT: a finite datatype. Four pairwise different colours do not exist;
; the solver splits on the testers is-red / is-green / is-blue.
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-const a Color)
(declare-const b Color)
(declare-const c Color)
(declare-const d Color)
(assert (distinct a b c d))
(check-sat)
