; The classic DPLL(T) introduction example (Reynolds, VTSA 2017):
;   (x+1 > 0 or x+y > 0) and (x < 0 or x+y > 4) and not (x+y > 0)
; Propositionally satisfiable, but LIA-unsatisfiable: the theory solver
; rejects the context {x+1>0, not x+y>0, x<0} and adds the theory lemma
; (not x+1>0 or not x<0); after backtracking, {x+1>0, not x+y>0, x+y>4}
; is rejected as well.
(declare-const x Int)
(declare-const y Int)
(assert (or (> (+ x 1) 0) (> (+ x y) 0)))
(assert (or (< x 0) (> (+ x y) 4)))
(assert (not (> (+ x y) 0)))
(check-sat)
