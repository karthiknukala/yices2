(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(set-option :yices-mcsat-parallel-workers 2)

(declare-fun x () Real)

;; SAT
(assert (> (* x x) 2.0))
(check-sat)

;; UNSAT
(push 1)
(assert (< (* x x) 1.0))
(check-sat)

;; SAT
(pop 1)
(check-sat)

;; UNSAT
(assert (< (* x x) 1.0))
(check-sat)

(exit)
