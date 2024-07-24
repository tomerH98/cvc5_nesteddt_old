; COMMAND-LINE: --nesteddt
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-fun R (Int) Bool)
(declare-fun x () Int)

(assert (R x))
(assert (not (R x)))

(check-sat)

