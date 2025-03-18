; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-fun R (Int) Bool)
(declare-fun x () Int)

(assert (R x))
(assert (not (R x)))

(check-sat)

