; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))


(declare-fun R (Int T) Bool)
(declare-fun x () Int)
(declare-fun y () T)

(assert (R x y))
(assert (not (R x y)))

(check-sat)

