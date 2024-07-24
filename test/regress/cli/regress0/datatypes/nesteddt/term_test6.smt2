; COMMAND-LINE: --nesteddt
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))


(declare-fun R (Int T) Bool)
(declare-fun x () Int)
(declare-fun y () T)

(assert (R x y))
(assert (not (R x y)))

(check-sat)

