; COMMAND-LINE: --nesteddt
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const a (Array Int T))
(declare-const b (Array Int T))

(assert (= x (select a 0)))
(assert (= b (store a 0 x)))
(assert (= a (arr x)))
(assert (not (= x nT)))

(check-sat)