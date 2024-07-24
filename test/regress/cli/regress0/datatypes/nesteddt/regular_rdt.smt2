; COMMAND-LINE: --nesteddt
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int Int)) ) ) ))

(declare-const x T)
(declare-const i Int)
(declare-const a (Array Int Int))

(assert (= i (select a 0)))
(assert (= a (arr x)))
(assert (not (= x nT)))

(check-sat)
