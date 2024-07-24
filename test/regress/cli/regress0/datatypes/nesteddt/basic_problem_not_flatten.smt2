; COMMAND-LINE: --nesteddt
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const a (Array Int T))

(assert (= x (select (arr x) 0)))
(assert (not (= x nT)))

(check-sat)
