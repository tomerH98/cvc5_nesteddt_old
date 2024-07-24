; COMMAND-LINE: --nesteddt
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)
(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int (Array Int T)))))))
(declare-const x T)
(assert (= x (select (select (arr x) 0) 0)))
(assert (not (= x nT)))
(check-sat)