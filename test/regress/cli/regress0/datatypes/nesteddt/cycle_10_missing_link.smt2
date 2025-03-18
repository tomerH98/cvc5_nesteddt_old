; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)
(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))
(declare-const x0 T)
(declare-const a0 (Array Int T))
(declare-const x1 T)
(declare-const a1 (Array Int T))

(assert (= a0 (arr x0)))
(assert (= x1 (select a0 0)))
;(assert (= a1 (arr x1)))
;(assert (= x0 (select a1 0)))
(assert (not (= nT x0)))
(assert (not (= nT x1)))
(check-sat)