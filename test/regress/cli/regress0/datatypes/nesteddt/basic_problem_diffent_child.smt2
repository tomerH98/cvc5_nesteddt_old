; COMMAND-LINE: --nesteddtl --dt-blast-splits
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const y T)
(declare-const a (Array Int T))

(assert (= y (select a 0)))
(assert (= a (arr x)))

(assert (not (= x nT)))

(check-sat)
