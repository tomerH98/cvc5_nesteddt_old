; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const a (Array Int T))
(declare-const b (Array Int T))

(assert (= x (select a 0)))
(assert (= b (store a 1 x)))
(assert (not (= x nT)))
(assert (not (= (select b 0) (select b 1))))

(check-sat)