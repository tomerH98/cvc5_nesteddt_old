; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const y T)

(declare-const a (Array Int T))
(declare-const b (Array Int T))


(assert (= a (arr x)))
(assert (= b (store a 1 y)))
(assert (= x (select b 0)))

(assert (not (= x nT)))

(check-sat)

