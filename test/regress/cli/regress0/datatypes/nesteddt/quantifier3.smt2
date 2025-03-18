; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const a (Array Int T))
(declare-const b (Array Int T))

(assert (forall ((i Int)) (= (select a (* 2 i)) (select b i))))

(assert (= a (arr x)))
(assert (= (select b 1) x))


(assert (not (= x nT)))

(check-sat)
