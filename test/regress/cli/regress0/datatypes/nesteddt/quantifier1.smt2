; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const a (Array Int T))

(assert (forall ((a1 (Array Int T))) (= x (select a1 0))))

(assert (= a (arr x)))
(assert (= x (select a 0)))


(assert (not (= x nT)))

(check-sat)
