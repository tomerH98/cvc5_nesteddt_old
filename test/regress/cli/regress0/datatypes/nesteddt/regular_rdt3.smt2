; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))
(declare-datatypes ((L 0)) (((nL) (cons (id Int) (arr (Array Int Int)) ) ) ))

(declare-const x T)
(declare-const i Int)
(declare-const a (Array Int T))

(declare-const x2 L)
(declare-const a2 (Array Int Int))

(assert (= a (arr x)))
(assert (= x (select a 0)))
(assert (not (= x nT)))

(assert (= a2 (arr x2)))
(assert (= i (select a2 0)))
(assert (not (= x2 nL)))

(check-sat)
