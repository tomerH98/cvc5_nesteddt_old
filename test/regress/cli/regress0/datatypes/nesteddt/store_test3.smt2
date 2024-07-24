; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const a (Array Int T))
(declare-const b (Array Int T))

; using store to create (assert (= x (select a 0)))
(assert (= a (store b 0 x)))

(assert (= a (arr x)))
(assert (not (= x nT)))

(check-sat)