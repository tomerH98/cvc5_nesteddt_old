; COMMAND-LINE: --nesteddtl --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const a (Array Int T))

(assert (= x (select a 0)))
(assert (= a (arr x)))

(assert (not (= x nT)))

(check-sat)