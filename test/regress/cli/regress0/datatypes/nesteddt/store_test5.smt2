; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const y T)
(declare-const z T)
(declare-const a (Array Int T))
(declare-const b (Array Int T))
(declare-const c (Array Int T))

(assert (= x (select c 0)))
(assert (= b (store c 1 y)))
(assert (= a (store b 2 z)))

(assert (= a (arr x)))
(assert (not (= x nT)))

(check-sat)