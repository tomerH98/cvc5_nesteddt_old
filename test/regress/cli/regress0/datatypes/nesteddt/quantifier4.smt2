; COMMAND-LINE: --nesteddtl --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
;(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const j Int)
(declare-const a (Array Int T))
(declare-const b (Array Int T))

(assert (forall ((i Int)) (= (select b (+ 1 i)) (select b i))))

(assert (= a (arr x)))
(assert (= (select b 1) x))
(assert (= (select b j) (select a j)))
(assert (= j 15))

(assert (not (= x nT)))

(check-sat)
