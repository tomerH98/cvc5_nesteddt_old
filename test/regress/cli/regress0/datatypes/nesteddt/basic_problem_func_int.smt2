; COMMAND-LINE: --nesteddtl --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const i Int)
(declare-const a (Array Int T))
(declare-fun f (T Int) T)

(assert (= (f x i) (select a 0)))
(assert (= a (arr (f x i))))

(assert (not (= (f x i) nT)))

(check-sat)

