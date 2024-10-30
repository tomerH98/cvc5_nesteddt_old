; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))
(declare-datatypes ((L 0)) (((nL) (cons (b T) ) ) ))

(declare-const x L)
(declare-const a (Array Int T))

(assert (= (b x) (select a 0)))
(assert (= a (arr (b x))))

(assert (not (= (b x) nT)))
(assert (not (= x nL)))
(check-sat)
