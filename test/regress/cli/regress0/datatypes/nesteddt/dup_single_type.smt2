; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :dt-nested-rec true)


(
    declare-datatypes ((ArrayEx 0) (T 0)) 
    (
        ((nil) (cons (arr (Array Int T)))) 
        ((nT) (newT (id Int) (arr (Array Int ArrayEx))))
    )
)

(declare-const x T)

(assert (= x (select (arr (select (arr x) 0)) 0)))

(assert (not (= x nT)))
(assert (not (= (select (arr x) 0) nil)))

(check-sat)

