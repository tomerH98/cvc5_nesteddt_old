; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
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
(declare-const a (Array Int ArrayEx))
(declare-const b ArrayEx)
(declare-const c (Array Int T))

(assert (= a (arr x)))
(assert (= b (select a 0)))
(assert (= c (arr b)))
(assert (= x (select c 0)))

(assert (not (= x nT)))
(assert (not (= b nil)))

(check-sat)

