; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-fun R (T) Bool)

(assert (R x))

(check-sat)

