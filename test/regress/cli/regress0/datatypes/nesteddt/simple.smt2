; COMMAND-LINE: --nesteddtl --dt-blast-splits
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)

(declare-const x Int)
(declare-const a (Array Int Int))

(assert (= x (select a 0)))

(check-sat)
