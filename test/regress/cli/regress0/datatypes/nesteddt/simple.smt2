; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)

(declare-const x Int)
(declare-const y Int)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))

(assert (= x (select b 0)))
(assert (= b  (store a 1 y)))

(check-sat)
