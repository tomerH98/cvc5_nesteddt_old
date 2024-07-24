; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))

(declare-const x T)
(declare-const y T)
(declare-const z T)
(declare-const i Int)
(declare-const a (Array Int T))
(declare-const b (Array Int T))

(assert (= i 0))
(assert (= x (select b 0)))
(assert (= a (store b i y)))

(assert (= a (arr x)))
(assert (not (= x nT)))
(assert (not (= y nT)))

(check-sat)
