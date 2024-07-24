; COMMAND-LINE: --nesteddt
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :dt-nested-rec true)

(declare-datatypes ((T 0)) (((nT) (cons (id Int) (seq (Seq T)) ) ) ))

(declare-const x T)
(declare-const s (Seq T))

(assert (= x (seq.nth s 0)))
(assert (= s (seq x)))
(assert (not (= x nT)))

(check-sat)
