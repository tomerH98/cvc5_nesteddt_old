; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: sat
; DISABLE-TESTER: model
; This is a simple SMT-LIB file that is satisfiable
(set-logic QF_LIA) ; Set the logic to Quantifier-Free Linear Integer Arithmetic

; Declare an integer variable
(declare-fun x () Int)
(declare-fun y () Int)

; Assert a simple constraint on x
(assert (> x 5))


; Assert a simple constraint on x
(assert (> y 5))


; Check for satisfiability
(check-sat)


; Exit
(exit)
