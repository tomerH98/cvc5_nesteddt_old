; COMMAND-LINE: --nesteddt  --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
; This is a simple SMT-LIB file that is satisfiable
(set-logic ALL) ; Set the logic to Quantifier-Free Linear Integer Arithmetic
    
(declare-fun x () Int)
(declare-fun y () Int)
(declare-const a (Array Int Int))

; Assert a simple constraint on x
(assert (= (+ x (select a 0)) 5))
(assert (= x 4))
(assert (= (select a 0) 2))


; Check for satisfiability
(check-sat)


; Exit
(exit)
