; COMMAND-LINE: --nesteddt --dt-blast-splits
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(
    declare-datatypes ((Array_Int_T_rc 0)(T_rc 0))
    (
        ((nil) (cons (id Int) (index_0 T_rc)))
        ((nT_rc) (cons_rc (id_rc Int) (arr_rc Array_Int_T_rc)))
    )
)

(declare-fun |Array_Int_T_rc_to_(Array Int T_rc)| (Array_Int_T_rc) (Array Int T_rc))
(declare-fun |(Array Int T_rc)_to_Array_Int_T_rc| ((Array Int T_rc)) Array_Int_T_rc)
(declare-const x_rc T_rc)
(declare-const a_rc Array_Int_T_rc)

(assert (= x_rc (select (|Array_Int_T_rc_to_(Array Int T_rc)| a_rc) 0)))
(assert (= (|Array_Int_T_rc_to_(Array Int T_rc)| a_rc) (|Array_Int_T_rc_to_(Array Int T_rc)| (arr_rc x_rc))))
(assert (not (= nT_rc x_rc)))
(assert true)
(assert (let ((_let_1 (|Array_Int_T_rc_to_(Array Int T_rc)| a_rc))) (= (index_0 (|(Array Int T_rc)_to_Array_Int_T_rc| _let_1)) (select _let_1 0))))
(assert (= a_rc (|(Array Int T_rc)_to_Array_Int_T_rc| (|Array_Int_T_rc_to_(Array Int T_rc)| a_rc))))
(assert (not (= a_rc nil)))
(assert (let ((_let_1 (arr_rc x_rc))) (= _let_1 (|(Array Int T_rc)_to_Array_Int_T_rc| (|Array_Int_T_rc_to_(Array Int T_rc)| _let_1)))))
(assert (not (= (arr_rc x_rc) nil)))
(check-sat)
