(set-logic ALL)
(
    declare-datatypes ((Array_Int_T_rc 0)(T_rc 0))
    (
        ((nil) (cons (id Int) (index_0 T_rc)))
        ((nT_rc) (cons_rc (id_rc Int) (arr_rc Array_Int_T_rc)))
    )
)

(declare-const x_rc0 T_rc)
(declare-const a_rc0 Array_Int_T_rc)

(declare-const x_rc1 T_rc)
(declare-const a_rc1 Array_Int_T_rc)

(assert (= a_rc0 (arr_rc x_rc0)))
(assert (= x_rc1 (index_0 a_rc0)))
(assert (not (= nT_rc x_rc0)))
(assert (not (= a_rc0 nil)))


(assert (= a_rc1 (arr_rc x_rc1)))
(assert (= x_rc0 (index_0 a_rc1)))
(assert (not (= nT_rc x_rc1)))
(assert (not (= a_rc1 nil)))
(check-sat)
