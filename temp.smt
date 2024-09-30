;;; assertions::post-nesteddtl start
(set-logic ALL)
(declare-datatypes ((|nested_datatype_prefix_Array_[Int_T]_rc| 0)(nested_datatype_prefix_T_rc 0)) (((nil_Int_T) (cons (car nested_datatype_prefix_T_rc) (cdr |nested_datatype_prefix_Array_[Int_T]_rc|)))((nT_rc) (cons_rc (id_rc Int) (arr_rc |nested_datatype_prefix_Array_[Int_T]_rc|)))))
(declare-fun |_nested_datatype_prefix_Array_[Int_T]_rc__0_3| (|nested_datatype_prefix_Array_[Int_T]_rc|) (Array Int nested_datatype_prefix_T_rc))
(declare-fun nested_datatype_prefix_reverse_5 ((Array Int nested_datatype_prefix_T_rc)) |nested_datatype_prefix_Array_[Int_T]_rc| )

(declare-fun x_rc_2 () nested_datatype_prefix_T_rc)
(assert (= x_rc_2 (select (|_nested_datatype_prefix_Array_[Int_T]_rc__0_3| (arr_rc x_rc_2)) 0)))
(assert (not (= x_rc_2 nT_rc)))
;;; assertions::post-nesteddtl end
(assert (not (= nil_Int_T (nested_datatype_prefix_reverse_5 (|_nested_datatype_prefix_Array_[Int_T]_rc__0_3| (arr_rc x_rc_2))))))
(assert (let ((_let_1 (|_nested_datatype_prefix_Array_[Int_T]_rc__0_3| (arr_rc x_rc_2)))) (= (select _let_1 0) (car (nested_datatype_prefix_reverse_5 _let_1)))))
(assert (let ((_let_1 (arr_rc x_rc_2))) (= _let_1 (nested_datatype_prefix_reverse_5 (|_nested_datatype_prefix_Array_[Int_T]_rc__0_3| _let_1)))))
(check-sat)
