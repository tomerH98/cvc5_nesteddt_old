;;; assertions::post-nesteddtl start
(set-logic ALL)
(declare-datatypes ((|nested_datatype_prefix_Array_[Int_T]_rc| 0)(nested_datatype_prefix_T_rc 0)) (((nil_Int_T) (cons (car nested_datatype_prefix_T_rc) (cdr |nested_datatype_prefix_Array_[Int_T]_rc|)))((nT_rc) (cons_rc (id_rc Int) (arr_rc |nested_datatype_prefix_Array_[Int_T]_rc|)))))
(declare-fun |_nested_datatype_prefix_Array_[Int_T]_rc__0_3| (|nested_datatype_prefix_Array_[Int_T]_rc|) (Array Int nested_datatype_prefix_T_rc))
(declare-fun x_rc_2 () nested_datatype_prefix_T_rc)
(assert (= x_rc_2 (select (|_nested_datatype_prefix_Array_[Int_T]_rc__0_3| (arr_rc x_rc_2)) 0)))
(assert (not (= x_rc_2 nT_rc)))
;;; assertions::post-nesteddtl end 
(check-sat)

