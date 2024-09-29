(assert (= x_rc_2 (select (|_nested_datatype_prefix_Array_[Int_T]_rc__0_4| a_rc_3) 0)))
(assert (= (|_nested_datatype_prefix_Array_[Int_T]_rc__0_4| a_rc_3) (|_nested_datatype_prefix_Array_[Int_T]_rc__0_4| (arr_rc x_rc_2))))
(assert (not (= x_rc_2 nT_rc)))

(assert (= a_rc_3 (nested_datatype_prefix_reverse_6 (|_nested_datatype_prefix_Array_[Int_T]_rc__0_4| a_rc_3))))
(assert (let ((_let_1 (|_nested_datatype_prefix_Array_[Int_T]_rc__0_4| a_rc_3))) (= (select _let_1 0) (car (nested_datatype_prefix_reverse_6 _let_1)))))