(set-logic ALL)
(declare-datatypes ((Arr_rc 0)(T_rc 0)) 
(((nil_Int_T) (cons (car T_rc) (cdr Arr_rc)))
((nT_rc) (cons_rc (id_rc Int) (arr_rc Arr_rc)))))
(declare-fun f (Arr_rc) (Array Int T_rc))
(declare-fun g ((Array Int T_rc)) Arr_rc)

(declare-fun x_rc_2 () T_rc)
(assert (= x_rc_2 (select (f (arr_rc x_rc_2)) 0)))
(assert (not (= x_rc_2 nT_rc)))
;;; assertions::post-nesteddtl end
(assert (let ((_let_1 (f (arr_rc x_rc_2)))) (= (select _let_1 0) (car (g _let_1)))))
(assert (let ((_let_1 (arr_rc x_rc_2))) (= _let_1 (g (f _let_1)))))
(check-sat)
