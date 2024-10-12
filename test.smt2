;;; assertions::post-nesteddtl start
(set-logic ALL)
(declare-datatypes ((Arr 0)(T 0)) (((nil_Int_T) (cons (car T) (cdr Arr)))((nT_rc) (cons_rc (id_rc Int) (arr_rc Arr)))))
(declare-fun f (Arr) (Array Int T))
(declare-fun g ((Array Int T)) Arr)
(declare-const x_rc_2 T)
(assert (= x_rc_2 (select (f (g (f (arr_rc x_rc_2)))) 0)))
(assert (not (= x_rc_2 nT_rc)))
(assert (= (arr_rc x_rc_2) (g (f (arr_rc x_rc_2)))))
(assert (= (f (arr_rc x_rc_2)) (f (g (f (arr_rc x_rc_2))))))
;;; assertions::post-nesteddtl end 
;(assert (not (= nil_Int_T (g (f (arr_rc x_rc_2))))))
;(assert (let ((_let_1 (g (f (arr_rc x_rc_2))))) (= (select (f _let_1) 0) (car _let_1))))
(check-sat)
