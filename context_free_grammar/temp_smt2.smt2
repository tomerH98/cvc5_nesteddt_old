(set-logic ALL)
(set-option :dt-nested-rec true)
(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) )) )
(declare-const t1 T)
(declare-const t2 T)
(declare-const t3 T)
(declare-const i Int)
(assert (not (= t1 nT)))
(assert (not (= t2 nT)))
(assert (not (= t3 nT)))


(assert ( = nT ( select ( store ( arr t2) 2 t1) i)))
(assert ( = t1 ( select ( arr ( select ( store ( arr t2) 2 t1) i)) 2)))

(check-sat)

