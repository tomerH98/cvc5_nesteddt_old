; using cav@cav20-artifact:~/artifact/libra/language/move-prover/bytecode-to-boogie$ time cargo run test_mvir/verify-stdlib/test-func-call.mvir --output test-func-call.bpl --boogie-exe ~/boogie/Binaries/boogie -B /useArrayTheory --z3-exe /usr/bin/z3 --boogie /proverLog:test-func-call.smt2
(set-logic ALL)
(set-option :dt-nested-rec true)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :AUTO_CONFIG false)
(set-option :pp.bv_literals false)
(set-option :MODEL.V2 true)
(set-option :smt.PHASE_SELECTION 0)
(set-option :smt.RESTART_STRATEGY 0)
(set-option :smt.RESTART_FACTOR |1.5|)
(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
(set-option :smt.CASE_SPLIT 3)
(set-option :smt.DELAY_UNITS true)
(set-option :NNF.SK_HACK true)
(set-option :smt.MBQI false)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :TYPE_CHECK true)
(set-option :smt.BV.REFLECT true)
(set-option :model_compress false)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-sort T@ByteArray 0)
(declare-datatypes ((T@Transaction 0)) (((Transaction (|gas_unit_price#Transaction| Int) (|max_gas_units#Transaction| Int) (|public_key#Transaction| T@ByteArray) (|sender#Transaction| Int) (|sequence_number#Transaction| Int) (|gas_remaining#Transaction| Int) ) ) ))
(declare-sort T@String 0)
(declare-datatypes ((T@Value 0)(T@ValueArray 0)) (((Boolean (|b#Boolean| Bool) ) (Integer (|i#Integer| Int) ) (Address (|a#Address| Int) ) (ByteArray (|b#ByteArray| T@ByteArray) ) (Str (|a#Str| T@String) ) (Vector (|v#Vector| T@ValueArray) ) ) ((ValueArray (|v#ValueArray| (Array Int T@Value)) (|l#ValueArray| Int) ) ) ))
(declare-sort T@TypeName 0)
(declare-datatypes ((T@TypeValue 0)(T@TypeValueArray 0)) (((BooleanType ) (IntegerType ) (AddressType ) (ByteArrayType ) (StrType ) (VectorType (|t#VectorType| T@TypeValue) ) (StructType (|name#StructType| T@TypeName) (|ts#StructType| T@TypeValueArray) ) ) ((TypeValueArray (|v#TypeValueArray| (Array Int T@TypeValue)) (|l#TypeValueArray| Int) ) ) ))
(declare-datatypes ((T@Location 0)) (((Global (|t#Global| T@TypeValue) (|a#Global| Int) ) (Local (|i#Local| Int) ) ) ))
(declare-datatypes ((T@Memory 0)) (((Memory (|domain#Memory| (Array T@Location Bool)) (|contents#Memory| (Array T@Location T@Value)) ) ) ))
(declare-datatypes ((T@Path 0)) (((Path (|p#Path| (Array Int Int)) (|size#Path| Int) ) ) ))
(declare-datatypes ((T@Reference 0)) (((Reference (|l#Reference| T@Location) (|p#Reference| T@Path) ) ) ))
(declare-fun EmptyPath () T@Path)
(declare-fun path_index_at (T@Path Int) Int)
(declare-fun EmptyTypeValueArray () T@TypeValueArray)
(declare-fun DefaultTypeValue () T@TypeValue)
(declare-fun ExtendTypeValueArray (T@TypeValueArray T@TypeValue) T@TypeValueArray)
(declare-fun MAX_U8 () Int)
(declare-fun MAX_U64 () Int)
(declare-fun MAX_U128 () Int)
(declare-fun max_u64 () T@Value)
(declare-fun EmptyValueArray () T@ValueArray)
(declare-fun DefaultValue () T@Value)
(declare-fun AddValueArray (T@ValueArray T@Value) T@ValueArray)
(declare-fun RemoveValueArray (T@ValueArray) T@ValueArray)
(declare-fun ConcatValueArray (T@ValueArray T@ValueArray) T@ValueArray)
(declare-fun |lambda#0| (Int (Array Int T@Value) (Array Int T@Value) Int) (Array Int T@Value))
(declare-fun ReverseValueArray (T@ValueArray) T@ValueArray)
(declare-fun |lambda#1| (Int Int (Array Int T@Value) Int Int T@Value) (Array Int T@Value))
(declare-fun ExtendValueArray (T@ValueArray T@Value) T@ValueArray)
(declare-fun UpdateValueArray (T@ValueArray Int T@Value) T@ValueArray)
(declare-fun SwapValueArray (T@ValueArray Int Int) T@ValueArray)
(declare-fun IsEmpty (T@ValueArray) Bool)
(declare-fun StratificationDepth () Int)
(declare-fun IsEqual4 (T@Value T@Value) Bool)
(declare-fun IsEqual3 (T@Value T@Value) Bool)
(declare-fun vlen (T@Value) Int)
(declare-fun vmap (T@Value) (Array Int T@Value))
(declare-fun IsEqual2 (T@Value T@Value) Bool)
(declare-fun IsEqual1 (T@Value T@Value) Bool)
(declare-fun IsEqual (T@Value T@Value) Bool)
(declare-fun ReadValue4 (T@Path T@Value) T@Value)
(declare-fun ReadValue3 (T@Path T@Value) T@Value)
(declare-fun ReadValue2 (T@Path T@Value) T@Value)
(declare-fun ReadValue1 (T@Path T@Value) T@Value)
(declare-fun ReadValue0 (T@Path T@Value) T@Value)
(declare-fun ReadValue (T@Path T@Value) T@Value)
(declare-fun UpdateValue4 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue3 (T@Path T@Value T@Value) T@Value)
(declare-fun update_vector (T@Value Int T@Value) T@Value)
(declare-fun UpdateValue2 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue1 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue0 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue (T@Path T@Value T@Value) T@Value)
(declare-fun mk_vector () T@Value)
(declare-fun push_back_vector (T@Value T@Value) T@Value)
(declare-fun pop_back_vector (T@Value) T@Value)
(declare-fun append_vector (T@Value T@Value) T@Value)
(declare-fun reverse_vector (T@Value) T@Value)
(declare-fun swap_vector (T@Value Int Int) T@Value)
(declare-fun EmptyMemory () T@Memory)
(declare-fun GetLocal (T@Memory Int) T@Value)
(declare-fun UpdateLocal (T@Memory Int T@Value) T@Memory)
(declare-fun ExistsResourceRaw (T@Memory T@TypeValue Int) Bool)
(declare-fun ExistsResource (T@Memory T@TypeValue Int) T@Value)
(declare-fun GetResourceReference (T@TypeValue Int) T@Reference)
(declare-fun GetLocalReference (Int Int) T@Reference)
(declare-fun SelectFieldFromRef (T@Reference Int) T@Reference)
(declare-fun SelectField (T@Value Int) T@Value)
(declare-fun Dereference (T@Memory T@Reference) T@Value)
(declare-fun ExistsTxnSenderAccount (T@Memory T@Transaction) Bool)
(declare-fun LibraAccount_T_type_value () T@TypeValue)
(declare-fun TxnSenderAddress (T@Transaction) Int)
(assert (= (|size#Path| EmptyPath) 0))
(assert (forall ((p T@Path) (i Int) ) (! (= (path_index_at p i) (select (|p#Path| p) i))
 :qid |testfunc.18:36|
 :skolemid |0|
 :pattern ( (path_index_at p i))
)))
(assert (= (|l#TypeValueArray| EmptyTypeValueArray) 0))
(assert (= (|v#TypeValueArray| EmptyTypeValueArray) ((as const (Array Int T@TypeValue)) DefaultTypeValue)))
(assert (forall ((ta T@TypeValueArray) (tv T@TypeValue) ) (! (= (ExtendTypeValueArray ta tv) (TypeValueArray (store (|v#TypeValueArray| ta) (|l#TypeValueArray| ta) tv) (+ (|l#TypeValueArray| ta) 1)))
 :qid |testfunc.45:43|
 :skolemid |1|
 :pattern ( (ExtendTypeValueArray ta tv))
)))
(assert (= MAX_U8 255))
(assert (= MAX_U64 9223372036854775807))
(assert (= MAX_U128 340282366920938463463374607431768211456))
(assert (= max_u64 (Integer 9223372036854775807)))
(assert (= (|l#ValueArray| EmptyValueArray) 0))
(assert (= (|v#ValueArray| EmptyValueArray) ((as const (Array Int T@Value)) DefaultValue)))
(assert (forall ((a T@ValueArray) (v T@Value) ) (! (= (AddValueArray a v) (ValueArray (store (|v#ValueArray| a) (|l#ValueArray| a) v) (+ (|l#ValueArray| a) 1)))
 :qid |testfunc.104:36|
 :skolemid |2|
 :pattern ( (AddValueArray a v))
)))
(assert (forall ((a@@0 T@ValueArray) ) (! (= (RemoveValueArray a@@0) (ValueArray (store (|v#ValueArray| a@@0) (|l#ValueArray| a@@0) DefaultValue) (- (|l#ValueArray| a@@0) 1)))
 :qid |testfunc.108:39|
 :skolemid |3|
 :pattern ( (RemoveValueArray a@@0))
)))
(assert (forall ((a1 T@ValueArray) (a2 T@ValueArray) ) (! (= (ConcatValueArray a1 a2) (ValueArray (|lambda#0| (|l#ValueArray| a1) (|v#ValueArray| a1) (|v#ValueArray| a2) (|l#ValueArray| a1)) (+ (|l#ValueArray| a1) (|l#ValueArray| a2))))
 :qid |testfunc.111:39|
 :skolemid |4|
 :pattern ( (ConcatValueArray a1 a2))
)))
(assert (forall ((a@@1 T@ValueArray) ) (! (= (ReverseValueArray a@@1) (ValueArray (|lambda#1| 0 (|l#ValueArray| a@@1) (|v#ValueArray| a@@1) (|l#ValueArray| a@@1) 1 DefaultValue) (|l#ValueArray| a@@1)))
 :qid |testfunc.116:40|
 :skolemid |5|
 :pattern ( (ReverseValueArray a@@1))
)))
(assert (forall ((a@@2 T@ValueArray) (elem T@Value) ) (! (= (ExtendValueArray a@@2 elem) (ValueArray (store (|v#ValueArray| a@@2) (|l#ValueArray| a@@2) elem) (+ (|l#ValueArray| a@@2) 1)))
 :qid |testfunc.122:39|
 :skolemid |6|
 :pattern ( (ExtendValueArray a@@2 elem))
)))
(assert (forall ((a@@3 T@ValueArray) (i@@0 Int) (elem@@0 T@Value) ) (! (= (UpdateValueArray a@@3 i@@0 elem@@0) (ValueArray (store (|v#ValueArray| a@@3) i@@0 elem@@0) (|l#ValueArray| a@@3)))
 :qid |testfunc.125:39|
 :skolemid |7|
 :pattern ( (UpdateValueArray a@@3 i@@0 elem@@0))
)))
(assert (forall ((a@@4 T@ValueArray) (i@@1 Int) (j Int) ) (! (= (SwapValueArray a@@4 i@@1 j) (ValueArray (store (store (|v#ValueArray| a@@4) i@@1 (select (|v#ValueArray| a@@4) j)) j (select (|v#ValueArray| a@@4) i@@1)) (|l#ValueArray| a@@4)))
 :qid |testfunc.128:37|
 :skolemid |8|
 :pattern ( (SwapValueArray a@@4 i@@1 j))
)))
(assert (forall ((a@@5 T@ValueArray) ) (!  (and (=> (IsEmpty a@@5) (= (|l#ValueArray| a@@5) 0)) (=> (= (|l#ValueArray| a@@5) 0) (IsEmpty a@@5)))
 :qid |testfunc.131:30|
 :skolemid |9|
 :pattern ( (IsEmpty a@@5))
)))
(assert (= StratificationDepth 4))
(assert (forall ((v1 T@Value) (v2 T@Value) ) (!  (and (=> (IsEqual4 v1 v2) (= v1 v2)) (=> (= v1 v2) (IsEqual4 v1 v2)))
 :qid |testfunc.146:31|
 :skolemid |10|
 :pattern ( (IsEqual4 v1 v2))
)))
(assert (forall ((v1@@0 T@Value) (v2@@0 T@Value) ) (!  (and (=> (IsEqual3 v1@@0 v2@@0) (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@2) (select (vmap v2@@0) i@@2)))
 :qid |testfunc.154:14|
 :skolemid |11|
))))) (=> (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@3 Int) ) (!  (=> (and (<= 0 i@@3) (< i@@3 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@3) (select (vmap v2@@0) i@@3)))
 :qid |testfunc.154:14|
 :skolemid |11|
)))) (IsEqual3 v1@@0 v2@@0)))
 :qid |testfunc.149:31|
 :skolemid |12|
 :pattern ( (IsEqual3 v1@@0 v2@@0))
)))
(assert (forall ((v1@@1 T@Value) (v2@@1 T@Value) ) (!  (and (=> (IsEqual2 v1@@1 v2@@1) (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@4 Int) ) (!  (=> (and (<= 0 i@@4) (< i@@4 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@4) (select (vmap v2@@1) i@@4)))
 :qid |testfunc.161:14|
 :skolemid |13|
))))) (=> (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@5 Int) ) (!  (=> (and (<= 0 i@@5) (< i@@5 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@5) (select (vmap v2@@1) i@@5)))
 :qid |testfunc.161:14|
 :skolemid |13|
)))) (IsEqual2 v1@@1 v2@@1)))
 :qid |testfunc.156:31|
 :skolemid |14|
 :pattern ( (IsEqual2 v1@@1 v2@@1))
)))
(assert (forall ((v1@@2 T@Value) (v2@@2 T@Value) ) (!  (and (=> (IsEqual1 v1@@2 v2@@2) (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@6 Int) ) (!  (=> (and (<= 0 i@@6) (< i@@6 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@6) (select (vmap v2@@2) i@@6)))
 :qid |testfunc.168:14|
 :skolemid |15|
))))) (=> (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@7 Int) ) (!  (=> (and (<= 0 i@@7) (< i@@7 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@7) (select (vmap v2@@2) i@@7)))
 :qid |testfunc.168:14|
 :skolemid |15|
)))) (IsEqual1 v1@@2 v2@@2)))
 :qid |testfunc.163:31|
 :skolemid |16|
 :pattern ( (IsEqual1 v1@@2 v2@@2))
)))
(assert (forall ((v1@@3 T@Value) (v2@@3 T@Value) ) (!  (and (=> (IsEqual v1@@3 v2@@3) (IsEqual1 v1@@3 v2@@3)) (=> (IsEqual1 v1@@3 v2@@3) (IsEqual v1@@3 v2@@3)))
 :qid |testfunc.170:30|
 :skolemid |17|
 :pattern ( (IsEqual v1@@3 v2@@3))
)))
(assert (forall ((p@@0 T@Path) (v@@0 T@Value) ) (! (= (ReadValue4 p@@0 v@@0) v@@0)
 :qid |testfunc.174:33|
 :skolemid |18|
 :pattern ( (ReadValue4 p@@0 v@@0))
)))
(assert (forall ((p@@1 T@Path) (v@@1 T@Value) ) (! (= (ReadValue3 p@@1 v@@1) (ite (= 3 (|size#Path| p@@1)) v@@1 (ReadValue4 p@@1 (select (vmap v@@1) (path_index_at p@@1 3)))))
 :qid |testfunc.177:33|
 :skolemid |19|
 :pattern ( (ReadValue3 p@@1 v@@1))
)))
(assert (forall ((p@@2 T@Path) (v@@2 T@Value) ) (! (= (ReadValue2 p@@2 v@@2) (ite (= 2 (|size#Path| p@@2)) v@@2 (ReadValue3 p@@2 (select (vmap v@@2) (path_index_at p@@2 2)))))
 :qid |testfunc.183:33|
 :skolemid |20|
 :pattern ( (ReadValue2 p@@2 v@@2))
)))
(assert (forall ((p@@3 T@Path) (v@@3 T@Value) ) (! (= (ReadValue1 p@@3 v@@3) (ite (= 1 (|size#Path| p@@3)) v@@3 (ReadValue2 p@@3 (select (vmap v@@3) (path_index_at p@@3 1)))))
 :qid |testfunc.189:33|
 :skolemid |21|
 :pattern ( (ReadValue1 p@@3 v@@3))
)))
(assert (forall ((p@@4 T@Path) (v@@4 T@Value) ) (! (= (ReadValue0 p@@4 v@@4) (ite (= 0 (|size#Path| p@@4)) v@@4 (ReadValue1 p@@4 (select (vmap v@@4) (path_index_at p@@4 0)))))
 :qid |testfunc.195:33|
 :skolemid |22|
 :pattern ( (ReadValue0 p@@4 v@@4))
)))
(assert (forall ((p@@5 T@Path) (v@@5 T@Value) ) (! (= (ReadValue p@@5 v@@5) (ReadValue0 p@@5 v@@5))
 :qid |testfunc.201:32|
 :skolemid |23|
 :pattern ( (ReadValue p@@5 v@@5))
)))
(assert (forall ((p@@6 T@Path) (v@@6 T@Value) (new_v T@Value) ) (! (= (UpdateValue4 p@@6 v@@6 new_v) new_v)
 :qid |testfunc.205:35|
 :skolemid |24|
 :pattern ( (UpdateValue4 p@@6 v@@6 new_v))
)))
(assert (forall ((p@@7 T@Path) (v@@7 T@Value) (new_v@@0 T@Value) ) (! (= (UpdateValue3 p@@7 v@@7 new_v@@0) (ite (= 3 (|size#Path| p@@7)) new_v@@0 (update_vector v@@7 (path_index_at p@@7 3) (UpdateValue4 p@@7 (select (vmap v@@7) (path_index_at p@@7 3)) new_v@@0))))
 :qid |testfunc.208:35|
 :skolemid |25|
 :pattern ( (UpdateValue3 p@@7 v@@7 new_v@@0))
)))
(assert (forall ((p@@8 T@Path) (v@@8 T@Value) (new_v@@1 T@Value) ) (! (= (UpdateValue2 p@@8 v@@8 new_v@@1) (ite (= 2 (|size#Path| p@@8)) new_v@@1 (update_vector v@@8 (path_index_at p@@8 2) (UpdateValue3 p@@8 (select (vmap v@@8) (path_index_at p@@8 2)) new_v@@1))))
 :qid |testfunc.214:35|
 :skolemid |26|
 :pattern ( (UpdateValue2 p@@8 v@@8 new_v@@1))
)))
(assert (forall ((p@@9 T@Path) (v@@9 T@Value) (new_v@@2 T@Value) ) (! (= (UpdateValue1 p@@9 v@@9 new_v@@2) (ite (= 1 (|size#Path| p@@9)) new_v@@2 (update_vector v@@9 (path_index_at p@@9 1) (UpdateValue2 p@@9 (select (vmap v@@9) (path_index_at p@@9 1)) new_v@@2))))
 :qid |testfunc.220:35|
 :skolemid |27|
 :pattern ( (UpdateValue1 p@@9 v@@9 new_v@@2))
)))
(assert (forall ((p@@10 T@Path) (v@@10 T@Value) (new_v@@3 T@Value) ) (! (= (UpdateValue0 p@@10 v@@10 new_v@@3) (ite (= 0 (|size#Path| p@@10)) new_v@@3 (update_vector v@@10 (path_index_at p@@10 0) (UpdateValue1 p@@10 (select (vmap v@@10) (path_index_at p@@10 0)) new_v@@3))))
 :qid |testfunc.226:35|
 :skolemid |28|
 :pattern ( (UpdateValue0 p@@10 v@@10 new_v@@3))
)))
(assert (forall ((p@@11 T@Path) (v@@11 T@Value) (new_v@@4 T@Value) ) (! (= (UpdateValue p@@11 v@@11 new_v@@4) (UpdateValue0 p@@11 v@@11 new_v@@4))
 :qid |testfunc.232:34|
 :skolemid |29|
 :pattern ( (UpdateValue p@@11 v@@11 new_v@@4))
)))
(assert (forall ((v@@12 T@Value) ) (! (= (vmap v@@12) (|v#ValueArray| (|v#Vector| v@@12)))
 :qid |testfunc.239:27|
 :skolemid |30|
 :pattern ( (vmap v@@12))
)))
(assert (forall ((v@@13 T@Value) ) (! (= (vlen v@@13) (|l#ValueArray| (|v#Vector| v@@13)))
 :qid |testfunc.242:27|
 :skolemid |31|
 :pattern ( (vlen v@@13))
)))
(assert (= mk_vector (Vector EmptyValueArray)))
(assert (forall ((v@@14 T@Value) (elem@@1 T@Value) ) (! (= (push_back_vector v@@14 elem@@1) (Vector (AddValueArray (|v#Vector| v@@14) elem@@1)))
 :qid |testfunc.248:39|
 :skolemid |32|
 :pattern ( (push_back_vector v@@14 elem@@1))
)))
(assert (forall ((v@@15 T@Value) ) (! (= (pop_back_vector v@@15) (Vector (RemoveValueArray (|v#Vector| v@@15))))
 :qid |testfunc.251:38|
 :skolemid |33|
 :pattern ( (pop_back_vector v@@15))
)))
(assert (forall ((v1@@4 T@Value) (v2@@4 T@Value) ) (! (= (append_vector v1@@4 v2@@4) (Vector (ConcatValueArray (|v#Vector| v1@@4) (|v#Vector| v2@@4))))
 :qid |testfunc.254:36|
 :skolemid |34|
 :pattern ( (append_vector v1@@4 v2@@4))
)))
(assert (forall ((v@@16 T@Value) ) (! (= (reverse_vector v@@16) (Vector (ReverseValueArray (|v#Vector| v@@16))))
 :qid |testfunc.257:37|
 :skolemid |35|
 :pattern ( (reverse_vector v@@16))
)))
(assert (forall ((v@@17 T@Value) (i@@8 Int) (elem@@2 T@Value) ) (! (= (update_vector v@@17 i@@8 elem@@2) (Vector (UpdateValueArray (|v#Vector| v@@17) i@@8 elem@@2)))
 :qid |testfunc.260:36|
 :skolemid |36|
 :pattern ( (update_vector v@@17 i@@8 elem@@2))
)))
(assert (forall ((v@@18 T@Value) (i@@9 Int) (j@@0 Int) ) (! (= (swap_vector v@@18 i@@9 j@@0) (Vector (SwapValueArray (|v#Vector| v@@18) i@@9 j@@0)))
 :qid |testfunc.263:34|
 :skolemid |37|
 :pattern ( (swap_vector v@@18 i@@9 j@@0))
)))
(assert (= (|domain#Memory| EmptyMemory) ((as const (Array T@Location Bool)) false)))
(assert (= (|contents#Memory| EmptyMemory) ((as const (Array T@Location T@Value)) DefaultValue)))
(assert (forall ((m T@Memory) (idx Int) ) (! (= (GetLocal m idx) (select (|contents#Memory| m) (Local idx)))
 :qid |testfunc.316:31|
 :skolemid |38|
 :pattern ( (GetLocal m idx))
)))
(assert (forall ((m@@0 T@Memory) (idx@@0 Int) (v@@19 T@Value) ) (! (= (UpdateLocal m@@0 idx@@0 v@@19) (Memory (store (|domain#Memory| m@@0) (Local idx@@0) true) (store (|contents#Memory| m@@0) (Local idx@@0) v@@19)))
 :qid |testfunc.320:34|
 :skolemid |39|
 :pattern ( (UpdateLocal m@@0 idx@@0 v@@19))
)))
(assert (forall ((m@@1 T@Memory) (resource T@TypeValue) (addr Int) ) (!  (and (=> (ExistsResourceRaw m@@1 resource addr) (select (|domain#Memory| m@@1) (Global resource addr))) (=> (select (|domain#Memory| m@@1) (Global resource addr)) (ExistsResourceRaw m@@1 resource addr)))
 :qid |testfunc.335:40|
 :skolemid |40|
 :pattern ( (ExistsResourceRaw m@@1 resource addr))
)))
(assert (forall ((m@@2 T@Memory) (resource@@0 T@TypeValue) (addr@@0 Int) ) (! (= (ExistsResource m@@2 resource@@0 addr@@0) (Boolean (ExistsResourceRaw m@@2 resource@@0 addr@@0)))
 :qid |testfunc.338:37|
 :skolemid |41|
 :pattern ( (ExistsResource m@@2 resource@@0 addr@@0))
)))
(assert (forall ((resource@@1 T@TypeValue) (addr@@1 Int) ) (! (= (GetResourceReference resource@@1 addr@@1) (Reference (Global resource@@1 addr@@1) EmptyPath))
 :qid |testfunc.343:43|
 :skolemid |42|
 :pattern ( (GetResourceReference resource@@1 addr@@1))
)))
(assert (forall ((frame_idx Int) (idx@@1 Int) ) (! (= (GetLocalReference frame_idx idx@@1) (Reference (Local (+ frame_idx idx@@1)) EmptyPath))
 :qid |testfunc.348:40|
 :skolemid |43|
 :pattern ( (GetLocalReference frame_idx idx@@1))
)))
(assert (forall ((ref T@Reference) (field Int) ) (! (= (SelectFieldFromRef ref field) (Reference (|l#Reference| ref) (Path (store (|p#Path| (|p#Reference| ref)) (|size#Path| (|p#Reference| ref)) field) (+ (|size#Path| (|p#Reference| ref)) 1))))
 :qid |testfunc.353:41|
 :skolemid |44|
 :pattern ( (SelectFieldFromRef ref field))
)))
(assert (forall ((val T@Value) (field@@0 Int) ) (! (= (SelectField val field@@0) (select (vmap val) field@@0))
 :qid |testfunc.361:34|
 :skolemid |45|
 :pattern ( (SelectField val field@@0))
)))
(assert (forall ((m@@3 T@Memory) (ref@@0 T@Reference) ) (! (= (Dereference m@@3 ref@@0) (ReadValue (|p#Reference| ref@@0) (select (|contents#Memory| m@@3) (|l#Reference| ref@@0))))
 :qid |testfunc.366:34|
 :skolemid |46|
 :pattern ( (Dereference m@@3 ref@@0))
)))
(assert (forall ((m@@4 T@Memory) (txn T@Transaction) ) (!  (and (=> (ExistsTxnSenderAccount m@@4 txn) (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn)))) (=> (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn))) (ExistsTxnSenderAccount m@@4 txn)))
 :qid |testfunc.371:45|
 :skolemid |47|
 :pattern ( (ExistsTxnSenderAccount m@@4 txn))
)))
(assert (forall ((txn@@0 T@Transaction) ) (! (= (TxnSenderAddress txn@@0) (|sender#Transaction| txn@@0))
 :qid |testfunc.380:39|
 :skolemid |48|
 :pattern ( (TxnSenderAddress txn@@0))
)))
(assert (forall ((i@@10 Int) (|l#0| Int) (|l#1| (Array Int T@Value)) (|l#2| (Array Int T@Value)) (|l#3| Int) ) (! (= (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10) (ite (< i@@10 |l#0|) (select |l#1| i@@10) (select |l#2| (- i@@10 |l#3|))))
 :qid |testfunc.113:17|
 :skolemid |49|
 :pattern ( (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10))
)))
(assert (forall ((i@@11 Int) (|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| (Array Int T@Value)) (|l#3@@0| Int) (|l#4| Int) (|l#5| T@Value) ) (! (= (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11) (ite  (and (<= |l#0@@0| i@@11) (< i@@11 |l#1@@0|)) (select |l#2@@0| (- (- |l#3@@0| i@@11) |l#4|)) |l#5|))
 :qid |testfunc.118:17|
 :skolemid |50|
 :pattern ( (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11))
)))
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%+1 () Bool)
(declare-fun %lbl%+2 () Bool)
(declare-fun inline$AddU64$0$src1@0 () T@Value)
(declare-fun inline$AddU64$0$src2@0 () T@Value)
(declare-fun inline$AddU64$0$dst@1 () T@Value)
(declare-fun abort_flag@0 () Bool)
(declare-fun abort_flag () Bool)
(declare-fun %lbl%+3 () Bool)
(declare-fun %lbl%+4 () Bool)
(declare-fun %lbl%+5 () Bool)
(declare-fun m@2 () T@Memory)
(declare-fun local_counter () Int)
(declare-fun %lbl%+6 () Bool)
(declare-fun m@1 () T@Memory)
(declare-fun inline$LdConst$0$ret@1 () T@Value)
(declare-fun %lbl%+7 () Bool)
(declare-fun %lbl%+8 () Bool)
(declare-fun m@0 () T@Memory)
(declare-fun inline$CopyOrMoveValue$0$local@0 () T@Value)
(declare-fun %lbl%+9 () Bool)
(declare-fun %lbl%+10 () Bool)
(declare-fun x () T@Value)
(declare-fun local_counter@0 () Int)
(declare-fun m@@5 () T@Memory)
(declare-fun %lbl%+11 () Bool)
(declare-fun %lbl%@12 () Bool)
(declare-fun txn@@1 () T@Transaction)
(declare-fun %lbl%+13 () Bool)
(declare-fun %lbl%+14 () Bool)
(push 1)
(set-info :boogie-vc-id TestFuncCall_f_verify)
(assert (not
(let ((inline$TestFuncCall_f$0$anon3_Else_correct  (=> (! (and %lbl%+0 true) :lblpos +0) true)))
(let ((inline$TestFuncCall_f$0$anon3_Then_correct  (=> (! (and %lbl%+1 true) :lblpos +1) true)))
(let ((inline$AddU64$0$anon3_Else_correct  (=> (! (and %lbl%+2 true) :lblpos +2) (=> (and (and (>= MAX_U64 (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0))) (= inline$AddU64$0$dst@1 (Integer (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0))))) (and (=> abort_flag@0 abort_flag) (=> abort_flag abort_flag@0))) (and inline$TestFuncCall_f$0$anon3_Then_correct inline$TestFuncCall_f$0$anon3_Else_correct)))))
(let ((inline$AddU64$0$anon3_Then_correct  (=> (! (and %lbl%+3 true) :lblpos +3) (=> (> (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0)) MAX_U64) (=> (and (=> abort_flag@0 true) (=> true abort_flag@0)) (and inline$TestFuncCall_f$0$anon3_Then_correct inline$TestFuncCall_f$0$anon3_Else_correct))))))
(let ((inline$AddU64$0$anon0_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (=> (and (and (and (is-Integer inline$AddU64$0$src1@0) (>= (|i#Integer| inline$AddU64$0$src1@0) 0)) (<= (|i#Integer| inline$AddU64$0$src1@0) MAX_U64)) (and (and (is-Integer inline$AddU64$0$src2@0) (>= (|i#Integer| inline$AddU64$0$src2@0) 0)) (<= (|i#Integer| inline$AddU64$0$src2@0) MAX_U64))) (and inline$AddU64$0$anon3_Then_correct inline$AddU64$0$anon3_Else_correct)))))
(let ((inline$AddU64$0$Entry_correct  (=> (! (and %lbl%+5 true) :lblpos +5) (=> (and (= inline$AddU64$0$src1@0 (GetLocal m@2 (+ local_counter 1))) (= inline$AddU64$0$src2@0 (GetLocal m@2 (+ local_counter 2)))) inline$AddU64$0$anon0_correct))))
(let ((inline$TestFuncCall_f$0$anon0$2_correct  (=> (! (and %lbl%+6 true) :lblpos +6) (=> (= m@2 (UpdateLocal m@1 (+ local_counter 2) inline$LdConst$0$ret@1)) inline$AddU64$0$Entry_correct))))
(let ((inline$LdConst$0$anon0_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> (= inline$LdConst$0$ret@1 (Integer 1)) inline$TestFuncCall_f$0$anon0$2_correct))))
(let ((inline$TestFuncCall_f$0$anon0$1_correct  (=> (! (and %lbl%+8 true) :lblpos +8) (=> (= m@1 (UpdateLocal m@0 (+ local_counter 1) inline$CopyOrMoveValue$0$local@0)) inline$LdConst$0$anon0_correct))))
(let ((inline$CopyOrMoveValue$0$Entry_correct  (=> (! (and %lbl%+9 true) :lblpos +9) (=> (= inline$CopyOrMoveValue$0$local@0 (GetLocal m@0 (+ local_counter 0))) inline$TestFuncCall_f$0$anon0$1_correct))))
(let ((inline$TestFuncCall_f$0$anon0_correct  (=> (! (and %lbl%+10 true) :lblpos +10) (=> (not abort_flag) (=> (and (and (and (is-Integer x) (>= (|i#Integer| x) 0)) (<= (|i#Integer| x) MAX_U64)) (and (= local_counter@0 (+ local_counter 4)) (= m@0 (UpdateLocal m@@5 (+ local_counter 0) x)))) inline$CopyOrMoveValue$0$Entry_correct)))))
(let ((inline$TestFuncCall_f$0$Entry_correct  (=> (! (and %lbl%+11 true) :lblpos +11) (and (! (or %lbl%@12 (ExistsTxnSenderAccount m@@5 txn@@1)) :lblneg @12) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestFuncCall_f$0$anon0_correct)))))
(let ((anon0_correct  (=> (! (and %lbl%+13 true) :lblpos +13) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestFuncCall_f$0$Entry_correct))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+14 true) :lblpos +14) anon0_correct)))
PreconditionGeneratedEntry_correct))))))))))))))
))
(check-sat)
(pop 1)
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :AUTO_CONFIG false)
(set-option :pp.bv_literals false)
(set-option :MODEL.V2 true)
(set-option :smt.PHASE_SELECTION 0)
(set-option :smt.RESTART_STRATEGY 0)
(set-option :smt.RESTART_FACTOR |1.5|)
(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
(set-option :smt.CASE_SPLIT 3)
(set-option :smt.DELAY_UNITS true)
(set-option :NNF.SK_HACK true)
(set-option :smt.MBQI false)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :TYPE_CHECK true)
(set-option :smt.BV.REFLECT true)
(set-option :model_compress false)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-sort T@ByteArray 0)
(declare-datatypes ((T@Transaction 0)) (((Transaction (|gas_unit_price#Transaction| Int) (|max_gas_units#Transaction| Int) (|public_key#Transaction| T@ByteArray) (|sender#Transaction| Int) (|sequence_number#Transaction| Int) (|gas_remaining#Transaction| Int) ) ) ))
(declare-sort T@String 0)
(declare-datatypes ((T@Value 0)(T@ValueArray 0)) (((Boolean (|b#Boolean| Bool) ) (Integer (|i#Integer| Int) ) (Address (|a#Address| Int) ) (ByteArray (|b#ByteArray| T@ByteArray) ) (Str (|a#Str| T@String) ) (Vector (|v#Vector| T@ValueArray) ) ) ((ValueArray (|v#ValueArray| (Array Int T@Value)) (|l#ValueArray| Int) ) ) ))
(declare-sort T@TypeName 0)
(declare-datatypes ((T@TypeValue 0)(T@TypeValueArray 0)) (((BooleanType ) (IntegerType ) (AddressType ) (ByteArrayType ) (StrType ) (VectorType (|t#VectorType| T@TypeValue) ) (StructType (|name#StructType| T@TypeName) (|ts#StructType| T@TypeValueArray) ) ) ((TypeValueArray (|v#TypeValueArray| (Array Int T@TypeValue)) (|l#TypeValueArray| Int) ) ) ))
(declare-datatypes ((T@Location 0)) (((Global (|t#Global| T@TypeValue) (|a#Global| Int) ) (Local (|i#Local| Int) ) ) ))
(declare-datatypes ((T@Memory 0)) (((Memory (|domain#Memory| (Array T@Location Bool)) (|contents#Memory| (Array T@Location T@Value)) ) ) ))
(declare-datatypes ((T@Path 0)) (((Path (|p#Path| (Array Int Int)) (|size#Path| Int) ) ) ))
(declare-datatypes ((T@Reference 0)) (((Reference (|l#Reference| T@Location) (|p#Reference| T@Path) ) ) ))
(declare-fun EmptyPath () T@Path)
(declare-fun path_index_at (T@Path Int) Int)
(declare-fun EmptyTypeValueArray () T@TypeValueArray)
(declare-fun DefaultTypeValue () T@TypeValue)
(declare-fun ExtendTypeValueArray (T@TypeValueArray T@TypeValue) T@TypeValueArray)
(declare-fun MAX_U8 () Int)
(declare-fun MAX_U64 () Int)
(declare-fun MAX_U128 () Int)
(declare-fun max_u64 () T@Value)
(declare-fun EmptyValueArray () T@ValueArray)
(declare-fun DefaultValue () T@Value)
(declare-fun AddValueArray (T@ValueArray T@Value) T@ValueArray)
(declare-fun RemoveValueArray (T@ValueArray) T@ValueArray)
(declare-fun ConcatValueArray (T@ValueArray T@ValueArray) T@ValueArray)
(declare-fun |lambda#0| (Int (Array Int T@Value) (Array Int T@Value) Int) (Array Int T@Value))
(declare-fun ReverseValueArray (T@ValueArray) T@ValueArray)
(declare-fun |lambda#1| (Int Int (Array Int T@Value) Int Int T@Value) (Array Int T@Value))
(declare-fun ExtendValueArray (T@ValueArray T@Value) T@ValueArray)
(declare-fun UpdateValueArray (T@ValueArray Int T@Value) T@ValueArray)
(declare-fun SwapValueArray (T@ValueArray Int Int) T@ValueArray)
(declare-fun IsEmpty (T@ValueArray) Bool)
(declare-fun StratificationDepth () Int)
(declare-fun IsEqual4 (T@Value T@Value) Bool)
(declare-fun IsEqual3 (T@Value T@Value) Bool)
(declare-fun vlen (T@Value) Int)
(declare-fun vmap (T@Value) (Array Int T@Value))
(declare-fun IsEqual2 (T@Value T@Value) Bool)
(declare-fun IsEqual1 (T@Value T@Value) Bool)
(declare-fun IsEqual (T@Value T@Value) Bool)
(declare-fun ReadValue4 (T@Path T@Value) T@Value)
(declare-fun ReadValue3 (T@Path T@Value) T@Value)
(declare-fun ReadValue2 (T@Path T@Value) T@Value)
(declare-fun ReadValue1 (T@Path T@Value) T@Value)
(declare-fun ReadValue0 (T@Path T@Value) T@Value)
(declare-fun ReadValue (T@Path T@Value) T@Value)
(declare-fun UpdateValue4 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue3 (T@Path T@Value T@Value) T@Value)
(declare-fun update_vector (T@Value Int T@Value) T@Value)
(declare-fun UpdateValue2 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue1 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue0 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue (T@Path T@Value T@Value) T@Value)
(declare-fun mk_vector () T@Value)
(declare-fun push_back_vector (T@Value T@Value) T@Value)
(declare-fun pop_back_vector (T@Value) T@Value)
(declare-fun append_vector (T@Value T@Value) T@Value)
(declare-fun reverse_vector (T@Value) T@Value)
(declare-fun swap_vector (T@Value Int Int) T@Value)
(declare-fun EmptyMemory () T@Memory)
(declare-fun GetLocal (T@Memory Int) T@Value)
(declare-fun UpdateLocal (T@Memory Int T@Value) T@Memory)
(declare-fun ExistsResourceRaw (T@Memory T@TypeValue Int) Bool)
(declare-fun ExistsResource (T@Memory T@TypeValue Int) T@Value)
(declare-fun GetResourceReference (T@TypeValue Int) T@Reference)
(declare-fun GetLocalReference (Int Int) T@Reference)
(declare-fun SelectFieldFromRef (T@Reference Int) T@Reference)
(declare-fun SelectField (T@Value Int) T@Value)
(declare-fun Dereference (T@Memory T@Reference) T@Value)
(declare-fun ExistsTxnSenderAccount (T@Memory T@Transaction) Bool)
(declare-fun LibraAccount_T_type_value () T@TypeValue)
(declare-fun TxnSenderAddress (T@Transaction) Int)
(assert (= (|size#Path| EmptyPath) 0))
(assert (forall ((p T@Path) (i Int) ) (! (= (path_index_at p i) (select (|p#Path| p) i))
 :qid |testfunc.18:36|
 :skolemid |0|
 :pattern ( (path_index_at p i))
)))
(assert (= (|l#TypeValueArray| EmptyTypeValueArray) 0))
(assert (= (|v#TypeValueArray| EmptyTypeValueArray) ((as const (Array Int T@TypeValue)) DefaultTypeValue)))
(assert (forall ((ta T@TypeValueArray) (tv T@TypeValue) ) (! (= (ExtendTypeValueArray ta tv) (TypeValueArray (store (|v#TypeValueArray| ta) (|l#TypeValueArray| ta) tv) (+ (|l#TypeValueArray| ta) 1)))
 :qid |testfunc.45:43|
 :skolemid |1|
 :pattern ( (ExtendTypeValueArray ta tv))
)))
(assert (= MAX_U8 255))
(assert (= MAX_U64 9223372036854775807))
(assert (= MAX_U128 340282366920938463463374607431768211456))
(assert (= max_u64 (Integer 9223372036854775807)))
(assert (= (|l#ValueArray| EmptyValueArray) 0))
(assert (= (|v#ValueArray| EmptyValueArray) ((as const (Array Int T@Value)) DefaultValue)))
(assert (forall ((a T@ValueArray) (v T@Value) ) (! (= (AddValueArray a v) (ValueArray (store (|v#ValueArray| a) (|l#ValueArray| a) v) (+ (|l#ValueArray| a) 1)))
 :qid |testfunc.104:36|
 :skolemid |2|
 :pattern ( (AddValueArray a v))
)))
(assert (forall ((a@@0 T@ValueArray) ) (! (= (RemoveValueArray a@@0) (ValueArray (store (|v#ValueArray| a@@0) (|l#ValueArray| a@@0) DefaultValue) (- (|l#ValueArray| a@@0) 1)))
 :qid |testfunc.108:39|
 :skolemid |3|
 :pattern ( (RemoveValueArray a@@0))
)))
(assert (forall ((a1 T@ValueArray) (a2 T@ValueArray) ) (! (= (ConcatValueArray a1 a2) (ValueArray (|lambda#0| (|l#ValueArray| a1) (|v#ValueArray| a1) (|v#ValueArray| a2) (|l#ValueArray| a1)) (+ (|l#ValueArray| a1) (|l#ValueArray| a2))))
 :qid |testfunc.111:39|
 :skolemid |4|
 :pattern ( (ConcatValueArray a1 a2))
)))
(assert (forall ((a@@1 T@ValueArray) ) (! (= (ReverseValueArray a@@1) (ValueArray (|lambda#1| 0 (|l#ValueArray| a@@1) (|v#ValueArray| a@@1) (|l#ValueArray| a@@1) 1 DefaultValue) (|l#ValueArray| a@@1)))
 :qid |testfunc.116:40|
 :skolemid |5|
 :pattern ( (ReverseValueArray a@@1))
)))
(assert (forall ((a@@2 T@ValueArray) (elem T@Value) ) (! (= (ExtendValueArray a@@2 elem) (ValueArray (store (|v#ValueArray| a@@2) (|l#ValueArray| a@@2) elem) (+ (|l#ValueArray| a@@2) 1)))
 :qid |testfunc.122:39|
 :skolemid |6|
 :pattern ( (ExtendValueArray a@@2 elem))
)))
(assert (forall ((a@@3 T@ValueArray) (i@@0 Int) (elem@@0 T@Value) ) (! (= (UpdateValueArray a@@3 i@@0 elem@@0) (ValueArray (store (|v#ValueArray| a@@3) i@@0 elem@@0) (|l#ValueArray| a@@3)))
 :qid |testfunc.125:39|
 :skolemid |7|
 :pattern ( (UpdateValueArray a@@3 i@@0 elem@@0))
)))
(assert (forall ((a@@4 T@ValueArray) (i@@1 Int) (j Int) ) (! (= (SwapValueArray a@@4 i@@1 j) (ValueArray (store (store (|v#ValueArray| a@@4) i@@1 (select (|v#ValueArray| a@@4) j)) j (select (|v#ValueArray| a@@4) i@@1)) (|l#ValueArray| a@@4)))
 :qid |testfunc.128:37|
 :skolemid |8|
 :pattern ( (SwapValueArray a@@4 i@@1 j))
)))
(assert (forall ((a@@5 T@ValueArray) ) (!  (and (=> (IsEmpty a@@5) (= (|l#ValueArray| a@@5) 0)) (=> (= (|l#ValueArray| a@@5) 0) (IsEmpty a@@5)))
 :qid |testfunc.131:30|
 :skolemid |9|
 :pattern ( (IsEmpty a@@5))
)))
(assert (= StratificationDepth 4))
(assert (forall ((v1 T@Value) (v2 T@Value) ) (!  (and (=> (IsEqual4 v1 v2) (= v1 v2)) (=> (= v1 v2) (IsEqual4 v1 v2)))
 :qid |testfunc.146:31|
 :skolemid |10|
 :pattern ( (IsEqual4 v1 v2))
)))
(assert (forall ((v1@@0 T@Value) (v2@@0 T@Value) ) (!  (and (=> (IsEqual3 v1@@0 v2@@0) (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@2) (select (vmap v2@@0) i@@2)))
 :qid |testfunc.154:14|
 :skolemid |11|
))))) (=> (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@3 Int) ) (!  (=> (and (<= 0 i@@3) (< i@@3 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@3) (select (vmap v2@@0) i@@3)))
 :qid |testfunc.154:14|
 :skolemid |11|
)))) (IsEqual3 v1@@0 v2@@0)))
 :qid |testfunc.149:31|
 :skolemid |12|
 :pattern ( (IsEqual3 v1@@0 v2@@0))
)))
(assert (forall ((v1@@1 T@Value) (v2@@1 T@Value) ) (!  (and (=> (IsEqual2 v1@@1 v2@@1) (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@4 Int) ) (!  (=> (and (<= 0 i@@4) (< i@@4 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@4) (select (vmap v2@@1) i@@4)))
 :qid |testfunc.161:14|
 :skolemid |13|
))))) (=> (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@5 Int) ) (!  (=> (and (<= 0 i@@5) (< i@@5 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@5) (select (vmap v2@@1) i@@5)))
 :qid |testfunc.161:14|
 :skolemid |13|
)))) (IsEqual2 v1@@1 v2@@1)))
 :qid |testfunc.156:31|
 :skolemid |14|
 :pattern ( (IsEqual2 v1@@1 v2@@1))
)))
(assert (forall ((v1@@2 T@Value) (v2@@2 T@Value) ) (!  (and (=> (IsEqual1 v1@@2 v2@@2) (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@6 Int) ) (!  (=> (and (<= 0 i@@6) (< i@@6 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@6) (select (vmap v2@@2) i@@6)))
 :qid |testfunc.168:14|
 :skolemid |15|
))))) (=> (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@7 Int) ) (!  (=> (and (<= 0 i@@7) (< i@@7 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@7) (select (vmap v2@@2) i@@7)))
 :qid |testfunc.168:14|
 :skolemid |15|
)))) (IsEqual1 v1@@2 v2@@2)))
 :qid |testfunc.163:31|
 :skolemid |16|
 :pattern ( (IsEqual1 v1@@2 v2@@2))
)))
(assert (forall ((v1@@3 T@Value) (v2@@3 T@Value) ) (!  (and (=> (IsEqual v1@@3 v2@@3) (IsEqual1 v1@@3 v2@@3)) (=> (IsEqual1 v1@@3 v2@@3) (IsEqual v1@@3 v2@@3)))
 :qid |testfunc.170:30|
 :skolemid |17|
 :pattern ( (IsEqual v1@@3 v2@@3))
)))
(assert (forall ((p@@0 T@Path) (v@@0 T@Value) ) (! (= (ReadValue4 p@@0 v@@0) v@@0)
 :qid |testfunc.174:33|
 :skolemid |18|
 :pattern ( (ReadValue4 p@@0 v@@0))
)))
(assert (forall ((p@@1 T@Path) (v@@1 T@Value) ) (! (= (ReadValue3 p@@1 v@@1) (ite (= 3 (|size#Path| p@@1)) v@@1 (ReadValue4 p@@1 (select (vmap v@@1) (path_index_at p@@1 3)))))
 :qid |testfunc.177:33|
 :skolemid |19|
 :pattern ( (ReadValue3 p@@1 v@@1))
)))
(assert (forall ((p@@2 T@Path) (v@@2 T@Value) ) (! (= (ReadValue2 p@@2 v@@2) (ite (= 2 (|size#Path| p@@2)) v@@2 (ReadValue3 p@@2 (select (vmap v@@2) (path_index_at p@@2 2)))))
 :qid |testfunc.183:33|
 :skolemid |20|
 :pattern ( (ReadValue2 p@@2 v@@2))
)))
(assert (forall ((p@@3 T@Path) (v@@3 T@Value) ) (! (= (ReadValue1 p@@3 v@@3) (ite (= 1 (|size#Path| p@@3)) v@@3 (ReadValue2 p@@3 (select (vmap v@@3) (path_index_at p@@3 1)))))
 :qid |testfunc.189:33|
 :skolemid |21|
 :pattern ( (ReadValue1 p@@3 v@@3))
)))
(assert (forall ((p@@4 T@Path) (v@@4 T@Value) ) (! (= (ReadValue0 p@@4 v@@4) (ite (= 0 (|size#Path| p@@4)) v@@4 (ReadValue1 p@@4 (select (vmap v@@4) (path_index_at p@@4 0)))))
 :qid |testfunc.195:33|
 :skolemid |22|
 :pattern ( (ReadValue0 p@@4 v@@4))
)))
(assert (forall ((p@@5 T@Path) (v@@5 T@Value) ) (! (= (ReadValue p@@5 v@@5) (ReadValue0 p@@5 v@@5))
 :qid |testfunc.201:32|
 :skolemid |23|
 :pattern ( (ReadValue p@@5 v@@5))
)))
(assert (forall ((p@@6 T@Path) (v@@6 T@Value) (new_v T@Value) ) (! (= (UpdateValue4 p@@6 v@@6 new_v) new_v)
 :qid |testfunc.205:35|
 :skolemid |24|
 :pattern ( (UpdateValue4 p@@6 v@@6 new_v))
)))
(assert (forall ((p@@7 T@Path) (v@@7 T@Value) (new_v@@0 T@Value) ) (! (= (UpdateValue3 p@@7 v@@7 new_v@@0) (ite (= 3 (|size#Path| p@@7)) new_v@@0 (update_vector v@@7 (path_index_at p@@7 3) (UpdateValue4 p@@7 (select (vmap v@@7) (path_index_at p@@7 3)) new_v@@0))))
 :qid |testfunc.208:35|
 :skolemid |25|
 :pattern ( (UpdateValue3 p@@7 v@@7 new_v@@0))
)))
(assert (forall ((p@@8 T@Path) (v@@8 T@Value) (new_v@@1 T@Value) ) (! (= (UpdateValue2 p@@8 v@@8 new_v@@1) (ite (= 2 (|size#Path| p@@8)) new_v@@1 (update_vector v@@8 (path_index_at p@@8 2) (UpdateValue3 p@@8 (select (vmap v@@8) (path_index_at p@@8 2)) new_v@@1))))
 :qid |testfunc.214:35|
 :skolemid |26|
 :pattern ( (UpdateValue2 p@@8 v@@8 new_v@@1))
)))
(assert (forall ((p@@9 T@Path) (v@@9 T@Value) (new_v@@2 T@Value) ) (! (= (UpdateValue1 p@@9 v@@9 new_v@@2) (ite (= 1 (|size#Path| p@@9)) new_v@@2 (update_vector v@@9 (path_index_at p@@9 1) (UpdateValue2 p@@9 (select (vmap v@@9) (path_index_at p@@9 1)) new_v@@2))))
 :qid |testfunc.220:35|
 :skolemid |27|
 :pattern ( (UpdateValue1 p@@9 v@@9 new_v@@2))
)))
(assert (forall ((p@@10 T@Path) (v@@10 T@Value) (new_v@@3 T@Value) ) (! (= (UpdateValue0 p@@10 v@@10 new_v@@3) (ite (= 0 (|size#Path| p@@10)) new_v@@3 (update_vector v@@10 (path_index_at p@@10 0) (UpdateValue1 p@@10 (select (vmap v@@10) (path_index_at p@@10 0)) new_v@@3))))
 :qid |testfunc.226:35|
 :skolemid |28|
 :pattern ( (UpdateValue0 p@@10 v@@10 new_v@@3))
)))
(assert (forall ((p@@11 T@Path) (v@@11 T@Value) (new_v@@4 T@Value) ) (! (= (UpdateValue p@@11 v@@11 new_v@@4) (UpdateValue0 p@@11 v@@11 new_v@@4))
 :qid |testfunc.232:34|
 :skolemid |29|
 :pattern ( (UpdateValue p@@11 v@@11 new_v@@4))
)))
(assert (forall ((v@@12 T@Value) ) (! (= (vmap v@@12) (|v#ValueArray| (|v#Vector| v@@12)))
 :qid |testfunc.239:27|
 :skolemid |30|
 :pattern ( (vmap v@@12))
)))
(assert (forall ((v@@13 T@Value) ) (! (= (vlen v@@13) (|l#ValueArray| (|v#Vector| v@@13)))
 :qid |testfunc.242:27|
 :skolemid |31|
 :pattern ( (vlen v@@13))
)))
(assert (= mk_vector (Vector EmptyValueArray)))
(assert (forall ((v@@14 T@Value) (elem@@1 T@Value) ) (! (= (push_back_vector v@@14 elem@@1) (Vector (AddValueArray (|v#Vector| v@@14) elem@@1)))
 :qid |testfunc.248:39|
 :skolemid |32|
 :pattern ( (push_back_vector v@@14 elem@@1))
)))
(assert (forall ((v@@15 T@Value) ) (! (= (pop_back_vector v@@15) (Vector (RemoveValueArray (|v#Vector| v@@15))))
 :qid |testfunc.251:38|
 :skolemid |33|
 :pattern ( (pop_back_vector v@@15))
)))
(assert (forall ((v1@@4 T@Value) (v2@@4 T@Value) ) (! (= (append_vector v1@@4 v2@@4) (Vector (ConcatValueArray (|v#Vector| v1@@4) (|v#Vector| v2@@4))))
 :qid |testfunc.254:36|
 :skolemid |34|
 :pattern ( (append_vector v1@@4 v2@@4))
)))
(assert (forall ((v@@16 T@Value) ) (! (= (reverse_vector v@@16) (Vector (ReverseValueArray (|v#Vector| v@@16))))
 :qid |testfunc.257:37|
 :skolemid |35|
 :pattern ( (reverse_vector v@@16))
)))
(assert (forall ((v@@17 T@Value) (i@@8 Int) (elem@@2 T@Value) ) (! (= (update_vector v@@17 i@@8 elem@@2) (Vector (UpdateValueArray (|v#Vector| v@@17) i@@8 elem@@2)))
 :qid |testfunc.260:36|
 :skolemid |36|
 :pattern ( (update_vector v@@17 i@@8 elem@@2))
)))
(assert (forall ((v@@18 T@Value) (i@@9 Int) (j@@0 Int) ) (! (= (swap_vector v@@18 i@@9 j@@0) (Vector (SwapValueArray (|v#Vector| v@@18) i@@9 j@@0)))
 :qid |testfunc.263:34|
 :skolemid |37|
 :pattern ( (swap_vector v@@18 i@@9 j@@0))
)))
(assert (= (|domain#Memory| EmptyMemory) ((as const (Array T@Location Bool)) false)))
(assert (= (|contents#Memory| EmptyMemory) ((as const (Array T@Location T@Value)) DefaultValue)))
(assert (forall ((m T@Memory) (idx Int) ) (! (= (GetLocal m idx) (select (|contents#Memory| m) (Local idx)))
 :qid |testfunc.316:31|
 :skolemid |38|
 :pattern ( (GetLocal m idx))
)))
(assert (forall ((m@@0 T@Memory) (idx@@0 Int) (v@@19 T@Value) ) (! (= (UpdateLocal m@@0 idx@@0 v@@19) (Memory (store (|domain#Memory| m@@0) (Local idx@@0) true) (store (|contents#Memory| m@@0) (Local idx@@0) v@@19)))
 :qid |testfunc.320:34|
 :skolemid |39|
 :pattern ( (UpdateLocal m@@0 idx@@0 v@@19))
)))
(assert (forall ((m@@1 T@Memory) (resource T@TypeValue) (addr Int) ) (!  (and (=> (ExistsResourceRaw m@@1 resource addr) (select (|domain#Memory| m@@1) (Global resource addr))) (=> (select (|domain#Memory| m@@1) (Global resource addr)) (ExistsResourceRaw m@@1 resource addr)))
 :qid |testfunc.335:40|
 :skolemid |40|
 :pattern ( (ExistsResourceRaw m@@1 resource addr))
)))
(assert (forall ((m@@2 T@Memory) (resource@@0 T@TypeValue) (addr@@0 Int) ) (! (= (ExistsResource m@@2 resource@@0 addr@@0) (Boolean (ExistsResourceRaw m@@2 resource@@0 addr@@0)))
 :qid |testfunc.338:37|
 :skolemid |41|
 :pattern ( (ExistsResource m@@2 resource@@0 addr@@0))
)))
(assert (forall ((resource@@1 T@TypeValue) (addr@@1 Int) ) (! (= (GetResourceReference resource@@1 addr@@1) (Reference (Global resource@@1 addr@@1) EmptyPath))
 :qid |testfunc.343:43|
 :skolemid |42|
 :pattern ( (GetResourceReference resource@@1 addr@@1))
)))
(assert (forall ((frame_idx Int) (idx@@1 Int) ) (! (= (GetLocalReference frame_idx idx@@1) (Reference (Local (+ frame_idx idx@@1)) EmptyPath))
 :qid |testfunc.348:40|
 :skolemid |43|
 :pattern ( (GetLocalReference frame_idx idx@@1))
)))
(assert (forall ((ref T@Reference) (field Int) ) (! (= (SelectFieldFromRef ref field) (Reference (|l#Reference| ref) (Path (store (|p#Path| (|p#Reference| ref)) (|size#Path| (|p#Reference| ref)) field) (+ (|size#Path| (|p#Reference| ref)) 1))))
 :qid |testfunc.353:41|
 :skolemid |44|
 :pattern ( (SelectFieldFromRef ref field))
)))
(assert (forall ((val T@Value) (field@@0 Int) ) (! (= (SelectField val field@@0) (select (vmap val) field@@0))
 :qid |testfunc.361:34|
 :skolemid |45|
 :pattern ( (SelectField val field@@0))
)))
(assert (forall ((m@@3 T@Memory) (ref@@0 T@Reference) ) (! (= (Dereference m@@3 ref@@0) (ReadValue (|p#Reference| ref@@0) (select (|contents#Memory| m@@3) (|l#Reference| ref@@0))))
 :qid |testfunc.366:34|
 :skolemid |46|
 :pattern ( (Dereference m@@3 ref@@0))
)))
(assert (forall ((m@@4 T@Memory) (txn T@Transaction) ) (!  (and (=> (ExistsTxnSenderAccount m@@4 txn) (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn)))) (=> (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn))) (ExistsTxnSenderAccount m@@4 txn)))
 :qid |testfunc.371:45|
 :skolemid |47|
 :pattern ( (ExistsTxnSenderAccount m@@4 txn))
)))
(assert (forall ((txn@@0 T@Transaction) ) (! (= (TxnSenderAddress txn@@0) (|sender#Transaction| txn@@0))
 :qid |testfunc.380:39|
 :skolemid |48|
 :pattern ( (TxnSenderAddress txn@@0))
)))
(assert (forall ((i@@10 Int) (|l#0| Int) (|l#1| (Array Int T@Value)) (|l#2| (Array Int T@Value)) (|l#3| Int) ) (! (= (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10) (ite (< i@@10 |l#0|) (select |l#1| i@@10) (select |l#2| (- i@@10 |l#3|))))
 :qid |testfunc.113:17|
 :skolemid |49|
 :pattern ( (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10))
)))
(assert (forall ((i@@11 Int) (|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| (Array Int T@Value)) (|l#3@@0| Int) (|l#4| Int) (|l#5| T@Value) ) (! (= (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11) (ite  (and (<= |l#0@@0| i@@11) (< i@@11 |l#1@@0|)) (select |l#2@@0| (- (- |l#3@@0| i@@11) |l#4|)) |l#5|))
 :qid |testfunc.118:17|
 :skolemid |50|
 :pattern ( (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11))
)))
; Valid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%+1 () Bool)
(declare-fun %lbl%+2 () Bool)
(declare-fun inline$AddU64$0$src1@0 () T@Value)
(declare-fun inline$AddU64$0$src2@0 () T@Value)
(declare-fun inline$AddU64$0$dst@1 () T@Value)
(declare-fun abort_flag@0 () Bool)
(declare-fun abort_flag () Bool)
(declare-fun %lbl%+3 () Bool)
(declare-fun %lbl%+4 () Bool)
(declare-fun %lbl%+5 () Bool)
(declare-fun m@2 () T@Memory)
(declare-fun local_counter () Int)
(declare-fun %lbl%+6 () Bool)
(declare-fun m@1 () T@Memory)
(declare-fun inline$LdConst$0$ret@1 () T@Value)
(declare-fun %lbl%+7 () Bool)
(declare-fun %lbl%+8 () Bool)
(declare-fun m@0 () T@Memory)
(declare-fun inline$CopyOrMoveValue$0$local@0 () T@Value)
(declare-fun %lbl%+9 () Bool)
(declare-fun %lbl%+10 () Bool)
(declare-fun x () T@Value)
(declare-fun local_counter@0 () Int)
(declare-fun m@@5 () T@Memory)
(declare-fun %lbl%+11 () Bool)
(declare-fun %lbl%@12 () Bool)
(declare-fun txn@@1 () T@Transaction)
(declare-fun %lbl%+13 () Bool)
(declare-fun %lbl%+14 () Bool)
(push 1)
(set-info :boogie-vc-id TestFuncCall_g_verify)
(assert (not
(let ((inline$TestFuncCall_g$0$anon3_Else_correct  (=> (! (and %lbl%+0 true) :lblpos +0) true)))
(let ((inline$TestFuncCall_g$0$anon3_Then_correct  (=> (! (and %lbl%+1 true) :lblpos +1) true)))
(let ((inline$AddU64$0$anon3_Else_correct  (=> (! (and %lbl%+2 true) :lblpos +2) (=> (and (and (>= MAX_U64 (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0))) (= inline$AddU64$0$dst@1 (Integer (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0))))) (and (=> abort_flag@0 abort_flag) (=> abort_flag abort_flag@0))) (and inline$TestFuncCall_g$0$anon3_Then_correct inline$TestFuncCall_g$0$anon3_Else_correct)))))
(let ((inline$AddU64$0$anon3_Then_correct  (=> (! (and %lbl%+3 true) :lblpos +3) (=> (> (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0)) MAX_U64) (=> (and (=> abort_flag@0 true) (=> true abort_flag@0)) (and inline$TestFuncCall_g$0$anon3_Then_correct inline$TestFuncCall_g$0$anon3_Else_correct))))))
(let ((inline$AddU64$0$anon0_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (=> (and (and (and (is-Integer inline$AddU64$0$src1@0) (>= (|i#Integer| inline$AddU64$0$src1@0) 0)) (<= (|i#Integer| inline$AddU64$0$src1@0) MAX_U64)) (and (and (is-Integer inline$AddU64$0$src2@0) (>= (|i#Integer| inline$AddU64$0$src2@0) 0)) (<= (|i#Integer| inline$AddU64$0$src2@0) MAX_U64))) (and inline$AddU64$0$anon3_Then_correct inline$AddU64$0$anon3_Else_correct)))))
(let ((inline$AddU64$0$Entry_correct  (=> (! (and %lbl%+5 true) :lblpos +5) (=> (and (= inline$AddU64$0$src1@0 (GetLocal m@2 (+ local_counter 1))) (= inline$AddU64$0$src2@0 (GetLocal m@2 (+ local_counter 2)))) inline$AddU64$0$anon0_correct))))
(let ((inline$TestFuncCall_g$0$anon0$2_correct  (=> (! (and %lbl%+6 true) :lblpos +6) (=> (= m@2 (UpdateLocal m@1 (+ local_counter 2) inline$LdConst$0$ret@1)) inline$AddU64$0$Entry_correct))))
(let ((inline$LdConst$0$anon0_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> (= inline$LdConst$0$ret@1 (Integer 2)) inline$TestFuncCall_g$0$anon0$2_correct))))
(let ((inline$TestFuncCall_g$0$anon0$1_correct  (=> (! (and %lbl%+8 true) :lblpos +8) (=> (= m@1 (UpdateLocal m@0 (+ local_counter 1) inline$CopyOrMoveValue$0$local@0)) inline$LdConst$0$anon0_correct))))
(let ((inline$CopyOrMoveValue$0$Entry_correct  (=> (! (and %lbl%+9 true) :lblpos +9) (=> (= inline$CopyOrMoveValue$0$local@0 (GetLocal m@0 (+ local_counter 0))) inline$TestFuncCall_g$0$anon0$1_correct))))
(let ((inline$TestFuncCall_g$0$anon0_correct  (=> (! (and %lbl%+10 true) :lblpos +10) (=> (not abort_flag) (=> (and (and (and (is-Integer x) (>= (|i#Integer| x) 0)) (<= (|i#Integer| x) MAX_U64)) (and (= local_counter@0 (+ local_counter 4)) (= m@0 (UpdateLocal m@@5 (+ local_counter 0) x)))) inline$CopyOrMoveValue$0$Entry_correct)))))
(let ((inline$TestFuncCall_g$0$Entry_correct  (=> (! (and %lbl%+11 true) :lblpos +11) (and (! (or %lbl%@12 (ExistsTxnSenderAccount m@@5 txn@@1)) :lblneg @12) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestFuncCall_g$0$anon0_correct)))))
(let ((anon0_correct  (=> (! (and %lbl%+13 true) :lblpos +13) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestFuncCall_g$0$Entry_correct))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+14 true) :lblpos +14) anon0_correct)))
PreconditionGeneratedEntry_correct))))))))))))))
))
(check-sat)
(pop 1)
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :AUTO_CONFIG false)
(set-option :pp.bv_literals false)
(set-option :MODEL.V2 true)
(set-option :smt.PHASE_SELECTION 0)
(set-option :smt.RESTART_STRATEGY 0)
(set-option :smt.RESTART_FACTOR |1.5|)
(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
(set-option :smt.CASE_SPLIT 3)
(set-option :smt.DELAY_UNITS true)
(set-option :NNF.SK_HACK true)
(set-option :smt.MBQI false)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :TYPE_CHECK true)
(set-option :smt.BV.REFLECT true)
(set-option :model_compress false)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-sort T@ByteArray 0)
(declare-datatypes ((T@Transaction 0)) (((Transaction (|gas_unit_price#Transaction| Int) (|max_gas_units#Transaction| Int) (|public_key#Transaction| T@ByteArray) (|sender#Transaction| Int) (|sequence_number#Transaction| Int) (|gas_remaining#Transaction| Int) ) ) ))
(declare-sort T@String 0)
(declare-datatypes ((T@Value 0)(T@ValueArray 0)) (((Boolean (|b#Boolean| Bool) ) (Integer (|i#Integer| Int) ) (Address (|a#Address| Int) ) (ByteArray (|b#ByteArray| T@ByteArray) ) (Str (|a#Str| T@String) ) (Vector (|v#Vector| T@ValueArray) ) ) ((ValueArray (|v#ValueArray| (Array Int T@Value)) (|l#ValueArray| Int) ) ) ))
(declare-sort T@TypeName 0)
(declare-datatypes ((T@TypeValue 0)(T@TypeValueArray 0)) (((BooleanType ) (IntegerType ) (AddressType ) (ByteArrayType ) (StrType ) (VectorType (|t#VectorType| T@TypeValue) ) (StructType (|name#StructType| T@TypeName) (|ts#StructType| T@TypeValueArray) ) ) ((TypeValueArray (|v#TypeValueArray| (Array Int T@TypeValue)) (|l#TypeValueArray| Int) ) ) ))
(declare-datatypes ((T@Location 0)) (((Global (|t#Global| T@TypeValue) (|a#Global| Int) ) (Local (|i#Local| Int) ) ) ))
(declare-datatypes ((T@Memory 0)) (((Memory (|domain#Memory| (Array T@Location Bool)) (|contents#Memory| (Array T@Location T@Value)) ) ) ))
(declare-datatypes ((T@Path 0)) (((Path (|p#Path| (Array Int Int)) (|size#Path| Int) ) ) ))
(declare-datatypes ((T@Reference 0)) (((Reference (|l#Reference| T@Location) (|p#Reference| T@Path) ) ) ))
(declare-fun EmptyPath () T@Path)
(declare-fun path_index_at (T@Path Int) Int)
(declare-fun EmptyTypeValueArray () T@TypeValueArray)
(declare-fun DefaultTypeValue () T@TypeValue)
(declare-fun ExtendTypeValueArray (T@TypeValueArray T@TypeValue) T@TypeValueArray)
(declare-fun MAX_U8 () Int)
(declare-fun MAX_U64 () Int)
(declare-fun MAX_U128 () Int)
(declare-fun max_u64 () T@Value)
(declare-fun EmptyValueArray () T@ValueArray)
(declare-fun DefaultValue () T@Value)
(declare-fun AddValueArray (T@ValueArray T@Value) T@ValueArray)
(declare-fun RemoveValueArray (T@ValueArray) T@ValueArray)
(declare-fun ConcatValueArray (T@ValueArray T@ValueArray) T@ValueArray)
(declare-fun |lambda#0| (Int (Array Int T@Value) (Array Int T@Value) Int) (Array Int T@Value))
(declare-fun ReverseValueArray (T@ValueArray) T@ValueArray)
(declare-fun |lambda#1| (Int Int (Array Int T@Value) Int Int T@Value) (Array Int T@Value))
(declare-fun ExtendValueArray (T@ValueArray T@Value) T@ValueArray)
(declare-fun UpdateValueArray (T@ValueArray Int T@Value) T@ValueArray)
(declare-fun SwapValueArray (T@ValueArray Int Int) T@ValueArray)
(declare-fun IsEmpty (T@ValueArray) Bool)
(declare-fun StratificationDepth () Int)
(declare-fun IsEqual4 (T@Value T@Value) Bool)
(declare-fun IsEqual3 (T@Value T@Value) Bool)
(declare-fun vlen (T@Value) Int)
(declare-fun vmap (T@Value) (Array Int T@Value))
(declare-fun IsEqual2 (T@Value T@Value) Bool)
(declare-fun IsEqual1 (T@Value T@Value) Bool)
(declare-fun IsEqual (T@Value T@Value) Bool)
(declare-fun ReadValue4 (T@Path T@Value) T@Value)
(declare-fun ReadValue3 (T@Path T@Value) T@Value)
(declare-fun ReadValue2 (T@Path T@Value) T@Value)
(declare-fun ReadValue1 (T@Path T@Value) T@Value)
(declare-fun ReadValue0 (T@Path T@Value) T@Value)
(declare-fun ReadValue (T@Path T@Value) T@Value)
(declare-fun UpdateValue4 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue3 (T@Path T@Value T@Value) T@Value)
(declare-fun update_vector (T@Value Int T@Value) T@Value)
(declare-fun UpdateValue2 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue1 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue0 (T@Path T@Value T@Value) T@Value)
(declare-fun UpdateValue (T@Path T@Value T@Value) T@Value)
(declare-fun mk_vector () T@Value)
(declare-fun push_back_vector (T@Value T@Value) T@Value)
(declare-fun pop_back_vector (T@Value) T@Value)
(declare-fun append_vector (T@Value T@Value) T@Value)
(declare-fun reverse_vector (T@Value) T@Value)
(declare-fun swap_vector (T@Value Int Int) T@Value)
(declare-fun EmptyMemory () T@Memory)
(declare-fun GetLocal (T@Memory Int) T@Value)
(declare-fun UpdateLocal (T@Memory Int T@Value) T@Memory)
(declare-fun ExistsResourceRaw (T@Memory T@TypeValue Int) Bool)
(declare-fun ExistsResource (T@Memory T@TypeValue Int) T@Value)
(declare-fun GetResourceReference (T@TypeValue Int) T@Reference)
(declare-fun GetLocalReference (Int Int) T@Reference)
(declare-fun SelectFieldFromRef (T@Reference Int) T@Reference)
(declare-fun SelectField (T@Value Int) T@Value)
(declare-fun Dereference (T@Memory T@Reference) T@Value)
(declare-fun ExistsTxnSenderAccount (T@Memory T@Transaction) Bool)
(declare-fun LibraAccount_T_type_value () T@TypeValue)
(declare-fun TxnSenderAddress (T@Transaction) Int)
(assert (= (|size#Path| EmptyPath) 0))
(assert (forall ((p T@Path) (i Int) ) (! (= (path_index_at p i) (select (|p#Path| p) i))
 :qid |testfunc.18:36|
 :skolemid |0|
 :pattern ( (path_index_at p i))
)))
(assert (= (|l#TypeValueArray| EmptyTypeValueArray) 0))
(assert (= (|v#TypeValueArray| EmptyTypeValueArray) ((as const (Array Int T@TypeValue)) DefaultTypeValue)))
(assert (forall ((ta T@TypeValueArray) (tv T@TypeValue) ) (! (= (ExtendTypeValueArray ta tv) (TypeValueArray (store (|v#TypeValueArray| ta) (|l#TypeValueArray| ta) tv) (+ (|l#TypeValueArray| ta) 1)))
 :qid |testfunc.45:43|
 :skolemid |1|
 :pattern ( (ExtendTypeValueArray ta tv))
)))
(assert (= MAX_U8 255))
(assert (= MAX_U64 9223372036854775807))
(assert (= MAX_U128 340282366920938463463374607431768211456))
(assert (= max_u64 (Integer 9223372036854775807)))
(assert (= (|l#ValueArray| EmptyValueArray) 0))
(assert (= (|v#ValueArray| EmptyValueArray) ((as const (Array Int T@Value)) DefaultValue)))
(assert (forall ((a T@ValueArray) (v T@Value) ) (! (= (AddValueArray a v) (ValueArray (store (|v#ValueArray| a) (|l#ValueArray| a) v) (+ (|l#ValueArray| a) 1)))
 :qid |testfunc.104:36|
 :skolemid |2|
 :pattern ( (AddValueArray a v))
)))
(assert (forall ((a@@0 T@ValueArray) ) (! (= (RemoveValueArray a@@0) (ValueArray (store (|v#ValueArray| a@@0) (|l#ValueArray| a@@0) DefaultValue) (- (|l#ValueArray| a@@0) 1)))
 :qid |testfunc.108:39|
 :skolemid |3|
 :pattern ( (RemoveValueArray a@@0))
)))
(assert (forall ((a1 T@ValueArray) (a2 T@ValueArray) ) (! (= (ConcatValueArray a1 a2) (ValueArray (|lambda#0| (|l#ValueArray| a1) (|v#ValueArray| a1) (|v#ValueArray| a2) (|l#ValueArray| a1)) (+ (|l#ValueArray| a1) (|l#ValueArray| a2))))
 :qid |testfunc.111:39|
 :skolemid |4|
 :pattern ( (ConcatValueArray a1 a2))
)))
(assert (forall ((a@@1 T@ValueArray) ) (! (= (ReverseValueArray a@@1) (ValueArray (|lambda#1| 0 (|l#ValueArray| a@@1) (|v#ValueArray| a@@1) (|l#ValueArray| a@@1) 1 DefaultValue) (|l#ValueArray| a@@1)))
 :qid |testfunc.116:40|
 :skolemid |5|
 :pattern ( (ReverseValueArray a@@1))
)))
(assert (forall ((a@@2 T@ValueArray) (elem T@Value) ) (! (= (ExtendValueArray a@@2 elem) (ValueArray (store (|v#ValueArray| a@@2) (|l#ValueArray| a@@2) elem) (+ (|l#ValueArray| a@@2) 1)))
 :qid |testfunc.122:39|
 :skolemid |6|
 :pattern ( (ExtendValueArray a@@2 elem))
)))
(assert (forall ((a@@3 T@ValueArray) (i@@0 Int) (elem@@0 T@Value) ) (! (= (UpdateValueArray a@@3 i@@0 elem@@0) (ValueArray (store (|v#ValueArray| a@@3) i@@0 elem@@0) (|l#ValueArray| a@@3)))
 :qid |testfunc.125:39|
 :skolemid |7|
 :pattern ( (UpdateValueArray a@@3 i@@0 elem@@0))
)))
(assert (forall ((a@@4 T@ValueArray) (i@@1 Int) (j Int) ) (! (= (SwapValueArray a@@4 i@@1 j) (ValueArray (store (store (|v#ValueArray| a@@4) i@@1 (select (|v#ValueArray| a@@4) j)) j (select (|v#ValueArray| a@@4) i@@1)) (|l#ValueArray| a@@4)))
 :qid |testfunc.128:37|
 :skolemid |8|
 :pattern ( (SwapValueArray a@@4 i@@1 j))
)))
(assert (forall ((a@@5 T@ValueArray) ) (!  (and (=> (IsEmpty a@@5) (= (|l#ValueArray| a@@5) 0)) (=> (= (|l#ValueArray| a@@5) 0) (IsEmpty a@@5)))
 :qid |testfunc.131:30|
 :skolemid |9|
 :pattern ( (IsEmpty a@@5))
)))
(assert (= StratificationDepth 4))
(assert (forall ((v1 T@Value) (v2 T@Value) ) (!  (and (=> (IsEqual4 v1 v2) (= v1 v2)) (=> (= v1 v2) (IsEqual4 v1 v2)))
 :qid |testfunc.146:31|
 :skolemid |10|
 :pattern ( (IsEqual4 v1 v2))
)))
(assert (forall ((v1@@0 T@Value) (v2@@0 T@Value) ) (!  (and (=> (IsEqual3 v1@@0 v2@@0) (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@2) (select (vmap v2@@0) i@@2)))
 :qid |testfunc.154:14|
 :skolemid |11|
))))) (=> (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@3 Int) ) (!  (=> (and (<= 0 i@@3) (< i@@3 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@3) (select (vmap v2@@0) i@@3)))
 :qid |testfunc.154:14|
 :skolemid |11|
)))) (IsEqual3 v1@@0 v2@@0)))
 :qid |testfunc.149:31|
 :skolemid |12|
 :pattern ( (IsEqual3 v1@@0 v2@@0))
)))
(assert (forall ((v1@@1 T@Value) (v2@@1 T@Value) ) (!  (and (=> (IsEqual2 v1@@1 v2@@1) (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@4 Int) ) (!  (=> (and (<= 0 i@@4) (< i@@4 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@4) (select (vmap v2@@1) i@@4)))
 :qid |testfunc.161:14|
 :skolemid |13|
))))) (=> (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@5 Int) ) (!  (=> (and (<= 0 i@@5) (< i@@5 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@5) (select (vmap v2@@1) i@@5)))
 :qid |testfunc.161:14|
 :skolemid |13|
)))) (IsEqual2 v1@@1 v2@@1)))
 :qid |testfunc.156:31|
 :skolemid |14|
 :pattern ( (IsEqual2 v1@@1 v2@@1))
)))
(assert (forall ((v1@@2 T@Value) (v2@@2 T@Value) ) (!  (and (=> (IsEqual1 v1@@2 v2@@2) (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@6 Int) ) (!  (=> (and (<= 0 i@@6) (< i@@6 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@6) (select (vmap v2@@2) i@@6)))
 :qid |testfunc.168:14|
 :skolemid |15|
))))) (=> (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@7 Int) ) (!  (=> (and (<= 0 i@@7) (< i@@7 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@7) (select (vmap v2@@2) i@@7)))
 :qid |testfunc.168:14|
 :skolemid |15|
)))) (IsEqual1 v1@@2 v2@@2)))
 :qid |testfunc.163:31|
 :skolemid |16|
 :pattern ( (IsEqual1 v1@@2 v2@@2))
)))
(assert (forall ((v1@@3 T@Value) (v2@@3 T@Value) ) (!  (and (=> (IsEqual v1@@3 v2@@3) (IsEqual1 v1@@3 v2@@3)) (=> (IsEqual1 v1@@3 v2@@3) (IsEqual v1@@3 v2@@3)))
 :qid |testfunc.170:30|
 :skolemid |17|
 :pattern ( (IsEqual v1@@3 v2@@3))
)))
(assert (forall ((p@@0 T@Path) (v@@0 T@Value) ) (! (= (ReadValue4 p@@0 v@@0) v@@0)
 :qid |testfunc.174:33|
 :skolemid |18|
 :pattern ( (ReadValue4 p@@0 v@@0))
)))
(assert (forall ((p@@1 T@Path) (v@@1 T@Value) ) (! (= (ReadValue3 p@@1 v@@1) (ite (= 3 (|size#Path| p@@1)) v@@1 (ReadValue4 p@@1 (select (vmap v@@1) (path_index_at p@@1 3)))))
 :qid |testfunc.177:33|
 :skolemid |19|
 :pattern ( (ReadValue3 p@@1 v@@1))
)))
(assert (forall ((p@@2 T@Path) (v@@2 T@Value) ) (! (= (ReadValue2 p@@2 v@@2) (ite (= 2 (|size#Path| p@@2)) v@@2 (ReadValue3 p@@2 (select (vmap v@@2) (path_index_at p@@2 2)))))
 :qid |testfunc.183:33|
 :skolemid |20|
 :pattern ( (ReadValue2 p@@2 v@@2))
)))
(assert (forall ((p@@3 T@Path) (v@@3 T@Value) ) (! (= (ReadValue1 p@@3 v@@3) (ite (= 1 (|size#Path| p@@3)) v@@3 (ReadValue2 p@@3 (select (vmap v@@3) (path_index_at p@@3 1)))))
 :qid |testfunc.189:33|
 :skolemid |21|
 :pattern ( (ReadValue1 p@@3 v@@3))
)))
(assert (forall ((p@@4 T@Path) (v@@4 T@Value) ) (! (= (ReadValue0 p@@4 v@@4) (ite (= 0 (|size#Path| p@@4)) v@@4 (ReadValue1 p@@4 (select (vmap v@@4) (path_index_at p@@4 0)))))
 :qid |testfunc.195:33|
 :skolemid |22|
 :pattern ( (ReadValue0 p@@4 v@@4))
)))
(assert (forall ((p@@5 T@Path) (v@@5 T@Value) ) (! (= (ReadValue p@@5 v@@5) (ReadValue0 p@@5 v@@5))
 :qid |testfunc.201:32|
 :skolemid |23|
 :pattern ( (ReadValue p@@5 v@@5))
)))
(assert (forall ((p@@6 T@Path) (v@@6 T@Value) (new_v T@Value) ) (! (= (UpdateValue4 p@@6 v@@6 new_v) new_v)
 :qid |testfunc.205:35|
 :skolemid |24|
 :pattern ( (UpdateValue4 p@@6 v@@6 new_v))
)))
(assert (forall ((p@@7 T@Path) (v@@7 T@Value) (new_v@@0 T@Value) ) (! (= (UpdateValue3 p@@7 v@@7 new_v@@0) (ite (= 3 (|size#Path| p@@7)) new_v@@0 (update_vector v@@7 (path_index_at p@@7 3) (UpdateValue4 p@@7 (select (vmap v@@7) (path_index_at p@@7 3)) new_v@@0))))
 :qid |testfunc.208:35|
 :skolemid |25|
 :pattern ( (UpdateValue3 p@@7 v@@7 new_v@@0))
)))
(assert (forall ((p@@8 T@Path) (v@@8 T@Value) (new_v@@1 T@Value) ) (! (= (UpdateValue2 p@@8 v@@8 new_v@@1) (ite (= 2 (|size#Path| p@@8)) new_v@@1 (update_vector v@@8 (path_index_at p@@8 2) (UpdateValue3 p@@8 (select (vmap v@@8) (path_index_at p@@8 2)) new_v@@1))))
 :qid |testfunc.214:35|
 :skolemid |26|
 :pattern ( (UpdateValue2 p@@8 v@@8 new_v@@1))
)))
(assert (forall ((p@@9 T@Path) (v@@9 T@Value) (new_v@@2 T@Value) ) (! (= (UpdateValue1 p@@9 v@@9 new_v@@2) (ite (= 1 (|size#Path| p@@9)) new_v@@2 (update_vector v@@9 (path_index_at p@@9 1) (UpdateValue2 p@@9 (select (vmap v@@9) (path_index_at p@@9 1)) new_v@@2))))
 :qid |testfunc.220:35|
 :skolemid |27|
 :pattern ( (UpdateValue1 p@@9 v@@9 new_v@@2))
)))
(assert (forall ((p@@10 T@Path) (v@@10 T@Value) (new_v@@3 T@Value) ) (! (= (UpdateValue0 p@@10 v@@10 new_v@@3) (ite (= 0 (|size#Path| p@@10)) new_v@@3 (update_vector v@@10 (path_index_at p@@10 0) (UpdateValue1 p@@10 (select (vmap v@@10) (path_index_at p@@10 0)) new_v@@3))))
 :qid |testfunc.226:35|
 :skolemid |28|
 :pattern ( (UpdateValue0 p@@10 v@@10 new_v@@3))
)))
(assert (forall ((p@@11 T@Path) (v@@11 T@Value) (new_v@@4 T@Value) ) (! (= (UpdateValue p@@11 v@@11 new_v@@4) (UpdateValue0 p@@11 v@@11 new_v@@4))
 :qid |testfunc.232:34|
 :skolemid |29|
 :pattern ( (UpdateValue p@@11 v@@11 new_v@@4))
)))
(assert (forall ((v@@12 T@Value) ) (! (= (vmap v@@12) (|v#ValueArray| (|v#Vector| v@@12)))
 :qid |testfunc.239:27|
 :skolemid |30|
 :pattern ( (vmap v@@12))
)))
(assert (forall ((v@@13 T@Value) ) (! (= (vlen v@@13) (|l#ValueArray| (|v#Vector| v@@13)))
 :qid |testfunc.242:27|
 :skolemid |31|
 :pattern ( (vlen v@@13))
)))
(assert (= mk_vector (Vector EmptyValueArray)))
(assert (forall ((v@@14 T@Value) (elem@@1 T@Value) ) (! (= (push_back_vector v@@14 elem@@1) (Vector (AddValueArray (|v#Vector| v@@14) elem@@1)))
 :qid |testfunc.248:39|
 :skolemid |32|
 :pattern ( (push_back_vector v@@14 elem@@1))
)))
(assert (forall ((v@@15 T@Value) ) (! (= (pop_back_vector v@@15) (Vector (RemoveValueArray (|v#Vector| v@@15))))
 :qid |testfunc.251:38|
 :skolemid |33|
 :pattern ( (pop_back_vector v@@15))
)))
(assert (forall ((v1@@4 T@Value) (v2@@4 T@Value) ) (! (= (append_vector v1@@4 v2@@4) (Vector (ConcatValueArray (|v#Vector| v1@@4) (|v#Vector| v2@@4))))
 :qid |testfunc.254:36|
 :skolemid |34|
 :pattern ( (append_vector v1@@4 v2@@4))
)))
(assert (forall ((v@@16 T@Value) ) (! (= (reverse_vector v@@16) (Vector (ReverseValueArray (|v#Vector| v@@16))))
 :qid |testfunc.257:37|
 :skolemid |35|
 :pattern ( (reverse_vector v@@16))
)))
(assert (forall ((v@@17 T@Value) (i@@8 Int) (elem@@2 T@Value) ) (! (= (update_vector v@@17 i@@8 elem@@2) (Vector (UpdateValueArray (|v#Vector| v@@17) i@@8 elem@@2)))
 :qid |testfunc.260:36|
 :skolemid |36|
 :pattern ( (update_vector v@@17 i@@8 elem@@2))
)))
(assert (forall ((v@@18 T@Value) (i@@9 Int) (j@@0 Int) ) (! (= (swap_vector v@@18 i@@9 j@@0) (Vector (SwapValueArray (|v#Vector| v@@18) i@@9 j@@0)))
 :qid |testfunc.263:34|
 :skolemid |37|
 :pattern ( (swap_vector v@@18 i@@9 j@@0))
)))
(assert (= (|domain#Memory| EmptyMemory) ((as const (Array T@Location Bool)) false)))
(assert (= (|contents#Memory| EmptyMemory) ((as const (Array T@Location T@Value)) DefaultValue)))
(assert (forall ((m T@Memory) (idx Int) ) (! (= (GetLocal m idx) (select (|contents#Memory| m) (Local idx)))
 :qid |testfunc.316:31|
 :skolemid |38|
 :pattern ( (GetLocal m idx))
)))
(assert (forall ((m@@0 T@Memory) (idx@@0 Int) (v@@19 T@Value) ) (! (= (UpdateLocal m@@0 idx@@0 v@@19) (Memory (store (|domain#Memory| m@@0) (Local idx@@0) true) (store (|contents#Memory| m@@0) (Local idx@@0) v@@19)))
 :qid |testfunc.320:34|
 :skolemid |39|
 :pattern ( (UpdateLocal m@@0 idx@@0 v@@19))
)))
(assert (forall ((m@@1 T@Memory) (resource T@TypeValue) (addr Int) ) (!  (and (=> (ExistsResourceRaw m@@1 resource addr) (select (|domain#Memory| m@@1) (Global resource addr))) (=> (select (|domain#Memory| m@@1) (Global resource addr)) (ExistsResourceRaw m@@1 resource addr)))
 :qid |testfunc.335:40|
 :skolemid |40|
 :pattern ( (ExistsResourceRaw m@@1 resource addr))
)))
(assert (forall ((m@@2 T@Memory) (resource@@0 T@TypeValue) (addr@@0 Int) ) (! (= (ExistsResource m@@2 resource@@0 addr@@0) (Boolean (ExistsResourceRaw m@@2 resource@@0 addr@@0)))
 :qid |testfunc.338:37|
 :skolemid |41|
 :pattern ( (ExistsResource m@@2 resource@@0 addr@@0))
)))
(assert (forall ((resource@@1 T@TypeValue) (addr@@1 Int) ) (! (= (GetResourceReference resource@@1 addr@@1) (Reference (Global resource@@1 addr@@1) EmptyPath))
 :qid |testfunc.343:43|
 :skolemid |42|
 :pattern ( (GetResourceReference resource@@1 addr@@1))
)))
(assert (forall ((frame_idx Int) (idx@@1 Int) ) (! (= (GetLocalReference frame_idx idx@@1) (Reference (Local (+ frame_idx idx@@1)) EmptyPath))
 :qid |testfunc.348:40|
 :skolemid |43|
 :pattern ( (GetLocalReference frame_idx idx@@1))
)))
(assert (forall ((ref T@Reference) (field Int) ) (! (= (SelectFieldFromRef ref field) (Reference (|l#Reference| ref) (Path (store (|p#Path| (|p#Reference| ref)) (|size#Path| (|p#Reference| ref)) field) (+ (|size#Path| (|p#Reference| ref)) 1))))
 :qid |testfunc.353:41|
 :skolemid |44|
 :pattern ( (SelectFieldFromRef ref field))
)))
(assert (forall ((val T@Value) (field@@0 Int) ) (! (= (SelectField val field@@0) (select (vmap val) field@@0))
 :qid |testfunc.361:34|
 :skolemid |45|
 :pattern ( (SelectField val field@@0))
)))
(assert (forall ((m@@3 T@Memory) (ref@@0 T@Reference) ) (! (= (Dereference m@@3 ref@@0) (ReadValue (|p#Reference| ref@@0) (select (|contents#Memory| m@@3) (|l#Reference| ref@@0))))
 :qid |testfunc.366:34|
 :skolemid |46|
 :pattern ( (Dereference m@@3 ref@@0))
)))
(assert (forall ((m@@4 T@Memory) (txn T@Transaction) ) (!  (and (=> (ExistsTxnSenderAccount m@@4 txn) (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn)))) (=> (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn))) (ExistsTxnSenderAccount m@@4 txn)))
 :qid |testfunc.371:45|
 :skolemid |47|
 :pattern ( (ExistsTxnSenderAccount m@@4 txn))
)))
(assert (forall ((txn@@0 T@Transaction) ) (! (= (TxnSenderAddress txn@@0) (|sender#Transaction| txn@@0))
 :qid |testfunc.380:39|
 :skolemid |48|
 :pattern ( (TxnSenderAddress txn@@0))
)))
(assert (forall ((i@@10 Int) (|l#0| Int) (|l#1| (Array Int T@Value)) (|l#2| (Array Int T@Value)) (|l#3| Int) ) (! (= (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10) (ite (< i@@10 |l#0|) (select |l#1| i@@10) (select |l#2| (- i@@10 |l#3|))))
 :qid |testfunc.113:17|
 :skolemid |49|
 :pattern ( (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10))
)))
(assert (forall ((i@@11 Int) (|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| (Array Int T@Value)) (|l#3@@0| Int) (|l#4| Int) (|l#5| T@Value) ) (! (= (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11) (ite  (and (<= |l#0@@0| i@@11) (< i@@11 |l#1@@0|)) (select |l#2@@0| (- (- |l#3@@0| i@@11) |l#4|)) |l#5|))
 :qid |testfunc.118:17|
 :skolemid |50|
 :pattern ( (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11))
)))
; Valid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun abort_flag@5 () Bool)
(declare-fun %lbl%@2 () Bool)
(declare-fun %lbl%+3 () Bool)
(declare-fun m@35 () T@Memory)
(declare-fun m@33 () T@Memory)
(declare-fun local_counter () Int)
(declare-fun inline$CopyOrMoveValue$9$local@0 () T@Value)
(declare-fun inline$TestFuncCall_h$0$ret0@1 () T@Value)
(declare-fun abort_flag@4 () Bool)
(declare-fun %lbl%+4 () Bool)
(declare-fun %lbl%+5 () Bool)
(declare-fun inline$TestFuncCall_h$0$tmp@4 () T@Value)
(declare-fun %lbl%+6 () Bool)
(declare-fun %lbl%+7 () Bool)
(declare-fun abort_flag@3 () Bool)
(declare-fun %lbl%+8 () Bool)
(declare-fun m@34 () T@Memory)
(declare-fun inline$LdConst$4$ret@1 () T@Value)
(declare-fun %lbl%+9 () Bool)
(declare-fun %lbl%+10 () Bool)
(declare-fun %lbl%+11 () Bool)
(declare-fun m@32 () T@Memory)
(declare-fun inline$Not$1$dst@1 () T@Value)
(declare-fun %lbl%+12 () Bool)
(declare-fun inline$Not$1$src@0 () T@Value)
(declare-fun %lbl%+13 () Bool)
(declare-fun %lbl%+14 () Bool)
(declare-fun m@31 () T@Memory)
(declare-fun inline$Or$0$dst@1 () T@Value)
(declare-fun %lbl%+15 () Bool)
(declare-fun inline$Or$0$src1@0 () T@Value)
(declare-fun inline$Or$0$src2@0 () T@Value)
(declare-fun %lbl%+16 () Bool)
(declare-fun %lbl%+17 () Bool)
(declare-fun m@30 () T@Memory)
(declare-fun inline$And$1$dst@1 () T@Value)
(declare-fun %lbl%+18 () Bool)
(declare-fun inline$And$1$src1@0 () T@Value)
(declare-fun inline$And$1$src2@0 () T@Value)
(declare-fun %lbl%+19 () Bool)
(declare-fun %lbl%+20 () Bool)
(declare-fun m@29 () T@Memory)
(declare-fun m@28 () T@Memory)
(declare-fun inline$LdConst$3$ret@1 () T@Value)
(declare-fun inline$TestFuncCall_h$0$tmp@3 () T@Value)
(declare-fun %lbl%+21 () Bool)
(declare-fun %lbl%+22 () Bool)
(declare-fun m@27 () T@Memory)
(declare-fun inline$CopyOrMoveValue$8$local@0 () T@Value)
(declare-fun %lbl%+23 () Bool)
(declare-fun %lbl%+24 () Bool)
(declare-fun m@26 () T@Memory)
(declare-fun inline$Not$0$dst@1 () T@Value)
(declare-fun %lbl%+25 () Bool)
(declare-fun inline$Not$0$src@0 () T@Value)
(declare-fun %lbl%+26 () Bool)
(declare-fun %lbl%+27 () Bool)
(declare-fun m@25 () T@Memory)
(declare-fun inline$CopyOrMoveValue$7$local@0 () T@Value)
(declare-fun %lbl%+28 () Bool)
(declare-fun %lbl%+29 () Bool)
(declare-fun m@24 () T@Memory)
(declare-fun inline$And$0$dst@1 () T@Value)
(declare-fun %lbl%+30 () Bool)
(declare-fun inline$And$0$src1@0 () T@Value)
(declare-fun inline$And$0$src2@0 () T@Value)
(declare-fun %lbl%+31 () Bool)
(declare-fun %lbl%+32 () Bool)
(declare-fun m@23 () T@Memory)
(declare-fun m@22 () T@Memory)
(declare-fun inline$LdConst$2$ret@1 () T@Value)
(declare-fun inline$TestFuncCall_h$0$tmp@2 () T@Value)
(declare-fun %lbl%+33 () Bool)
(declare-fun %lbl%+34 () Bool)
(declare-fun m@21 () T@Memory)
(declare-fun inline$CopyOrMoveValue$6$local@0 () T@Value)
(declare-fun %lbl%+35 () Bool)
(declare-fun %lbl%+36 () Bool)
(declare-fun m@20 () T@Memory)
(declare-fun inline$CopyOrMoveValue$5$local@0 () T@Value)
(declare-fun %lbl%+37 () Bool)
(declare-fun %lbl%+38 () Bool)
(declare-fun m@19 () T@Memory)
(declare-fun m@18 () T@Memory)
(declare-fun inline$CopyOrMoveValue$12$local@0 () T@Value)
(declare-fun %lbl%+39 () Bool)
(declare-fun %lbl%+40 () Bool)
(declare-fun inline$TestFuncCall_g$0$ret0@2 () T@Value)
(declare-fun m@17 () T@Memory)
(declare-fun %lbl%+41 () Bool)
(declare-fun abort_flag@2 () Bool)
(declare-fun m@16 () T@Memory)
(declare-fun m@15 () T@Memory)
(declare-fun local_counter@0 () Int)
(declare-fun inline$AddU64$1$dst@2 () T@Value)
(declare-fun inline$TestFuncCall_g$0$ret0@1 () T@Value)
(declare-fun %lbl%+42 () Bool)
(declare-fun m@12 () T@Memory)
(declare-fun %lbl%+43 () Bool)
(declare-fun inline$AddU64$1$src1@0 () T@Value)
(declare-fun inline$AddU64$1$src2@0 () T@Value)
(declare-fun inline$AddU64$1$dst@1 () T@Value)
(declare-fun abort_flag () Bool)
(declare-fun %lbl%+44 () Bool)
(declare-fun inline$AddU64$1$dst@0 () T@Value)
(declare-fun %lbl%+45 () Bool)
(declare-fun %lbl%+46 () Bool)
(declare-fun %lbl%+47 () Bool)
(declare-fun m@14 () T@Memory)
(declare-fun inline$LdConst$5$ret@1 () T@Value)
(declare-fun %lbl%+48 () Bool)
(declare-fun %lbl%+49 () Bool)
(declare-fun m@13 () T@Memory)
(declare-fun inline$CopyOrMoveValue$11$local@0 () T@Value)
(declare-fun %lbl%+50 () Bool)
(declare-fun %lbl%+51 () Bool)
(declare-fun inline$TestFuncCall_g$0$x@0 () T@Value)
(declare-fun local_counter@2 () Int)
(declare-fun %lbl%+52 () Bool)
(declare-fun %lbl%@53 () Bool)
(declare-fun txn@@1 () T@Transaction)
(declare-fun %lbl%+54 () Bool)
(declare-fun m@3 () T@Memory)
(declare-fun inline$CopyOrMoveValue$10$local@0 () T@Value)
(declare-fun %lbl%+55 () Bool)
(declare-fun %lbl%+56 () Bool)
(declare-fun inline$TestFuncCall_h$0$tmp@1 () T@Value)
(declare-fun %lbl%+57 () Bool)
(declare-fun m@11 () T@Memory)
(declare-fun m@10 () T@Memory)
(declare-fun inline$CopyOrMoveValue$4$local@0 () T@Value)
(declare-fun abort_flag@1 () Bool)
(declare-fun %lbl%+58 () Bool)
(declare-fun %lbl%+59 () Bool)
(declare-fun inline$TestFuncCall_f$0$ret0@2 () T@Value)
(declare-fun m@9 () T@Memory)
(declare-fun %lbl%+60 () Bool)
(declare-fun %lbl%+61 () Bool)
(declare-fun abort_flag@0 () Bool)
(declare-fun m@8 () T@Memory)
(declare-fun m@7 () T@Memory)
(declare-fun inline$AddU64$0$dst@2 () T@Value)
(declare-fun inline$TestFuncCall_f$0$ret0@1 () T@Value)
(declare-fun %lbl%+62 () Bool)
(declare-fun m@4 () T@Memory)
(declare-fun %lbl%+63 () Bool)
(declare-fun inline$AddU64$0$src1@0 () T@Value)
(declare-fun inline$AddU64$0$src2@0 () T@Value)
(declare-fun inline$AddU64$0$dst@1 () T@Value)
(declare-fun %lbl%+64 () Bool)
(declare-fun inline$AddU64$0$dst@0 () T@Value)
(declare-fun %lbl%+65 () Bool)
(declare-fun %lbl%+66 () Bool)
(declare-fun %lbl%+67 () Bool)
(declare-fun m@6 () T@Memory)
(declare-fun inline$LdConst$1$ret@1 () T@Value)
(declare-fun %lbl%+68 () Bool)
(declare-fun %lbl%+69 () Bool)
(declare-fun m@5 () T@Memory)
(declare-fun inline$CopyOrMoveValue$3$local@0 () T@Value)
(declare-fun %lbl%+70 () Bool)
(declare-fun %lbl%+71 () Bool)
(declare-fun inline$TestFuncCall_f$0$x@0 () T@Value)
(declare-fun local_counter@1 () Int)
(declare-fun %lbl%+72 () Bool)
(declare-fun %lbl%@73 () Bool)
(declare-fun %lbl%+74 () Bool)
(declare-fun inline$CopyOrMoveValue$2$local@0 () T@Value)
(declare-fun %lbl%+75 () Bool)
(declare-fun %lbl%+76 () Bool)
(declare-fun %lbl%+77 () Bool)
(declare-fun m@2 () T@Memory)
(declare-fun inline$CopyOrMoveValue$1$local@0 () T@Value)
(declare-fun %lbl%+78 () Bool)
(declare-fun %lbl%+79 () Bool)
(declare-fun m@1 () T@Memory)
(declare-fun inline$CopyOrMoveValue$0$local@0 () T@Value)
(declare-fun %lbl%+80 () Bool)
(declare-fun %lbl%+81 () Bool)
(declare-fun m@0 () T@Memory)
(declare-fun inline$LdConst$0$ret@1 () T@Value)
(declare-fun %lbl%+82 () Bool)
(declare-fun %lbl%+83 () Bool)
(declare-fun b () T@Value)
(declare-fun m@@5 () T@Memory)
(declare-fun %lbl%+84 () Bool)
(declare-fun %lbl%@85 () Bool)
(declare-fun %lbl%+86 () Bool)
(declare-fun %lbl%+87 () Bool)
(push 1)
(set-info :boogie-vc-id TestFuncCall_h_verify)
(assert (not
(let ((inline$TestFuncCall_h$0$Return_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (and (! (or %lbl%@1  (=> (not (|b#Boolean| (Boolean false))) (not abort_flag@5))) :lblneg @1) (=> (=> (not (|b#Boolean| (Boolean false))) (not abort_flag@5)) (! (or %lbl%@2  (=> (|b#Boolean| (Boolean false)) abort_flag@5)) :lblneg @2))))))
(let ((inline$TestFuncCall_h$0$anon12_Then$1_correct  (=> (! (and %lbl%+3 true) :lblpos +3) (=> (and (and (= m@35 (UpdateLocal m@33 (+ local_counter 23) inline$CopyOrMoveValue$9$local@0)) (= inline$TestFuncCall_h$0$ret0@1 (GetLocal m@35 (+ local_counter 23)))) (and (=> abort_flag@5 abort_flag@4) (=> abort_flag@4 abort_flag@5))) inline$TestFuncCall_h$0$Return_correct))))
(let ((inline$CopyOrMoveValue$9$Entry_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (=> (= inline$CopyOrMoveValue$9$local@0 (GetLocal m@33 (+ local_counter 2))) inline$TestFuncCall_h$0$anon12_Then$1_correct))))
(let ((inline$TestFuncCall_h$0$anon12_Then_correct  (=> (! (and %lbl%+5 true) :lblpos +5) (=> (not (|b#Boolean| inline$TestFuncCall_h$0$tmp@4)) inline$CopyOrMoveValue$9$Entry_correct))))
(let ((inline$TestFuncCall_h$0$Label_Abort_correct  (=> (! (and %lbl%+6 true) :lblpos +6) (=> (and (=> abort_flag@5 true) (=> true abort_flag@5)) inline$TestFuncCall_h$0$Return_correct))))
(let ((inline$TestFuncCall_h$0$anon11_Then_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> abort_flag@3 inline$TestFuncCall_h$0$Label_Abort_correct))))
(let ((inline$TestFuncCall_h$0$anon12_Else$1_correct  (=> (! (and %lbl%+8 true) :lblpos +8) (=> (= m@34 (UpdateLocal m@33 (+ local_counter 22) inline$LdConst$4$ret@1)) inline$TestFuncCall_h$0$Label_Abort_correct))))
(let ((inline$LdConst$4$anon0_correct  (=> (! (and %lbl%+9 true) :lblpos +9) (=> (= inline$LdConst$4$ret@1 (Integer 42)) inline$TestFuncCall_h$0$anon12_Else$1_correct))))
(let ((inline$TestFuncCall_h$0$anon12_Else_correct  (=> (! (and %lbl%+10 true) :lblpos +10) (=> (|b#Boolean| inline$TestFuncCall_h$0$tmp@4) inline$LdConst$4$anon0_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$11_correct  (=> (! (and %lbl%+11 true) :lblpos +11) (=> (and (= m@33 (UpdateLocal m@32 (+ local_counter 21) inline$Not$1$dst@1)) (= inline$TestFuncCall_h$0$tmp@4 (GetLocal m@33 (+ local_counter 21)))) (and inline$TestFuncCall_h$0$anon12_Then_correct inline$TestFuncCall_h$0$anon12_Else_correct)))))
(let ((inline$Not$1$anon0_correct  (=> (! (and %lbl%+12 true) :lblpos +12) (=> (and (is-Boolean inline$Not$1$src@0) (= inline$Not$1$dst@1 (Boolean  (not (|b#Boolean| inline$Not$1$src@0))))) inline$TestFuncCall_h$0$Label_11$11_correct))))
(let ((inline$Not$1$Entry_correct  (=> (! (and %lbl%+13 true) :lblpos +13) (=> (= inline$Not$1$src@0 (GetLocal m@32 (+ local_counter 20))) inline$Not$1$anon0_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$10_correct  (=> (! (and %lbl%+14 true) :lblpos +14) (=> (= m@32 (UpdateLocal m@31 (+ local_counter 20) inline$Or$0$dst@1)) inline$Not$1$Entry_correct))))
(let ((inline$Or$0$anon0_correct  (=> (! (and %lbl%+15 true) :lblpos +15) (=> (and (and (is-Boolean inline$Or$0$src1@0) (is-Boolean inline$Or$0$src2@0)) (= inline$Or$0$dst@1 (Boolean  (or (|b#Boolean| inline$Or$0$src1@0) (|b#Boolean| inline$Or$0$src2@0))))) inline$TestFuncCall_h$0$Label_11$10_correct))))
(let ((inline$Or$0$Entry_correct  (=> (! (and %lbl%+16 true) :lblpos +16) (=> (and (= inline$Or$0$src1@0 (GetLocal m@31 (+ local_counter 13))) (= inline$Or$0$src2@0 (GetLocal m@31 (+ local_counter 19)))) inline$Or$0$anon0_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$9_correct  (=> (! (and %lbl%+17 true) :lblpos +17) (=> (= m@31 (UpdateLocal m@30 (+ local_counter 19) inline$And$1$dst@1)) inline$Or$0$Entry_correct))))
(let ((inline$And$1$anon0_correct  (=> (! (and %lbl%+18 true) :lblpos +18) (=> (and (and (is-Boolean inline$And$1$src1@0) (is-Boolean inline$And$1$src2@0)) (= inline$And$1$dst@1 (Boolean  (and (|b#Boolean| inline$And$1$src1@0) (|b#Boolean| inline$And$1$src2@0))))) inline$TestFuncCall_h$0$Label_11$9_correct))))
(let ((inline$And$1$Entry_correct  (=> (! (and %lbl%+19 true) :lblpos +19) (=> (and (= inline$And$1$src1@0 (GetLocal m@30 (+ local_counter 15))) (= inline$And$1$src2@0 (GetLocal m@30 (+ local_counter 18)))) inline$And$1$anon0_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$8_correct  (=> (! (and %lbl%+20 true) :lblpos +20) (=> (= m@29 (UpdateLocal m@28 (+ local_counter 17) inline$LdConst$3$ret@1)) (=> (and (= inline$TestFuncCall_h$0$tmp@3 (Boolean (IsEqual (GetLocal m@29 (+ local_counter 16)) (GetLocal m@29 (+ local_counter 17))))) (= m@30 (UpdateLocal m@29 (+ local_counter 18) inline$TestFuncCall_h$0$tmp@3))) inline$And$1$Entry_correct)))))
(let ((inline$LdConst$3$anon0_correct  (=> (! (and %lbl%+21 true) :lblpos +21) (=> (= inline$LdConst$3$ret@1 (Integer 5)) inline$TestFuncCall_h$0$Label_11$8_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$7_correct  (=> (! (and %lbl%+22 true) :lblpos +22) (=> (= m@28 (UpdateLocal m@27 (+ local_counter 16) inline$CopyOrMoveValue$8$local@0)) inline$LdConst$3$anon0_correct))))
(let ((inline$CopyOrMoveValue$8$Entry_correct  (=> (! (and %lbl%+23 true) :lblpos +23) (=> (= inline$CopyOrMoveValue$8$local@0 (GetLocal m@27 (+ local_counter 2))) inline$TestFuncCall_h$0$Label_11$7_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$6_correct  (=> (! (and %lbl%+24 true) :lblpos +24) (=> (= m@27 (UpdateLocal m@26 (+ local_counter 15) inline$Not$0$dst@1)) inline$CopyOrMoveValue$8$Entry_correct))))
(let ((inline$Not$0$anon0_correct  (=> (! (and %lbl%+25 true) :lblpos +25) (=> (and (is-Boolean inline$Not$0$src@0) (= inline$Not$0$dst@1 (Boolean  (not (|b#Boolean| inline$Not$0$src@0))))) inline$TestFuncCall_h$0$Label_11$6_correct))))
(let ((inline$Not$0$Entry_correct  (=> (! (and %lbl%+26 true) :lblpos +26) (=> (= inline$Not$0$src@0 (GetLocal m@26 (+ local_counter 14))) inline$Not$0$anon0_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$5_correct  (=> (! (and %lbl%+27 true) :lblpos +27) (=> (= m@26 (UpdateLocal m@25 (+ local_counter 14) inline$CopyOrMoveValue$7$local@0)) inline$Not$0$Entry_correct))))
(let ((inline$CopyOrMoveValue$7$Entry_correct  (=> (! (and %lbl%+28 true) :lblpos +28) (=> (= inline$CopyOrMoveValue$7$local@0 (GetLocal m@25 (+ local_counter 0))) inline$TestFuncCall_h$0$Label_11$5_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$4_correct  (=> (! (and %lbl%+29 true) :lblpos +29) (=> (= m@25 (UpdateLocal m@24 (+ local_counter 13) inline$And$0$dst@1)) inline$CopyOrMoveValue$7$Entry_correct))))
(let ((inline$And$0$anon0_correct  (=> (! (and %lbl%+30 true) :lblpos +30) (=> (and (and (is-Boolean inline$And$0$src1@0) (is-Boolean inline$And$0$src2@0)) (= inline$And$0$dst@1 (Boolean  (and (|b#Boolean| inline$And$0$src1@0) (|b#Boolean| inline$And$0$src2@0))))) inline$TestFuncCall_h$0$Label_11$4_correct))))
(let ((inline$And$0$Entry_correct  (=> (! (and %lbl%+31 true) :lblpos +31) (=> (and (= inline$And$0$src1@0 (GetLocal m@24 (+ local_counter 9))) (= inline$And$0$src2@0 (GetLocal m@24 (+ local_counter 12)))) inline$And$0$anon0_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$3_correct  (=> (! (and %lbl%+32 true) :lblpos +32) (=> (= m@23 (UpdateLocal m@22 (+ local_counter 11) inline$LdConst$2$ret@1)) (=> (and (= inline$TestFuncCall_h$0$tmp@2 (Boolean (IsEqual (GetLocal m@23 (+ local_counter 10)) (GetLocal m@23 (+ local_counter 11))))) (= m@24 (UpdateLocal m@23 (+ local_counter 12) inline$TestFuncCall_h$0$tmp@2))) inline$And$0$Entry_correct)))))
(let ((inline$LdConst$2$anon0_correct  (=> (! (and %lbl%+33 true) :lblpos +33) (=> (= inline$LdConst$2$ret@1 (Integer 4)) inline$TestFuncCall_h$0$Label_11$3_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$2_correct  (=> (! (and %lbl%+34 true) :lblpos +34) (=> (= m@22 (UpdateLocal m@21 (+ local_counter 10) inline$CopyOrMoveValue$6$local@0)) inline$LdConst$2$anon0_correct))))
(let ((inline$CopyOrMoveValue$6$Entry_correct  (=> (! (and %lbl%+35 true) :lblpos +35) (=> (= inline$CopyOrMoveValue$6$local@0 (GetLocal m@21 (+ local_counter 2))) inline$TestFuncCall_h$0$Label_11$2_correct))))
(let ((inline$TestFuncCall_h$0$Label_11$1_correct  (=> (! (and %lbl%+36 true) :lblpos +36) (=> (= m@21 (UpdateLocal m@20 (+ local_counter 9) inline$CopyOrMoveValue$5$local@0)) inline$CopyOrMoveValue$6$Entry_correct))))
(let ((inline$CopyOrMoveValue$5$Entry_correct  (=> (! (and %lbl%+37 true) :lblpos +37) (=> (= inline$CopyOrMoveValue$5$local@0 (GetLocal m@20 (+ local_counter 0))) inline$TestFuncCall_h$0$Label_11$1_correct))))
(let ((inline$TestFuncCall_h$0$anon11_Else$1_correct  (=> (! (and %lbl%+38 true) :lblpos +38) (=> (= m@19 (UpdateLocal m@18 (+ local_counter 2) inline$CopyOrMoveValue$12$local@0)) (=> (and (and (=> abort_flag@4 abort_flag@3) (=> abort_flag@3 abort_flag@4)) (= m@20 m@19)) inline$CopyOrMoveValue$5$Entry_correct)))))
(let ((inline$CopyOrMoveValue$12$Entry_correct  (=> (! (and %lbl%+39 true) :lblpos +39) (=> (= inline$CopyOrMoveValue$12$local@0 (GetLocal m@18 (+ local_counter 8))) inline$TestFuncCall_h$0$anon11_Else$1_correct))))
(let ((inline$TestFuncCall_h$0$anon11_Else_correct  (=> (! (and %lbl%+40 true) :lblpos +40) (=> (not abort_flag@3) (=> (and (and (and (is-Integer inline$TestFuncCall_g$0$ret0@2) (>= (|i#Integer| inline$TestFuncCall_g$0$ret0@2) 0)) (<= (|i#Integer| inline$TestFuncCall_g$0$ret0@2) MAX_U64)) (= m@18 (UpdateLocal m@17 (+ local_counter 8) inline$TestFuncCall_g$0$ret0@2))) inline$CopyOrMoveValue$12$Entry_correct)))))
(let ((inline$TestFuncCall_g$0$anon3_Else_correct  (=> (! (and %lbl%+41 true) :lblpos +41) (=> (not abort_flag@2) (=> (and (= m@16 (UpdateLocal m@15 (+ local_counter@0 3) inline$AddU64$1$dst@2)) (= inline$TestFuncCall_g$0$ret0@1 (GetLocal m@16 (+ local_counter@0 3)))) (=> (and (and (= m@17 m@16) (= inline$TestFuncCall_g$0$ret0@2 inline$TestFuncCall_g$0$ret0@1)) (and (=> abort_flag@3 abort_flag@2) (=> abort_flag@2 abort_flag@3))) (and inline$TestFuncCall_h$0$anon11_Then_correct inline$TestFuncCall_h$0$anon11_Else_correct)))))))
(let ((inline$TestFuncCall_g$0$anon3_Then_correct  (=> (! (and %lbl%+42 true) :lblpos +42) (=> abort_flag@2 (=> (and (and (= m@17 m@12) (= inline$TestFuncCall_g$0$ret0@2 DefaultValue)) (and (=> abort_flag@3 true) (=> true abort_flag@3))) (and inline$TestFuncCall_h$0$anon11_Then_correct inline$TestFuncCall_h$0$anon11_Else_correct))))))
(let ((inline$AddU64$1$anon3_Else_correct  (=> (! (and %lbl%+43 true) :lblpos +43) (=> (>= MAX_U64 (+ (|i#Integer| inline$AddU64$1$src1@0) (|i#Integer| inline$AddU64$1$src2@0))) (=> (and (and (= inline$AddU64$1$dst@1 (Integer (+ (|i#Integer| inline$AddU64$1$src1@0) (|i#Integer| inline$AddU64$1$src2@0)))) (= inline$AddU64$1$dst@2 inline$AddU64$1$dst@1)) (and (=> abort_flag@2 abort_flag) (=> abort_flag abort_flag@2))) (and inline$TestFuncCall_g$0$anon3_Then_correct inline$TestFuncCall_g$0$anon3_Else_correct))))))
(let ((inline$AddU64$1$anon3_Then_correct  (=> (! (and %lbl%+44 true) :lblpos +44) (=> (and (and (> (+ (|i#Integer| inline$AddU64$1$src1@0) (|i#Integer| inline$AddU64$1$src2@0)) MAX_U64) (= inline$AddU64$1$dst@2 inline$AddU64$1$dst@0)) (and (=> abort_flag@2 true) (=> true abort_flag@2))) (and inline$TestFuncCall_g$0$anon3_Then_correct inline$TestFuncCall_g$0$anon3_Else_correct)))))
(let ((inline$AddU64$1$anon0_correct  (=> (! (and %lbl%+45 true) :lblpos +45) (=> (and (and (and (is-Integer inline$AddU64$1$src1@0) (>= (|i#Integer| inline$AddU64$1$src1@0) 0)) (<= (|i#Integer| inline$AddU64$1$src1@0) MAX_U64)) (and (and (is-Integer inline$AddU64$1$src2@0) (>= (|i#Integer| inline$AddU64$1$src2@0) 0)) (<= (|i#Integer| inline$AddU64$1$src2@0) MAX_U64))) (and inline$AddU64$1$anon3_Then_correct inline$AddU64$1$anon3_Else_correct)))))
(let ((inline$AddU64$1$Entry_correct  (=> (! (and %lbl%+46 true) :lblpos +46) (=> (and (= inline$AddU64$1$src1@0 (GetLocal m@15 (+ local_counter@0 1))) (= inline$AddU64$1$src2@0 (GetLocal m@15 (+ local_counter@0 2)))) inline$AddU64$1$anon0_correct))))
(let ((inline$TestFuncCall_g$0$anon0$2_correct  (=> (! (and %lbl%+47 true) :lblpos +47) (=> (= m@15 (UpdateLocal m@14 (+ local_counter@0 2) inline$LdConst$5$ret@1)) inline$AddU64$1$Entry_correct))))
(let ((inline$LdConst$5$anon0_correct  (=> (! (and %lbl%+48 true) :lblpos +48) (=> (= inline$LdConst$5$ret@1 (Integer 2)) inline$TestFuncCall_g$0$anon0$2_correct))))
(let ((inline$TestFuncCall_g$0$anon0$1_correct  (=> (! (and %lbl%+49 true) :lblpos +49) (=> (= m@14 (UpdateLocal m@13 (+ local_counter@0 1) inline$CopyOrMoveValue$11$local@0)) inline$LdConst$5$anon0_correct))))
(let ((inline$CopyOrMoveValue$11$Entry_correct  (=> (! (and %lbl%+50 true) :lblpos +50) (=> (= inline$CopyOrMoveValue$11$local@0 (GetLocal m@13 (+ local_counter@0 0))) inline$TestFuncCall_g$0$anon0$1_correct))))
(let ((inline$TestFuncCall_g$0$anon0_correct  (=> (! (and %lbl%+51 true) :lblpos +51) (=> (not abort_flag) (=> (and (and (and (is-Integer inline$TestFuncCall_g$0$x@0) (>= (|i#Integer| inline$TestFuncCall_g$0$x@0) 0)) (<= (|i#Integer| inline$TestFuncCall_g$0$x@0) MAX_U64)) (and (= local_counter@2 (+ local_counter@0 4)) (= m@13 (UpdateLocal m@12 (+ local_counter@0 0) inline$TestFuncCall_g$0$x@0)))) inline$CopyOrMoveValue$11$Entry_correct)))))
(let ((inline$TestFuncCall_g$0$Entry_correct  (=> (! (and %lbl%+52 true) :lblpos +52) (=> (= inline$TestFuncCall_g$0$x@0 (GetLocal m@12 (+ local_counter 7))) (and (! (or %lbl%@53 (ExistsTxnSenderAccount m@12 txn@@1)) :lblneg @53) (=> (ExistsTxnSenderAccount m@12 txn@@1) inline$TestFuncCall_g$0$anon0_correct))))))
(let ((inline$TestFuncCall_h$0$anon9_Then$1_correct  (=> (! (and %lbl%+54 true) :lblpos +54) (=> (= m@12 (UpdateLocal m@3 (+ local_counter 7) inline$CopyOrMoveValue$10$local@0)) inline$TestFuncCall_g$0$Entry_correct))))
(let ((inline$CopyOrMoveValue$10$Entry_correct  (=> (! (and %lbl%+55 true) :lblpos +55) (=> (= inline$CopyOrMoveValue$10$local@0 (GetLocal m@3 (+ local_counter 1))) inline$TestFuncCall_h$0$anon9_Then$1_correct))))
(let ((inline$TestFuncCall_h$0$anon9_Then_correct  (=> (! (and %lbl%+56 true) :lblpos +56) (=> (not (|b#Boolean| inline$TestFuncCall_h$0$tmp@1)) inline$CopyOrMoveValue$10$Entry_correct))))
(let ((inline$TestFuncCall_h$0$anon10_Else$1_correct  (=> (! (and %lbl%+57 true) :lblpos +57) (=> (= m@11 (UpdateLocal m@10 (+ local_counter 2) inline$CopyOrMoveValue$4$local@0)) (=> (and (and (=> abort_flag@4 abort_flag@1) (=> abort_flag@1 abort_flag@4)) (= m@20 m@11)) inline$CopyOrMoveValue$5$Entry_correct)))))
(let ((inline$CopyOrMoveValue$4$Entry_correct  (=> (! (and %lbl%+58 true) :lblpos +58) (=> (= inline$CopyOrMoveValue$4$local@0 (GetLocal m@10 (+ local_counter 6))) inline$TestFuncCall_h$0$anon10_Else$1_correct))))
(let ((inline$TestFuncCall_h$0$anon10_Else_correct  (=> (! (and %lbl%+59 true) :lblpos +59) (=> (not abort_flag@1) (=> (and (and (and (is-Integer inline$TestFuncCall_f$0$ret0@2) (>= (|i#Integer| inline$TestFuncCall_f$0$ret0@2) 0)) (<= (|i#Integer| inline$TestFuncCall_f$0$ret0@2) MAX_U64)) (= m@10 (UpdateLocal m@9 (+ local_counter 6) inline$TestFuncCall_f$0$ret0@2))) inline$CopyOrMoveValue$4$Entry_correct)))))
(let ((inline$TestFuncCall_h$0$anon10_Then_correct  (=> (! (and %lbl%+60 true) :lblpos +60) (=> abort_flag@1 inline$TestFuncCall_h$0$Label_Abort_correct))))
(let ((inline$TestFuncCall_f$0$anon3_Else_correct  (=> (! (and %lbl%+61 true) :lblpos +61) (=> (not abort_flag@0) (=> (and (= m@8 (UpdateLocal m@7 (+ local_counter@0 3) inline$AddU64$0$dst@2)) (= inline$TestFuncCall_f$0$ret0@1 (GetLocal m@8 (+ local_counter@0 3)))) (=> (and (and (= m@9 m@8) (= inline$TestFuncCall_f$0$ret0@2 inline$TestFuncCall_f$0$ret0@1)) (and (=> abort_flag@1 abort_flag@0) (=> abort_flag@0 abort_flag@1))) (and inline$TestFuncCall_h$0$anon10_Then_correct inline$TestFuncCall_h$0$anon10_Else_correct)))))))
(let ((inline$TestFuncCall_f$0$anon3_Then_correct  (=> (! (and %lbl%+62 true) :lblpos +62) (=> abort_flag@0 (=> (and (and (= m@9 m@4) (= inline$TestFuncCall_f$0$ret0@2 DefaultValue)) (and (=> abort_flag@1 true) (=> true abort_flag@1))) (and inline$TestFuncCall_h$0$anon10_Then_correct inline$TestFuncCall_h$0$anon10_Else_correct))))))
(let ((inline$AddU64$0$anon3_Else_correct  (=> (! (and %lbl%+63 true) :lblpos +63) (=> (>= MAX_U64 (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0))) (=> (and (and (= inline$AddU64$0$dst@1 (Integer (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0)))) (= inline$AddU64$0$dst@2 inline$AddU64$0$dst@1)) (and (=> abort_flag@0 abort_flag) (=> abort_flag abort_flag@0))) (and inline$TestFuncCall_f$0$anon3_Then_correct inline$TestFuncCall_f$0$anon3_Else_correct))))))
(let ((inline$AddU64$0$anon3_Then_correct  (=> (! (and %lbl%+64 true) :lblpos +64) (=> (and (and (> (+ (|i#Integer| inline$AddU64$0$src1@0) (|i#Integer| inline$AddU64$0$src2@0)) MAX_U64) (= inline$AddU64$0$dst@2 inline$AddU64$0$dst@0)) (and (=> abort_flag@0 true) (=> true abort_flag@0))) (and inline$TestFuncCall_f$0$anon3_Then_correct inline$TestFuncCall_f$0$anon3_Else_correct)))))
(let ((inline$AddU64$0$anon0_correct  (=> (! (and %lbl%+65 true) :lblpos +65) (=> (and (and (and (is-Integer inline$AddU64$0$src1@0) (>= (|i#Integer| inline$AddU64$0$src1@0) 0)) (<= (|i#Integer| inline$AddU64$0$src1@0) MAX_U64)) (and (and (is-Integer inline$AddU64$0$src2@0) (>= (|i#Integer| inline$AddU64$0$src2@0) 0)) (<= (|i#Integer| inline$AddU64$0$src2@0) MAX_U64))) (and inline$AddU64$0$anon3_Then_correct inline$AddU64$0$anon3_Else_correct)))))
(let ((inline$AddU64$0$Entry_correct  (=> (! (and %lbl%+66 true) :lblpos +66) (=> (and (= inline$AddU64$0$src1@0 (GetLocal m@7 (+ local_counter@0 1))) (= inline$AddU64$0$src2@0 (GetLocal m@7 (+ local_counter@0 2)))) inline$AddU64$0$anon0_correct))))
(let ((inline$TestFuncCall_f$0$anon0$2_correct  (=> (! (and %lbl%+67 true) :lblpos +67) (=> (= m@7 (UpdateLocal m@6 (+ local_counter@0 2) inline$LdConst$1$ret@1)) inline$AddU64$0$Entry_correct))))
(let ((inline$LdConst$1$anon0_correct  (=> (! (and %lbl%+68 true) :lblpos +68) (=> (= inline$LdConst$1$ret@1 (Integer 1)) inline$TestFuncCall_f$0$anon0$2_correct))))
(let ((inline$TestFuncCall_f$0$anon0$1_correct  (=> (! (and %lbl%+69 true) :lblpos +69) (=> (= m@6 (UpdateLocal m@5 (+ local_counter@0 1) inline$CopyOrMoveValue$3$local@0)) inline$LdConst$1$anon0_correct))))
(let ((inline$CopyOrMoveValue$3$Entry_correct  (=> (! (and %lbl%+70 true) :lblpos +70) (=> (= inline$CopyOrMoveValue$3$local@0 (GetLocal m@5 (+ local_counter@0 0))) inline$TestFuncCall_f$0$anon0$1_correct))))
(let ((inline$TestFuncCall_f$0$anon0_correct  (=> (! (and %lbl%+71 true) :lblpos +71) (=> (not abort_flag) (=> (and (and (and (is-Integer inline$TestFuncCall_f$0$x@0) (>= (|i#Integer| inline$TestFuncCall_f$0$x@0) 0)) (<= (|i#Integer| inline$TestFuncCall_f$0$x@0) MAX_U64)) (and (= local_counter@1 (+ local_counter@0 4)) (= m@5 (UpdateLocal m@4 (+ local_counter@0 0) inline$TestFuncCall_f$0$x@0)))) inline$CopyOrMoveValue$3$Entry_correct)))))
(let ((inline$TestFuncCall_f$0$Entry_correct  (=> (! (and %lbl%+72 true) :lblpos +72) (=> (= inline$TestFuncCall_f$0$x@0 (GetLocal m@4 (+ local_counter 5))) (and (! (or %lbl%@73 (ExistsTxnSenderAccount m@4 txn@@1)) :lblneg @73) (=> (ExistsTxnSenderAccount m@4 txn@@1) inline$TestFuncCall_f$0$anon0_correct))))))
(let ((inline$TestFuncCall_h$0$anon9_Else$1_correct  (=> (! (and %lbl%+74 true) :lblpos +74) (=> (= m@4 (UpdateLocal m@3 (+ local_counter 5) inline$CopyOrMoveValue$2$local@0)) inline$TestFuncCall_f$0$Entry_correct))))
(let ((inline$CopyOrMoveValue$2$Entry_correct  (=> (! (and %lbl%+75 true) :lblpos +75) (=> (= inline$CopyOrMoveValue$2$local@0 (GetLocal m@3 (+ local_counter 1))) inline$TestFuncCall_h$0$anon9_Else$1_correct))))
(let ((inline$TestFuncCall_h$0$anon9_Else_correct  (=> (! (and %lbl%+76 true) :lblpos +76) (=> (|b#Boolean| inline$TestFuncCall_h$0$tmp@1) inline$CopyOrMoveValue$2$Entry_correct))))
(let ((inline$TestFuncCall_h$0$anon0$3_correct  (=> (! (and %lbl%+77 true) :lblpos +77) (=> (and (= m@3 (UpdateLocal m@2 (+ local_counter 4) inline$CopyOrMoveValue$1$local@0)) (= inline$TestFuncCall_h$0$tmp@1 (GetLocal m@3 (+ local_counter 4)))) (and inline$TestFuncCall_h$0$anon9_Then_correct inline$TestFuncCall_h$0$anon9_Else_correct)))))
(let ((inline$CopyOrMoveValue$1$Entry_correct  (=> (! (and %lbl%+78 true) :lblpos +78) (=> (= inline$CopyOrMoveValue$1$local@0 (GetLocal m@2 (+ local_counter 0))) inline$TestFuncCall_h$0$anon0$3_correct))))
(let ((inline$TestFuncCall_h$0$anon0$2_correct  (=> (! (and %lbl%+79 true) :lblpos +79) (=> (= m@2 (UpdateLocal m@1 (+ local_counter 1) inline$CopyOrMoveValue$0$local@0)) inline$CopyOrMoveValue$1$Entry_correct))))
(let ((inline$CopyOrMoveValue$0$Entry_correct  (=> (! (and %lbl%+80 true) :lblpos +80) (=> (= inline$CopyOrMoveValue$0$local@0 (GetLocal m@1 (+ local_counter 3))) inline$TestFuncCall_h$0$anon0$2_correct))))
(let ((inline$TestFuncCall_h$0$anon0$1_correct  (=> (! (and %lbl%+81 true) :lblpos +81) (=> (= m@1 (UpdateLocal m@0 (+ local_counter 3) inline$LdConst$0$ret@1)) inline$CopyOrMoveValue$0$Entry_correct))))
(let ((inline$LdConst$0$anon0_correct  (=> (! (and %lbl%+82 true) :lblpos +82) (=> (= inline$LdConst$0$ret@1 (Integer 3)) inline$TestFuncCall_h$0$anon0$1_correct))))
(let ((inline$TestFuncCall_h$0$anon0_correct  (=> (! (and %lbl%+83 true) :lblpos +83) (=> (and (and (not abort_flag) (is-Boolean b)) (and (= local_counter@0 (+ local_counter 24)) (= m@0 (UpdateLocal m@@5 (+ local_counter 0) b)))) inline$LdConst$0$anon0_correct))))
(let ((inline$TestFuncCall_h$0$Entry_correct  (=> (! (and %lbl%+84 true) :lblpos +84) (and (! (or %lbl%@85 (ExistsTxnSenderAccount m@@5 txn@@1)) :lblneg @85) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestFuncCall_h$0$anon0_correct)))))
(let ((anon0_correct  (=> (! (and %lbl%+86 true) :lblpos +86) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestFuncCall_h$0$Entry_correct))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+87 true) :lblpos +87) anon0_correct)))
PreconditionGeneratedEntry_correct)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))
(check-sat)
(pop 1)
; Valid
