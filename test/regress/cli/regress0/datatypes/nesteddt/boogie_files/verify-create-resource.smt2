; using cav@cav20-artifact:~/artifact/libra/language/move-prover/bytecode-to-boogie$ time cargo run test_mvir/verify-stdlib/verify-create-resource.mvir --output verify-create-resource.bpl --boogie-exe ~/boogie/Binaries/boogie -B /useArrayTheory --z3-exe /usr/bin/z3 --boogie /proverLog:verify-create-resource.smt2
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
(declare-fun TestSpecs_R_x () Int)
(declare-fun TestSpecs_R_type_value () T@TypeValue)
(declare-fun TestSpecs_R () T@TypeName)
(assert (= (|size#Path| EmptyPath) 0))
(assert (forall ((p T@Path) (i Int) ) (! (= (path_index_at p i) (select (|p#Path| p) i))
 :qid |verifycr.18:36|
 :skolemid |0|
 :pattern ( (path_index_at p i))
)))
(assert (= (|l#TypeValueArray| EmptyTypeValueArray) 0))
(assert (= (|v#TypeValueArray| EmptyTypeValueArray) ((as const (Array Int T@TypeValue)) DefaultTypeValue)))
(assert (forall ((ta T@TypeValueArray) (tv T@TypeValue) ) (! (= (ExtendTypeValueArray ta tv) (TypeValueArray (store (|v#TypeValueArray| ta) (|l#TypeValueArray| ta) tv) (+ (|l#TypeValueArray| ta) 1)))
 :qid |verifycr.45:43|
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
 :qid |verifycr.104:36|
 :skolemid |2|
 :pattern ( (AddValueArray a v))
)))
(assert (forall ((a@@0 T@ValueArray) ) (! (= (RemoveValueArray a@@0) (ValueArray (store (|v#ValueArray| a@@0) (|l#ValueArray| a@@0) DefaultValue) (- (|l#ValueArray| a@@0) 1)))
 :qid |verifycr.108:39|
 :skolemid |3|
 :pattern ( (RemoveValueArray a@@0))
)))
(assert (forall ((a1 T@ValueArray) (a2 T@ValueArray) ) (! (= (ConcatValueArray a1 a2) (ValueArray (|lambda#0| (|l#ValueArray| a1) (|v#ValueArray| a1) (|v#ValueArray| a2) (|l#ValueArray| a1)) (+ (|l#ValueArray| a1) (|l#ValueArray| a2))))
 :qid |verifycr.111:39|
 :skolemid |4|
 :pattern ( (ConcatValueArray a1 a2))
)))
(assert (forall ((a@@1 T@ValueArray) ) (! (= (ReverseValueArray a@@1) (ValueArray (|lambda#1| 0 (|l#ValueArray| a@@1) (|v#ValueArray| a@@1) (|l#ValueArray| a@@1) 1 DefaultValue) (|l#ValueArray| a@@1)))
 :qid |verifycr.116:40|
 :skolemid |5|
 :pattern ( (ReverseValueArray a@@1))
)))
(assert (forall ((a@@2 T@ValueArray) (elem T@Value) ) (! (= (ExtendValueArray a@@2 elem) (ValueArray (store (|v#ValueArray| a@@2) (|l#ValueArray| a@@2) elem) (+ (|l#ValueArray| a@@2) 1)))
 :qid |verifycr.122:39|
 :skolemid |6|
 :pattern ( (ExtendValueArray a@@2 elem))
)))
(assert (forall ((a@@3 T@ValueArray) (i@@0 Int) (elem@@0 T@Value) ) (! (= (UpdateValueArray a@@3 i@@0 elem@@0) (ValueArray (store (|v#ValueArray| a@@3) i@@0 elem@@0) (|l#ValueArray| a@@3)))
 :qid |verifycr.125:39|
 :skolemid |7|
 :pattern ( (UpdateValueArray a@@3 i@@0 elem@@0))
)))
(assert (forall ((a@@4 T@ValueArray) (i@@1 Int) (j Int) ) (! (= (SwapValueArray a@@4 i@@1 j) (ValueArray (store (store (|v#ValueArray| a@@4) i@@1 (select (|v#ValueArray| a@@4) j)) j (select (|v#ValueArray| a@@4) i@@1)) (|l#ValueArray| a@@4)))
 :qid |verifycr.128:37|
 :skolemid |8|
 :pattern ( (SwapValueArray a@@4 i@@1 j))
)))
(assert (forall ((a@@5 T@ValueArray) ) (!  (and (=> (IsEmpty a@@5) (= (|l#ValueArray| a@@5) 0)) (=> (= (|l#ValueArray| a@@5) 0) (IsEmpty a@@5)))
 :qid |verifycr.131:30|
 :skolemid |9|
 :pattern ( (IsEmpty a@@5))
)))
(assert (= StratificationDepth 4))
(assert (forall ((v1 T@Value) (v2 T@Value) ) (!  (and (=> (IsEqual4 v1 v2) (= v1 v2)) (=> (= v1 v2) (IsEqual4 v1 v2)))
 :qid |verifycr.146:31|
 :skolemid |10|
 :pattern ( (IsEqual4 v1 v2))
)))
(assert (forall ((v1@@0 T@Value) (v2@@0 T@Value) ) (!  (and (=> (IsEqual3 v1@@0 v2@@0) (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@2) (select (vmap v2@@0) i@@2)))
 :qid |verifycr.154:14|
 :skolemid |11|
))))) (=> (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@3 Int) ) (!  (=> (and (<= 0 i@@3) (< i@@3 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@3) (select (vmap v2@@0) i@@3)))
 :qid |verifycr.154:14|
 :skolemid |11|
)))) (IsEqual3 v1@@0 v2@@0)))
 :qid |verifycr.149:31|
 :skolemid |12|
 :pattern ( (IsEqual3 v1@@0 v2@@0))
)))
(assert (forall ((v1@@1 T@Value) (v2@@1 T@Value) ) (!  (and (=> (IsEqual2 v1@@1 v2@@1) (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@4 Int) ) (!  (=> (and (<= 0 i@@4) (< i@@4 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@4) (select (vmap v2@@1) i@@4)))
 :qid |verifycr.161:14|
 :skolemid |13|
))))) (=> (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@5 Int) ) (!  (=> (and (<= 0 i@@5) (< i@@5 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@5) (select (vmap v2@@1) i@@5)))
 :qid |verifycr.161:14|
 :skolemid |13|
)))) (IsEqual2 v1@@1 v2@@1)))
 :qid |verifycr.156:31|
 :skolemid |14|
 :pattern ( (IsEqual2 v1@@1 v2@@1))
)))
(assert (forall ((v1@@2 T@Value) (v2@@2 T@Value) ) (!  (and (=> (IsEqual1 v1@@2 v2@@2) (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@6 Int) ) (!  (=> (and (<= 0 i@@6) (< i@@6 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@6) (select (vmap v2@@2) i@@6)))
 :qid |verifycr.168:14|
 :skolemid |15|
))))) (=> (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@7 Int) ) (!  (=> (and (<= 0 i@@7) (< i@@7 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@7) (select (vmap v2@@2) i@@7)))
 :qid |verifycr.168:14|
 :skolemid |15|
)))) (IsEqual1 v1@@2 v2@@2)))
 :qid |verifycr.163:31|
 :skolemid |16|
 :pattern ( (IsEqual1 v1@@2 v2@@2))
)))
(assert (forall ((v1@@3 T@Value) (v2@@3 T@Value) ) (!  (and (=> (IsEqual v1@@3 v2@@3) (IsEqual1 v1@@3 v2@@3)) (=> (IsEqual1 v1@@3 v2@@3) (IsEqual v1@@3 v2@@3)))
 :qid |verifycr.170:30|
 :skolemid |17|
 :pattern ( (IsEqual v1@@3 v2@@3))
)))
(assert (forall ((p@@0 T@Path) (v@@0 T@Value) ) (! (= (ReadValue4 p@@0 v@@0) v@@0)
 :qid |verifycr.174:33|
 :skolemid |18|
 :pattern ( (ReadValue4 p@@0 v@@0))
)))
(assert (forall ((p@@1 T@Path) (v@@1 T@Value) ) (! (= (ReadValue3 p@@1 v@@1) (ite (= 3 (|size#Path| p@@1)) v@@1 (ReadValue4 p@@1 (select (vmap v@@1) (path_index_at p@@1 3)))))
 :qid |verifycr.177:33|
 :skolemid |19|
 :pattern ( (ReadValue3 p@@1 v@@1))
)))
(assert (forall ((p@@2 T@Path) (v@@2 T@Value) ) (! (= (ReadValue2 p@@2 v@@2) (ite (= 2 (|size#Path| p@@2)) v@@2 (ReadValue3 p@@2 (select (vmap v@@2) (path_index_at p@@2 2)))))
 :qid |verifycr.183:33|
 :skolemid |20|
 :pattern ( (ReadValue2 p@@2 v@@2))
)))
(assert (forall ((p@@3 T@Path) (v@@3 T@Value) ) (! (= (ReadValue1 p@@3 v@@3) (ite (= 1 (|size#Path| p@@3)) v@@3 (ReadValue2 p@@3 (select (vmap v@@3) (path_index_at p@@3 1)))))
 :qid |verifycr.189:33|
 :skolemid |21|
 :pattern ( (ReadValue1 p@@3 v@@3))
)))
(assert (forall ((p@@4 T@Path) (v@@4 T@Value) ) (! (= (ReadValue0 p@@4 v@@4) (ite (= 0 (|size#Path| p@@4)) v@@4 (ReadValue1 p@@4 (select (vmap v@@4) (path_index_at p@@4 0)))))
 :qid |verifycr.195:33|
 :skolemid |22|
 :pattern ( (ReadValue0 p@@4 v@@4))
)))
(assert (forall ((p@@5 T@Path) (v@@5 T@Value) ) (! (= (ReadValue p@@5 v@@5) (ReadValue0 p@@5 v@@5))
 :qid |verifycr.201:32|
 :skolemid |23|
 :pattern ( (ReadValue p@@5 v@@5))
)))
(assert (forall ((p@@6 T@Path) (v@@6 T@Value) (new_v T@Value) ) (! (= (UpdateValue4 p@@6 v@@6 new_v) new_v)
 :qid |verifycr.205:35|
 :skolemid |24|
 :pattern ( (UpdateValue4 p@@6 v@@6 new_v))
)))
(assert (forall ((p@@7 T@Path) (v@@7 T@Value) (new_v@@0 T@Value) ) (! (= (UpdateValue3 p@@7 v@@7 new_v@@0) (ite (= 3 (|size#Path| p@@7)) new_v@@0 (update_vector v@@7 (path_index_at p@@7 3) (UpdateValue4 p@@7 (select (vmap v@@7) (path_index_at p@@7 3)) new_v@@0))))
 :qid |verifycr.208:35|
 :skolemid |25|
 :pattern ( (UpdateValue3 p@@7 v@@7 new_v@@0))
)))
(assert (forall ((p@@8 T@Path) (v@@8 T@Value) (new_v@@1 T@Value) ) (! (= (UpdateValue2 p@@8 v@@8 new_v@@1) (ite (= 2 (|size#Path| p@@8)) new_v@@1 (update_vector v@@8 (path_index_at p@@8 2) (UpdateValue3 p@@8 (select (vmap v@@8) (path_index_at p@@8 2)) new_v@@1))))
 :qid |verifycr.214:35|
 :skolemid |26|
 :pattern ( (UpdateValue2 p@@8 v@@8 new_v@@1))
)))
(assert (forall ((p@@9 T@Path) (v@@9 T@Value) (new_v@@2 T@Value) ) (! (= (UpdateValue1 p@@9 v@@9 new_v@@2) (ite (= 1 (|size#Path| p@@9)) new_v@@2 (update_vector v@@9 (path_index_at p@@9 1) (UpdateValue2 p@@9 (select (vmap v@@9) (path_index_at p@@9 1)) new_v@@2))))
 :qid |verifycr.220:35|
 :skolemid |27|
 :pattern ( (UpdateValue1 p@@9 v@@9 new_v@@2))
)))
(assert (forall ((p@@10 T@Path) (v@@10 T@Value) (new_v@@3 T@Value) ) (! (= (UpdateValue0 p@@10 v@@10 new_v@@3) (ite (= 0 (|size#Path| p@@10)) new_v@@3 (update_vector v@@10 (path_index_at p@@10 0) (UpdateValue1 p@@10 (select (vmap v@@10) (path_index_at p@@10 0)) new_v@@3))))
 :qid |verifycr.226:35|
 :skolemid |28|
 :pattern ( (UpdateValue0 p@@10 v@@10 new_v@@3))
)))
(assert (forall ((p@@11 T@Path) (v@@11 T@Value) (new_v@@4 T@Value) ) (! (= (UpdateValue p@@11 v@@11 new_v@@4) (UpdateValue0 p@@11 v@@11 new_v@@4))
 :qid |verifycr.232:34|
 :skolemid |29|
 :pattern ( (UpdateValue p@@11 v@@11 new_v@@4))
)))
(assert (forall ((v@@12 T@Value) ) (! (= (vmap v@@12) (|v#ValueArray| (|v#Vector| v@@12)))
 :qid |verifycr.239:27|
 :skolemid |30|
 :pattern ( (vmap v@@12))
)))
(assert (forall ((v@@13 T@Value) ) (! (= (vlen v@@13) (|l#ValueArray| (|v#Vector| v@@13)))
 :qid |verifycr.242:27|
 :skolemid |31|
 :pattern ( (vlen v@@13))
)))
(assert (= mk_vector (Vector EmptyValueArray)))
(assert (forall ((v@@14 T@Value) (elem@@1 T@Value) ) (! (= (push_back_vector v@@14 elem@@1) (Vector (AddValueArray (|v#Vector| v@@14) elem@@1)))
 :qid |verifycr.248:39|
 :skolemid |32|
 :pattern ( (push_back_vector v@@14 elem@@1))
)))
(assert (forall ((v@@15 T@Value) ) (! (= (pop_back_vector v@@15) (Vector (RemoveValueArray (|v#Vector| v@@15))))
 :qid |verifycr.251:38|
 :skolemid |33|
 :pattern ( (pop_back_vector v@@15))
)))
(assert (forall ((v1@@4 T@Value) (v2@@4 T@Value) ) (! (= (append_vector v1@@4 v2@@4) (Vector (ConcatValueArray (|v#Vector| v1@@4) (|v#Vector| v2@@4))))
 :qid |verifycr.254:36|
 :skolemid |34|
 :pattern ( (append_vector v1@@4 v2@@4))
)))
(assert (forall ((v@@16 T@Value) ) (! (= (reverse_vector v@@16) (Vector (ReverseValueArray (|v#Vector| v@@16))))
 :qid |verifycr.257:37|
 :skolemid |35|
 :pattern ( (reverse_vector v@@16))
)))
(assert (forall ((v@@17 T@Value) (i@@8 Int) (elem@@2 T@Value) ) (! (= (update_vector v@@17 i@@8 elem@@2) (Vector (UpdateValueArray (|v#Vector| v@@17) i@@8 elem@@2)))
 :qid |verifycr.260:36|
 :skolemid |36|
 :pattern ( (update_vector v@@17 i@@8 elem@@2))
)))
(assert (forall ((v@@18 T@Value) (i@@9 Int) (j@@0 Int) ) (! (= (swap_vector v@@18 i@@9 j@@0) (Vector (SwapValueArray (|v#Vector| v@@18) i@@9 j@@0)))
 :qid |verifycr.263:34|
 :skolemid |37|
 :pattern ( (swap_vector v@@18 i@@9 j@@0))
)))
(assert (= (|domain#Memory| EmptyMemory) ((as const (Array T@Location Bool)) false)))
(assert (= (|contents#Memory| EmptyMemory) ((as const (Array T@Location T@Value)) DefaultValue)))
(assert (forall ((m T@Memory) (idx Int) ) (! (= (GetLocal m idx) (select (|contents#Memory| m) (Local idx)))
 :qid |verifycr.316:31|
 :skolemid |38|
 :pattern ( (GetLocal m idx))
)))
(assert (forall ((m@@0 T@Memory) (idx@@0 Int) (v@@19 T@Value) ) (! (= (UpdateLocal m@@0 idx@@0 v@@19) (Memory (store (|domain#Memory| m@@0) (Local idx@@0) true) (store (|contents#Memory| m@@0) (Local idx@@0) v@@19)))
 :qid |verifycr.320:34|
 :skolemid |39|
 :pattern ( (UpdateLocal m@@0 idx@@0 v@@19))
)))
(assert (forall ((m@@1 T@Memory) (resource T@TypeValue) (addr Int) ) (!  (and (=> (ExistsResourceRaw m@@1 resource addr) (select (|domain#Memory| m@@1) (Global resource addr))) (=> (select (|domain#Memory| m@@1) (Global resource addr)) (ExistsResourceRaw m@@1 resource addr)))
 :qid |verifycr.335:40|
 :skolemid |40|
 :pattern ( (ExistsResourceRaw m@@1 resource addr))
)))
(assert (forall ((m@@2 T@Memory) (resource@@0 T@TypeValue) (addr@@0 Int) ) (! (= (ExistsResource m@@2 resource@@0 addr@@0) (Boolean (ExistsResourceRaw m@@2 resource@@0 addr@@0)))
 :qid |verifycr.338:37|
 :skolemid |41|
 :pattern ( (ExistsResource m@@2 resource@@0 addr@@0))
)))
(assert (forall ((resource@@1 T@TypeValue) (addr@@1 Int) ) (! (= (GetResourceReference resource@@1 addr@@1) (Reference (Global resource@@1 addr@@1) EmptyPath))
 :qid |verifycr.343:43|
 :skolemid |42|
 :pattern ( (GetResourceReference resource@@1 addr@@1))
)))
(assert (forall ((frame_idx Int) (idx@@1 Int) ) (! (= (GetLocalReference frame_idx idx@@1) (Reference (Local (+ frame_idx idx@@1)) EmptyPath))
 :qid |verifycr.348:40|
 :skolemid |43|
 :pattern ( (GetLocalReference frame_idx idx@@1))
)))
(assert (forall ((ref T@Reference) (field Int) ) (! (= (SelectFieldFromRef ref field) (Reference (|l#Reference| ref) (Path (store (|p#Path| (|p#Reference| ref)) (|size#Path| (|p#Reference| ref)) field) (+ (|size#Path| (|p#Reference| ref)) 1))))
 :qid |verifycr.353:41|
 :skolemid |44|
 :pattern ( (SelectFieldFromRef ref field))
)))
(assert (forall ((val T@Value) (field@@0 Int) ) (! (= (SelectField val field@@0) (select (vmap val) field@@0))
 :qid |verifycr.361:34|
 :skolemid |45|
 :pattern ( (SelectField val field@@0))
)))
(assert (forall ((m@@3 T@Memory) (ref@@0 T@Reference) ) (! (= (Dereference m@@3 ref@@0) (ReadValue (|p#Reference| ref@@0) (select (|contents#Memory| m@@3) (|l#Reference| ref@@0))))
 :qid |verifycr.366:34|
 :skolemid |46|
 :pattern ( (Dereference m@@3 ref@@0))
)))
(assert (forall ((m@@4 T@Memory) (txn T@Transaction) ) (!  (and (=> (ExistsTxnSenderAccount m@@4 txn) (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn)))) (=> (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn))) (ExistsTxnSenderAccount m@@4 txn)))
 :qid |verifycr.371:45|
 :skolemid |47|
 :pattern ( (ExistsTxnSenderAccount m@@4 txn))
)))
(assert (forall ((txn@@0 T@Transaction) ) (! (= (TxnSenderAddress txn@@0) (|sender#Transaction| txn@@0))
 :qid |verifycr.380:39|
 :skolemid |48|
 :pattern ( (TxnSenderAddress txn@@0))
)))
(assert (= TestSpecs_R_x 0))
(assert (= TestSpecs_R_type_value (StructType TestSpecs_R (ExtendTypeValueArray EmptyTypeValueArray IntegerType))))
(assert (forall ((i@@10 Int) (|l#0| Int) (|l#1| (Array Int T@Value)) (|l#2| (Array Int T@Value)) (|l#3| Int) ) (! (= (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10) (ite (< i@@10 |l#0|) (select |l#1| i@@10) (select |l#2| (- i@@10 |l#3|))))
 :qid |verifycr.113:17|
 :skolemid |49|
 :pattern ( (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10))
)))
(assert (forall ((i@@11 Int) (|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| (Array Int T@Value)) (|l#3@@0| Int) (|l#4| Int) (|l#5| T@Value) ) (! (= (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11) (ite  (and (<= |l#0@@0| i@@11) (< i@@11 |l#1@@0|)) (select |l#2@@0| (- (- |l#3@@0| i@@11) |l#4|)) |l#5|))
 :qid |verifycr.118:17|
 :skolemid |50|
 :pattern ( (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11))
)))
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun abort_flag@1 () Bool)
(declare-fun m@7 () T@Memory)
(declare-fun txn@@1 () T@Transaction)
(declare-fun %lbl%@2 () Bool)
(declare-fun m@@5 () T@Memory)
(declare-fun %lbl%@3 () Bool)
(declare-fun %lbl%+4 () Bool)
(declare-fun abort_flag@0 () Bool)
(declare-fun m@6 () T@Memory)
(declare-fun %lbl%+5 () Bool)
(declare-fun %lbl%+6 () Bool)
(declare-fun %lbl%+7 () Bool)
(declare-fun m@4 () T@Memory)
(declare-fun inline$MoveToSender$0$ta@0 () T@TypeValue)
(declare-fun inline$MoveToSender$0$a@1 () Int)
(declare-fun m@5 () T@Memory)
(declare-fun inline$MoveToSender$0$l@1 () T@Location)
(declare-fun inline$MoveToSender$0$v@0 () T@Value)
(declare-fun abort_flag () Bool)
(declare-fun %lbl%+8 () Bool)
(declare-fun %lbl%+9 () Bool)
(declare-fun %lbl%+10 () Bool)
(declare-fun local_counter () Int)
(declare-fun %lbl%+11 () Bool)
(declare-fun m@3 () T@Memory)
(declare-fun inline$Pack_TestSpecs_R$0$_struct@1 () T@Value)
(declare-fun %lbl%+12 () Bool)
(declare-fun inline$Pack_TestSpecs_R$0$x@0 () T@Value)
(declare-fun %lbl%+13 () Bool)
(declare-fun %lbl%+14 () Bool)
(declare-fun m@1 () T@Memory)
(declare-fun inline$LdConst$1$ret@1 () T@Value)
(declare-fun %lbl%+15 () Bool)
(declare-fun %lbl%+16 () Bool)
(declare-fun inline$TestSpecs_create_resource$0$tmp@1 () T@Value)
(declare-fun %lbl%+17 () Bool)
(declare-fun m@2 () T@Memory)
(declare-fun inline$LdConst$0$ret@1 () T@Value)
(declare-fun %lbl%+18 () Bool)
(declare-fun %lbl%+19 () Bool)
(declare-fun %lbl%+20 () Bool)
(declare-fun m@0 () T@Memory)
(declare-fun inline$Exists$0$dst@1 () T@Value)
(declare-fun %lbl%+21 () Bool)
(declare-fun inline$Exists$0$address@0 () T@Value)
(declare-fun inline$Exists$0$t@0 () T@TypeValue)
(declare-fun %lbl%+22 () Bool)
(declare-fun %lbl%+23 () Bool)
(declare-fun inline$GetTxnSenderAddress$0$ret_sender@1 () T@Value)
(declare-fun %lbl%+24 () Bool)
(declare-fun %lbl%+25 () Bool)
(declare-fun local_counter@0 () Int)
(declare-fun %lbl%+26 () Bool)
(declare-fun %lbl%@27 () Bool)
(declare-fun %lbl%+28 () Bool)
(declare-fun %lbl%+29 () Bool)
(push 1)
(set-info :boogie-vc-id TestSpecs_create_resource_verify)
(assert (not
(let ((inline$TestSpecs_create_resource$0$Return_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (and (! (or %lbl%@1  (=> (not abort_flag@1) (|b#Boolean| (ExistsResource m@7 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1))))))) :lblneg @1) (=> (=> (not abort_flag@1) (|b#Boolean| (ExistsResource m@7 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1)))))) (and (! (or %lbl%@2  (=> (not (|b#Boolean| (ExistsResource m@@5 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1)))))) (not abort_flag@1))) :lblneg @2) (=> (=> (not (|b#Boolean| (ExistsResource m@@5 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1)))))) (not abort_flag@1)) (! (or %lbl%@3  (=> (|b#Boolean| (ExistsResource m@@5 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1))))) abort_flag@1)) :lblneg @3))))))))
(let ((inline$TestSpecs_create_resource$0$anon6_Else_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (=> (and (and (not abort_flag@0) (= m@7 m@6)) (and (=> abort_flag@1 abort_flag@0) (=> abort_flag@0 abort_flag@1))) inline$TestSpecs_create_resource$0$Return_correct))))
(let ((inline$TestSpecs_create_resource$0$Label_Abort_correct  (=> (! (and %lbl%+5 true) :lblpos +5) (=> (= m@7 m@@5) (=> (and (=> abort_flag@1 true) (=> true abort_flag@1)) inline$TestSpecs_create_resource$0$Return_correct)))))
(let ((inline$TestSpecs_create_resource$0$anon6_Then_correct  (=> (! (and %lbl%+6 true) :lblpos +6) (=> abort_flag@0 inline$TestSpecs_create_resource$0$Label_Abort_correct))))
(let ((inline$MoveToSender$0$anon3_Else_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> (not (ExistsResourceRaw m@4 inline$MoveToSender$0$ta@0 inline$MoveToSender$0$a@1)) (=> (and (and (= m@5 (Memory (store (|domain#Memory| m@4) inline$MoveToSender$0$l@1 true) (store (|contents#Memory| m@4) inline$MoveToSender$0$l@1 inline$MoveToSender$0$v@0))) (= m@6 m@5)) (and (=> abort_flag@0 abort_flag) (=> abort_flag abort_flag@0))) (and inline$TestSpecs_create_resource$0$anon6_Then_correct inline$TestSpecs_create_resource$0$anon6_Else_correct))))))
(let ((inline$MoveToSender$0$anon3_Then_correct  (=> (! (and %lbl%+8 true) :lblpos +8) (=> (and (and (ExistsResourceRaw m@4 inline$MoveToSender$0$ta@0 inline$MoveToSender$0$a@1) (= m@6 m@4)) (and (=> abort_flag@0 true) (=> true abort_flag@0))) (and inline$TestSpecs_create_resource$0$anon6_Then_correct inline$TestSpecs_create_resource$0$anon6_Else_correct)))))
(let ((inline$MoveToSender$0$anon0_correct  (=> (! (and %lbl%+9 true) :lblpos +9) (=> (and (= inline$MoveToSender$0$a@1 (|sender#Transaction| txn@@1)) (= inline$MoveToSender$0$l@1 (Global inline$MoveToSender$0$ta@0 inline$MoveToSender$0$a@1))) (and inline$MoveToSender$0$anon3_Then_correct inline$MoveToSender$0$anon3_Else_correct)))))
(let ((inline$MoveToSender$0$Entry_correct  (=> (! (and %lbl%+10 true) :lblpos +10) (=> (and (= inline$MoveToSender$0$ta@0 TestSpecs_R_type_value) (= inline$MoveToSender$0$v@0 (GetLocal m@4 (+ local_counter 4)))) inline$MoveToSender$0$anon0_correct))))
(let ((inline$TestSpecs_create_resource$0$anon5_Then$2_correct  (=> (! (and %lbl%+11 true) :lblpos +11) (=> (= m@4 (UpdateLocal m@3 (+ local_counter 4) inline$Pack_TestSpecs_R$0$_struct@1)) inline$MoveToSender$0$Entry_correct))))
(let ((inline$Pack_TestSpecs_R$0$anon0_correct  (=> (! (and %lbl%+12 true) :lblpos +12) (=> (and (and (and (is-Integer inline$Pack_TestSpecs_R$0$x@0) (>= (|i#Integer| inline$Pack_TestSpecs_R$0$x@0) 0)) (<= (|i#Integer| inline$Pack_TestSpecs_R$0$x@0) MAX_U64)) (= inline$Pack_TestSpecs_R$0$_struct@1 (Vector (ExtendValueArray EmptyValueArray inline$Pack_TestSpecs_R$0$x@0)))) inline$TestSpecs_create_resource$0$anon5_Then$2_correct))))
(let ((inline$Pack_TestSpecs_R$0$Entry_correct  (=> (! (and %lbl%+13 true) :lblpos +13) (=> (= inline$Pack_TestSpecs_R$0$x@0 (GetLocal m@3 (+ local_counter 3))) inline$Pack_TestSpecs_R$0$anon0_correct))))
(let ((inline$TestSpecs_create_resource$0$anon5_Then$1_correct  (=> (! (and %lbl%+14 true) :lblpos +14) (=> (= m@3 (UpdateLocal m@1 (+ local_counter 3) inline$LdConst$1$ret@1)) inline$Pack_TestSpecs_R$0$Entry_correct))))
(let ((inline$LdConst$1$anon0_correct  (=> (! (and %lbl%+15 true) :lblpos +15) (=> (= inline$LdConst$1$ret@1 (Integer 1)) inline$TestSpecs_create_resource$0$anon5_Then$1_correct))))
(let ((inline$TestSpecs_create_resource$0$anon5_Then_correct  (=> (! (and %lbl%+16 true) :lblpos +16) (=> (not (|b#Boolean| inline$TestSpecs_create_resource$0$tmp@1)) inline$LdConst$1$anon0_correct))))
(let ((inline$TestSpecs_create_resource$0$anon5_Else$1_correct  (=> (! (and %lbl%+17 true) :lblpos +17) (=> (= m@2 (UpdateLocal m@1 (+ local_counter 2) inline$LdConst$0$ret@1)) inline$TestSpecs_create_resource$0$Label_Abort_correct))))
(let ((inline$LdConst$0$anon0_correct  (=> (! (and %lbl%+18 true) :lblpos +18) (=> (= inline$LdConst$0$ret@1 (Integer 1)) inline$TestSpecs_create_resource$0$anon5_Else$1_correct))))
(let ((inline$TestSpecs_create_resource$0$anon5_Else_correct  (=> (! (and %lbl%+19 true) :lblpos +19) (=> (|b#Boolean| inline$TestSpecs_create_resource$0$tmp@1) inline$LdConst$0$anon0_correct))))
(let ((inline$TestSpecs_create_resource$0$anon0$2_correct  (=> (! (and %lbl%+20 true) :lblpos +20) (=> (and (= m@1 (UpdateLocal m@0 (+ local_counter 1) inline$Exists$0$dst@1)) (= inline$TestSpecs_create_resource$0$tmp@1 (GetLocal m@1 (+ local_counter 1)))) (and inline$TestSpecs_create_resource$0$anon5_Then_correct inline$TestSpecs_create_resource$0$anon5_Else_correct)))))
(let ((inline$Exists$0$anon0_correct  (=> (! (and %lbl%+21 true) :lblpos +21) (=> (and (is-Address inline$Exists$0$address@0) (= inline$Exists$0$dst@1 (ExistsResource m@0 inline$Exists$0$t@0 (|a#Address| inline$Exists$0$address@0)))) inline$TestSpecs_create_resource$0$anon0$2_correct))))
(let ((inline$Exists$0$Entry_correct  (=> (! (and %lbl%+22 true) :lblpos +22) (=> (and (= inline$Exists$0$address@0 (GetLocal m@0 (+ local_counter 0))) (= inline$Exists$0$t@0 TestSpecs_R_type_value)) inline$Exists$0$anon0_correct))))
(let ((inline$TestSpecs_create_resource$0$anon0$1_correct  (=> (! (and %lbl%+23 true) :lblpos +23) (=> (= m@0 (UpdateLocal m@@5 (+ local_counter 0) inline$GetTxnSenderAddress$0$ret_sender@1)) inline$Exists$0$Entry_correct))))
(let ((inline$GetTxnSenderAddress$0$anon0_correct  (=> (! (and %lbl%+24 true) :lblpos +24) (=> (= inline$GetTxnSenderAddress$0$ret_sender@1 (Address (|sender#Transaction| txn@@1))) inline$TestSpecs_create_resource$0$anon0$1_correct))))
(let ((inline$TestSpecs_create_resource$0$anon0_correct  (=> (! (and %lbl%+25 true) :lblpos +25) (=> (and (not abort_flag) (= local_counter@0 (+ local_counter 5))) inline$GetTxnSenderAddress$0$anon0_correct))))
(let ((inline$TestSpecs_create_resource$0$Entry_correct  (=> (! (and %lbl%+26 true) :lblpos +26) (and (! (or %lbl%@27 (ExistsTxnSenderAccount m@@5 txn@@1)) :lblneg @27) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestSpecs_create_resource$0$anon0_correct)))))
(let ((anon0_correct  (=> (! (and %lbl%+28 true) :lblpos +28) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestSpecs_create_resource$0$Entry_correct))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+29 true) :lblpos +29) anon0_correct)))
PreconditionGeneratedEntry_correct))))))))))))))))))))))))))
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
(declare-fun TestSpecs_R_x () Int)
(declare-fun TestSpecs_R_type_value () T@TypeValue)
(declare-fun TestSpecs_R () T@TypeName)
(assert (= (|size#Path| EmptyPath) 0))
(assert (forall ((p T@Path) (i Int) ) (! (= (path_index_at p i) (select (|p#Path| p) i))
 :qid |verifycr.18:36|
 :skolemid |0|
 :pattern ( (path_index_at p i))
)))
(assert (= (|l#TypeValueArray| EmptyTypeValueArray) 0))
(assert (= (|v#TypeValueArray| EmptyTypeValueArray) ((as const (Array Int T@TypeValue)) DefaultTypeValue)))
(assert (forall ((ta T@TypeValueArray) (tv T@TypeValue) ) (! (= (ExtendTypeValueArray ta tv) (TypeValueArray (store (|v#TypeValueArray| ta) (|l#TypeValueArray| ta) tv) (+ (|l#TypeValueArray| ta) 1)))
 :qid |verifycr.45:43|
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
 :qid |verifycr.104:36|
 :skolemid |2|
 :pattern ( (AddValueArray a v))
)))
(assert (forall ((a@@0 T@ValueArray) ) (! (= (RemoveValueArray a@@0) (ValueArray (store (|v#ValueArray| a@@0) (|l#ValueArray| a@@0) DefaultValue) (- (|l#ValueArray| a@@0) 1)))
 :qid |verifycr.108:39|
 :skolemid |3|
 :pattern ( (RemoveValueArray a@@0))
)))
(assert (forall ((a1 T@ValueArray) (a2 T@ValueArray) ) (! (= (ConcatValueArray a1 a2) (ValueArray (|lambda#0| (|l#ValueArray| a1) (|v#ValueArray| a1) (|v#ValueArray| a2) (|l#ValueArray| a1)) (+ (|l#ValueArray| a1) (|l#ValueArray| a2))))
 :qid |verifycr.111:39|
 :skolemid |4|
 :pattern ( (ConcatValueArray a1 a2))
)))
(assert (forall ((a@@1 T@ValueArray) ) (! (= (ReverseValueArray a@@1) (ValueArray (|lambda#1| 0 (|l#ValueArray| a@@1) (|v#ValueArray| a@@1) (|l#ValueArray| a@@1) 1 DefaultValue) (|l#ValueArray| a@@1)))
 :qid |verifycr.116:40|
 :skolemid |5|
 :pattern ( (ReverseValueArray a@@1))
)))
(assert (forall ((a@@2 T@ValueArray) (elem T@Value) ) (! (= (ExtendValueArray a@@2 elem) (ValueArray (store (|v#ValueArray| a@@2) (|l#ValueArray| a@@2) elem) (+ (|l#ValueArray| a@@2) 1)))
 :qid |verifycr.122:39|
 :skolemid |6|
 :pattern ( (ExtendValueArray a@@2 elem))
)))
(assert (forall ((a@@3 T@ValueArray) (i@@0 Int) (elem@@0 T@Value) ) (! (= (UpdateValueArray a@@3 i@@0 elem@@0) (ValueArray (store (|v#ValueArray| a@@3) i@@0 elem@@0) (|l#ValueArray| a@@3)))
 :qid |verifycr.125:39|
 :skolemid |7|
 :pattern ( (UpdateValueArray a@@3 i@@0 elem@@0))
)))
(assert (forall ((a@@4 T@ValueArray) (i@@1 Int) (j Int) ) (! (= (SwapValueArray a@@4 i@@1 j) (ValueArray (store (store (|v#ValueArray| a@@4) i@@1 (select (|v#ValueArray| a@@4) j)) j (select (|v#ValueArray| a@@4) i@@1)) (|l#ValueArray| a@@4)))
 :qid |verifycr.128:37|
 :skolemid |8|
 :pattern ( (SwapValueArray a@@4 i@@1 j))
)))
(assert (forall ((a@@5 T@ValueArray) ) (!  (and (=> (IsEmpty a@@5) (= (|l#ValueArray| a@@5) 0)) (=> (= (|l#ValueArray| a@@5) 0) (IsEmpty a@@5)))
 :qid |verifycr.131:30|
 :skolemid |9|
 :pattern ( (IsEmpty a@@5))
)))
(assert (= StratificationDepth 4))
(assert (forall ((v1 T@Value) (v2 T@Value) ) (!  (and (=> (IsEqual4 v1 v2) (= v1 v2)) (=> (= v1 v2) (IsEqual4 v1 v2)))
 :qid |verifycr.146:31|
 :skolemid |10|
 :pattern ( (IsEqual4 v1 v2))
)))
(assert (forall ((v1@@0 T@Value) (v2@@0 T@Value) ) (!  (and (=> (IsEqual3 v1@@0 v2@@0) (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@2) (select (vmap v2@@0) i@@2)))
 :qid |verifycr.154:14|
 :skolemid |11|
))))) (=> (or (= v1@@0 v2@@0) (and (and (and (is-Vector v1@@0) (is-Vector v2@@0)) (= (vlen v1@@0) (vlen v2@@0))) (forall ((i@@3 Int) ) (!  (=> (and (<= 0 i@@3) (< i@@3 (vlen v1@@0))) (IsEqual4 (select (vmap v1@@0) i@@3) (select (vmap v2@@0) i@@3)))
 :qid |verifycr.154:14|
 :skolemid |11|
)))) (IsEqual3 v1@@0 v2@@0)))
 :qid |verifycr.149:31|
 :skolemid |12|
 :pattern ( (IsEqual3 v1@@0 v2@@0))
)))
(assert (forall ((v1@@1 T@Value) (v2@@1 T@Value) ) (!  (and (=> (IsEqual2 v1@@1 v2@@1) (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@4 Int) ) (!  (=> (and (<= 0 i@@4) (< i@@4 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@4) (select (vmap v2@@1) i@@4)))
 :qid |verifycr.161:14|
 :skolemid |13|
))))) (=> (or (= v1@@1 v2@@1) (and (and (and (is-Vector v1@@1) (is-Vector v2@@1)) (= (vlen v1@@1) (vlen v2@@1))) (forall ((i@@5 Int) ) (!  (=> (and (<= 0 i@@5) (< i@@5 (vlen v1@@1))) (IsEqual3 (select (vmap v1@@1) i@@5) (select (vmap v2@@1) i@@5)))
 :qid |verifycr.161:14|
 :skolemid |13|
)))) (IsEqual2 v1@@1 v2@@1)))
 :qid |verifycr.156:31|
 :skolemid |14|
 :pattern ( (IsEqual2 v1@@1 v2@@1))
)))
(assert (forall ((v1@@2 T@Value) (v2@@2 T@Value) ) (!  (and (=> (IsEqual1 v1@@2 v2@@2) (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@6 Int) ) (!  (=> (and (<= 0 i@@6) (< i@@6 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@6) (select (vmap v2@@2) i@@6)))
 :qid |verifycr.168:14|
 :skolemid |15|
))))) (=> (or (= v1@@2 v2@@2) (and (and (and (is-Vector v1@@2) (is-Vector v2@@2)) (= (vlen v1@@2) (vlen v2@@2))) (forall ((i@@7 Int) ) (!  (=> (and (<= 0 i@@7) (< i@@7 (vlen v1@@2))) (IsEqual2 (select (vmap v1@@2) i@@7) (select (vmap v2@@2) i@@7)))
 :qid |verifycr.168:14|
 :skolemid |15|
)))) (IsEqual1 v1@@2 v2@@2)))
 :qid |verifycr.163:31|
 :skolemid |16|
 :pattern ( (IsEqual1 v1@@2 v2@@2))
)))
(assert (forall ((v1@@3 T@Value) (v2@@3 T@Value) ) (!  (and (=> (IsEqual v1@@3 v2@@3) (IsEqual1 v1@@3 v2@@3)) (=> (IsEqual1 v1@@3 v2@@3) (IsEqual v1@@3 v2@@3)))
 :qid |verifycr.170:30|
 :skolemid |17|
 :pattern ( (IsEqual v1@@3 v2@@3))
)))
(assert (forall ((p@@0 T@Path) (v@@0 T@Value) ) (! (= (ReadValue4 p@@0 v@@0) v@@0)
 :qid |verifycr.174:33|
 :skolemid |18|
 :pattern ( (ReadValue4 p@@0 v@@0))
)))
(assert (forall ((p@@1 T@Path) (v@@1 T@Value) ) (! (= (ReadValue3 p@@1 v@@1) (ite (= 3 (|size#Path| p@@1)) v@@1 (ReadValue4 p@@1 (select (vmap v@@1) (path_index_at p@@1 3)))))
 :qid |verifycr.177:33|
 :skolemid |19|
 :pattern ( (ReadValue3 p@@1 v@@1))
)))
(assert (forall ((p@@2 T@Path) (v@@2 T@Value) ) (! (= (ReadValue2 p@@2 v@@2) (ite (= 2 (|size#Path| p@@2)) v@@2 (ReadValue3 p@@2 (select (vmap v@@2) (path_index_at p@@2 2)))))
 :qid |verifycr.183:33|
 :skolemid |20|
 :pattern ( (ReadValue2 p@@2 v@@2))
)))
(assert (forall ((p@@3 T@Path) (v@@3 T@Value) ) (! (= (ReadValue1 p@@3 v@@3) (ite (= 1 (|size#Path| p@@3)) v@@3 (ReadValue2 p@@3 (select (vmap v@@3) (path_index_at p@@3 1)))))
 :qid |verifycr.189:33|
 :skolemid |21|
 :pattern ( (ReadValue1 p@@3 v@@3))
)))
(assert (forall ((p@@4 T@Path) (v@@4 T@Value) ) (! (= (ReadValue0 p@@4 v@@4) (ite (= 0 (|size#Path| p@@4)) v@@4 (ReadValue1 p@@4 (select (vmap v@@4) (path_index_at p@@4 0)))))
 :qid |verifycr.195:33|
 :skolemid |22|
 :pattern ( (ReadValue0 p@@4 v@@4))
)))
(assert (forall ((p@@5 T@Path) (v@@5 T@Value) ) (! (= (ReadValue p@@5 v@@5) (ReadValue0 p@@5 v@@5))
 :qid |verifycr.201:32|
 :skolemid |23|
 :pattern ( (ReadValue p@@5 v@@5))
)))
(assert (forall ((p@@6 T@Path) (v@@6 T@Value) (new_v T@Value) ) (! (= (UpdateValue4 p@@6 v@@6 new_v) new_v)
 :qid |verifycr.205:35|
 :skolemid |24|
 :pattern ( (UpdateValue4 p@@6 v@@6 new_v))
)))
(assert (forall ((p@@7 T@Path) (v@@7 T@Value) (new_v@@0 T@Value) ) (! (= (UpdateValue3 p@@7 v@@7 new_v@@0) (ite (= 3 (|size#Path| p@@7)) new_v@@0 (update_vector v@@7 (path_index_at p@@7 3) (UpdateValue4 p@@7 (select (vmap v@@7) (path_index_at p@@7 3)) new_v@@0))))
 :qid |verifycr.208:35|
 :skolemid |25|
 :pattern ( (UpdateValue3 p@@7 v@@7 new_v@@0))
)))
(assert (forall ((p@@8 T@Path) (v@@8 T@Value) (new_v@@1 T@Value) ) (! (= (UpdateValue2 p@@8 v@@8 new_v@@1) (ite (= 2 (|size#Path| p@@8)) new_v@@1 (update_vector v@@8 (path_index_at p@@8 2) (UpdateValue3 p@@8 (select (vmap v@@8) (path_index_at p@@8 2)) new_v@@1))))
 :qid |verifycr.214:35|
 :skolemid |26|
 :pattern ( (UpdateValue2 p@@8 v@@8 new_v@@1))
)))
(assert (forall ((p@@9 T@Path) (v@@9 T@Value) (new_v@@2 T@Value) ) (! (= (UpdateValue1 p@@9 v@@9 new_v@@2) (ite (= 1 (|size#Path| p@@9)) new_v@@2 (update_vector v@@9 (path_index_at p@@9 1) (UpdateValue2 p@@9 (select (vmap v@@9) (path_index_at p@@9 1)) new_v@@2))))
 :qid |verifycr.220:35|
 :skolemid |27|
 :pattern ( (UpdateValue1 p@@9 v@@9 new_v@@2))
)))
(assert (forall ((p@@10 T@Path) (v@@10 T@Value) (new_v@@3 T@Value) ) (! (= (UpdateValue0 p@@10 v@@10 new_v@@3) (ite (= 0 (|size#Path| p@@10)) new_v@@3 (update_vector v@@10 (path_index_at p@@10 0) (UpdateValue1 p@@10 (select (vmap v@@10) (path_index_at p@@10 0)) new_v@@3))))
 :qid |verifycr.226:35|
 :skolemid |28|
 :pattern ( (UpdateValue0 p@@10 v@@10 new_v@@3))
)))
(assert (forall ((p@@11 T@Path) (v@@11 T@Value) (new_v@@4 T@Value) ) (! (= (UpdateValue p@@11 v@@11 new_v@@4) (UpdateValue0 p@@11 v@@11 new_v@@4))
 :qid |verifycr.232:34|
 :skolemid |29|
 :pattern ( (UpdateValue p@@11 v@@11 new_v@@4))
)))
(assert (forall ((v@@12 T@Value) ) (! (= (vmap v@@12) (|v#ValueArray| (|v#Vector| v@@12)))
 :qid |verifycr.239:27|
 :skolemid |30|
 :pattern ( (vmap v@@12))
)))
(assert (forall ((v@@13 T@Value) ) (! (= (vlen v@@13) (|l#ValueArray| (|v#Vector| v@@13)))
 :qid |verifycr.242:27|
 :skolemid |31|
 :pattern ( (vlen v@@13))
)))
(assert (= mk_vector (Vector EmptyValueArray)))
(assert (forall ((v@@14 T@Value) (elem@@1 T@Value) ) (! (= (push_back_vector v@@14 elem@@1) (Vector (AddValueArray (|v#Vector| v@@14) elem@@1)))
 :qid |verifycr.248:39|
 :skolemid |32|
 :pattern ( (push_back_vector v@@14 elem@@1))
)))
(assert (forall ((v@@15 T@Value) ) (! (= (pop_back_vector v@@15) (Vector (RemoveValueArray (|v#Vector| v@@15))))
 :qid |verifycr.251:38|
 :skolemid |33|
 :pattern ( (pop_back_vector v@@15))
)))
(assert (forall ((v1@@4 T@Value) (v2@@4 T@Value) ) (! (= (append_vector v1@@4 v2@@4) (Vector (ConcatValueArray (|v#Vector| v1@@4) (|v#Vector| v2@@4))))
 :qid |verifycr.254:36|
 :skolemid |34|
 :pattern ( (append_vector v1@@4 v2@@4))
)))
(assert (forall ((v@@16 T@Value) ) (! (= (reverse_vector v@@16) (Vector (ReverseValueArray (|v#Vector| v@@16))))
 :qid |verifycr.257:37|
 :skolemid |35|
 :pattern ( (reverse_vector v@@16))
)))
(assert (forall ((v@@17 T@Value) (i@@8 Int) (elem@@2 T@Value) ) (! (= (update_vector v@@17 i@@8 elem@@2) (Vector (UpdateValueArray (|v#Vector| v@@17) i@@8 elem@@2)))
 :qid |verifycr.260:36|
 :skolemid |36|
 :pattern ( (update_vector v@@17 i@@8 elem@@2))
)))
(assert (forall ((v@@18 T@Value) (i@@9 Int) (j@@0 Int) ) (! (= (swap_vector v@@18 i@@9 j@@0) (Vector (SwapValueArray (|v#Vector| v@@18) i@@9 j@@0)))
 :qid |verifycr.263:34|
 :skolemid |37|
 :pattern ( (swap_vector v@@18 i@@9 j@@0))
)))
(assert (= (|domain#Memory| EmptyMemory) ((as const (Array T@Location Bool)) false)))
(assert (= (|contents#Memory| EmptyMemory) ((as const (Array T@Location T@Value)) DefaultValue)))
(assert (forall ((m T@Memory) (idx Int) ) (! (= (GetLocal m idx) (select (|contents#Memory| m) (Local idx)))
 :qid |verifycr.316:31|
 :skolemid |38|
 :pattern ( (GetLocal m idx))
)))
(assert (forall ((m@@0 T@Memory) (idx@@0 Int) (v@@19 T@Value) ) (! (= (UpdateLocal m@@0 idx@@0 v@@19) (Memory (store (|domain#Memory| m@@0) (Local idx@@0) true) (store (|contents#Memory| m@@0) (Local idx@@0) v@@19)))
 :qid |verifycr.320:34|
 :skolemid |39|
 :pattern ( (UpdateLocal m@@0 idx@@0 v@@19))
)))
(assert (forall ((m@@1 T@Memory) (resource T@TypeValue) (addr Int) ) (!  (and (=> (ExistsResourceRaw m@@1 resource addr) (select (|domain#Memory| m@@1) (Global resource addr))) (=> (select (|domain#Memory| m@@1) (Global resource addr)) (ExistsResourceRaw m@@1 resource addr)))
 :qid |verifycr.335:40|
 :skolemid |40|
 :pattern ( (ExistsResourceRaw m@@1 resource addr))
)))
(assert (forall ((m@@2 T@Memory) (resource@@0 T@TypeValue) (addr@@0 Int) ) (! (= (ExistsResource m@@2 resource@@0 addr@@0) (Boolean (ExistsResourceRaw m@@2 resource@@0 addr@@0)))
 :qid |verifycr.338:37|
 :skolemid |41|
 :pattern ( (ExistsResource m@@2 resource@@0 addr@@0))
)))
(assert (forall ((resource@@1 T@TypeValue) (addr@@1 Int) ) (! (= (GetResourceReference resource@@1 addr@@1) (Reference (Global resource@@1 addr@@1) EmptyPath))
 :qid |verifycr.343:43|
 :skolemid |42|
 :pattern ( (GetResourceReference resource@@1 addr@@1))
)))
(assert (forall ((frame_idx Int) (idx@@1 Int) ) (! (= (GetLocalReference frame_idx idx@@1) (Reference (Local (+ frame_idx idx@@1)) EmptyPath))
 :qid |verifycr.348:40|
 :skolemid |43|
 :pattern ( (GetLocalReference frame_idx idx@@1))
)))
(assert (forall ((ref T@Reference) (field Int) ) (! (= (SelectFieldFromRef ref field) (Reference (|l#Reference| ref) (Path (store (|p#Path| (|p#Reference| ref)) (|size#Path| (|p#Reference| ref)) field) (+ (|size#Path| (|p#Reference| ref)) 1))))
 :qid |verifycr.353:41|
 :skolemid |44|
 :pattern ( (SelectFieldFromRef ref field))
)))
(assert (forall ((val T@Value) (field@@0 Int) ) (! (= (SelectField val field@@0) (select (vmap val) field@@0))
 :qid |verifycr.361:34|
 :skolemid |45|
 :pattern ( (SelectField val field@@0))
)))
(assert (forall ((m@@3 T@Memory) (ref@@0 T@Reference) ) (! (= (Dereference m@@3 ref@@0) (ReadValue (|p#Reference| ref@@0) (select (|contents#Memory| m@@3) (|l#Reference| ref@@0))))
 :qid |verifycr.366:34|
 :skolemid |46|
 :pattern ( (Dereference m@@3 ref@@0))
)))
(assert (forall ((m@@4 T@Memory) (txn T@Transaction) ) (!  (and (=> (ExistsTxnSenderAccount m@@4 txn) (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn)))) (=> (select (|domain#Memory| m@@4) (Global LibraAccount_T_type_value (|sender#Transaction| txn))) (ExistsTxnSenderAccount m@@4 txn)))
 :qid |verifycr.371:45|
 :skolemid |47|
 :pattern ( (ExistsTxnSenderAccount m@@4 txn))
)))
(assert (forall ((txn@@0 T@Transaction) ) (! (= (TxnSenderAddress txn@@0) (|sender#Transaction| txn@@0))
 :qid |verifycr.380:39|
 :skolemid |48|
 :pattern ( (TxnSenderAddress txn@@0))
)))
(assert (= TestSpecs_R_x 0))
(assert (= TestSpecs_R_type_value (StructType TestSpecs_R (ExtendTypeValueArray EmptyTypeValueArray IntegerType))))
(assert (forall ((i@@10 Int) (|l#0| Int) (|l#1| (Array Int T@Value)) (|l#2| (Array Int T@Value)) (|l#3| Int) ) (! (= (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10) (ite (< i@@10 |l#0|) (select |l#1| i@@10) (select |l#2| (- i@@10 |l#3|))))
 :qid |verifycr.113:17|
 :skolemid |49|
 :pattern ( (select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) i@@10))
)))
(assert (forall ((i@@11 Int) (|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| (Array Int T@Value)) (|l#3@@0| Int) (|l#4| Int) (|l#5| T@Value) ) (! (= (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11) (ite  (and (<= |l#0@@0| i@@11) (< i@@11 |l#1@@0|)) (select |l#2@@0| (- (- |l#3@@0| i@@11) |l#4|)) |l#5|))
 :qid |verifycr.118:17|
 :skolemid |50|
 :pattern ( (select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4| |l#5|) i@@11))
)))
; Valid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun abort_flag@0 () Bool)
(declare-fun m@3 () T@Memory)
(declare-fun txn@@1 () T@Transaction)
(declare-fun %lbl%@2 () Bool)
(declare-fun m@@5 () T@Memory)
(declare-fun %lbl%@3 () Bool)
(declare-fun %lbl%+4 () Bool)
(declare-fun m@2 () T@Memory)
(declare-fun m@1 () T@Memory)
(declare-fun local_counter () Int)
(declare-fun inline$LdConst$0$ret@1 () T@Value)
(declare-fun %lbl%+5 () Bool)
(declare-fun %lbl%+6 () Bool)
(declare-fun inline$TestSpecs_create_resource_error$0$tmp@1 () T@Value)
(declare-fun %lbl%+7 () Bool)
(declare-fun abort_flag () Bool)
(declare-fun %lbl%+8 () Bool)
(declare-fun m@0 () T@Memory)
(declare-fun inline$Exists$0$dst@1 () T@Value)
(declare-fun %lbl%+9 () Bool)
(declare-fun inline$Exists$0$address@0 () T@Value)
(declare-fun inline$Exists$0$t@0 () T@TypeValue)
(declare-fun %lbl%+10 () Bool)
(declare-fun %lbl%+11 () Bool)
(declare-fun inline$GetTxnSenderAddress$0$ret_sender@1 () T@Value)
(declare-fun %lbl%+12 () Bool)
(declare-fun %lbl%+13 () Bool)
(declare-fun local_counter@0 () Int)
(declare-fun %lbl%+14 () Bool)
(declare-fun %lbl%@15 () Bool)
(declare-fun %lbl%+16 () Bool)
(declare-fun %lbl%+17 () Bool)
(push 1)
(set-info :boogie-vc-id TestSpecs_create_resource_error_verify)
(assert (not
(let ((inline$TestSpecs_create_resource_error$0$Return_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (and (! (or %lbl%@1  (=> (not abort_flag@0) (|b#Boolean| (ExistsResource m@3 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1))))))) :lblneg @1) (=> (=> (not abort_flag@0) (|b#Boolean| (ExistsResource m@3 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1)))))) (and (! (or %lbl%@2  (=> (not (|b#Boolean| (ExistsResource m@@5 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1)))))) (not abort_flag@0))) :lblneg @2) (=> (=> (not (|b#Boolean| (ExistsResource m@@5 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1)))))) (not abort_flag@0)) (! (or %lbl%@3  (=> (|b#Boolean| (ExistsResource m@@5 TestSpecs_R_type_value (|a#Address| (Address (TxnSenderAddress txn@@1))))) abort_flag@0)) :lblneg @3))))))))
(let ((inline$TestSpecs_create_resource_error$0$anon3_Else$1_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (=> (= m@2 (UpdateLocal m@1 (+ local_counter 2) inline$LdConst$0$ret@1)) (=> (and (and (=> abort_flag@0 true) (=> true abort_flag@0)) (= m@3 m@@5)) inline$TestSpecs_create_resource_error$0$Return_correct)))))
(let ((inline$LdConst$0$anon0_correct  (=> (! (and %lbl%+5 true) :lblpos +5) (=> (= inline$LdConst$0$ret@1 (Integer 1)) inline$TestSpecs_create_resource_error$0$anon3_Else$1_correct))))
(let ((inline$TestSpecs_create_resource_error$0$anon3_Else_correct  (=> (! (and %lbl%+6 true) :lblpos +6) (=> (|b#Boolean| inline$TestSpecs_create_resource_error$0$tmp@1) inline$LdConst$0$anon0_correct))))
(let ((inline$TestSpecs_create_resource_error$0$anon3_Then_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> (not (|b#Boolean| inline$TestSpecs_create_resource_error$0$tmp@1)) (=> (and (and (=> abort_flag@0 abort_flag) (=> abort_flag abort_flag@0)) (= m@3 m@1)) inline$TestSpecs_create_resource_error$0$Return_correct)))))
(let ((inline$TestSpecs_create_resource_error$0$anon0$2_correct  (=> (! (and %lbl%+8 true) :lblpos +8) (=> (and (= m@1 (UpdateLocal m@0 (+ local_counter 1) inline$Exists$0$dst@1)) (= inline$TestSpecs_create_resource_error$0$tmp@1 (GetLocal m@1 (+ local_counter 1)))) (and inline$TestSpecs_create_resource_error$0$anon3_Then_correct inline$TestSpecs_create_resource_error$0$anon3_Else_correct)))))
(let ((inline$Exists$0$anon0_correct  (=> (! (and %lbl%+9 true) :lblpos +9) (=> (and (is-Address inline$Exists$0$address@0) (= inline$Exists$0$dst@1 (ExistsResource m@0 inline$Exists$0$t@0 (|a#Address| inline$Exists$0$address@0)))) inline$TestSpecs_create_resource_error$0$anon0$2_correct))))
(let ((inline$Exists$0$Entry_correct  (=> (! (and %lbl%+10 true) :lblpos +10) (=> (and (= inline$Exists$0$address@0 (GetLocal m@0 (+ local_counter 0))) (= inline$Exists$0$t@0 TestSpecs_R_type_value)) inline$Exists$0$anon0_correct))))
(let ((inline$TestSpecs_create_resource_error$0$anon0$1_correct  (=> (! (and %lbl%+11 true) :lblpos +11) (=> (= m@0 (UpdateLocal m@@5 (+ local_counter 0) inline$GetTxnSenderAddress$0$ret_sender@1)) inline$Exists$0$Entry_correct))))
(let ((inline$GetTxnSenderAddress$0$anon0_correct  (=> (! (and %lbl%+12 true) :lblpos +12) (=> (= inline$GetTxnSenderAddress$0$ret_sender@1 (Address (|sender#Transaction| txn@@1))) inline$TestSpecs_create_resource_error$0$anon0$1_correct))))
(let ((inline$TestSpecs_create_resource_error$0$anon0_correct  (=> (! (and %lbl%+13 true) :lblpos +13) (=> (and (not abort_flag) (= local_counter@0 (+ local_counter 3))) inline$GetTxnSenderAddress$0$anon0_correct))))
(let ((inline$TestSpecs_create_resource_error$0$Entry_correct  (=> (! (and %lbl%+14 true) :lblpos +14) (and (! (or %lbl%@15 (ExistsTxnSenderAccount m@@5 txn@@1)) :lblneg @15) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestSpecs_create_resource_error$0$anon0_correct)))))
(let ((anon0_correct  (=> (! (and %lbl%+16 true) :lblpos +16) (=> (ExistsTxnSenderAccount m@@5 txn@@1) inline$TestSpecs_create_resource_error$0$Entry_correct))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+17 true) :lblpos +17) anon0_correct)))
PreconditionGeneratedEntry_correct))))))))))))))
))
(check-sat)
(get-info :reason-unknown)
(labels)
(assert %lbl%@1)
(check-sat)
(pop 1)
; Invalid
