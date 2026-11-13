theory Wasm imports Wasm_Base_Defs begin

inductive b_e_typing :: "[t_context, b_e list, tf] \<Rightarrow> bool" ("_ \<turnstile> _ : _" 60) where
  const_num:"\<C> \<turnstile> [EConstNum v] :([] _> [T_num (typeof_num v)])"
| const_vec:"\<C> \<turnstile> [EConstVec v] :([] _> [T_vec (typeof_vec v)])"
| unop:"unop_t_num_agree op t   \<Longrightarrow> \<C> \<turnstile> [Unop t op]  : ([T_num t]   _> [T_num t])"
| binop:"binop_t_num_agree op t \<Longrightarrow> \<C> \<turnstile> [Binop t op] : ([T_num t,T_num t] _> [T_num t])"
| testop:"is_int_t_num t   \<Longrightarrow> \<C> \<turnstile> [Testop t _]      : ([T_num t]   _> [T_num T_i32])"
| relop:"relop_t_num_agree op t   \<Longrightarrow> \<C> \<turnstile> [Relop t op] : ([T_num t,T_num t] _> [T_num T_i32])"
| ref_null:"\<C> \<turnstile> [Ref_null t] :([] _> [T_ref t])"
| ref_is_null:"\<C> \<turnstile> [Ref_is_null] :([T_ref t] _> [T_num T_i32])"
| ref_func:"\<lbrakk>j < length (func_t \<C>); j \<in> set (refs \<C>)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Ref_func j] :([] _> [T_ref T_func_ref])"
| unop_vec:"\<C> \<turnstile> [Unop_vec op]  : ([T_vec T_v128]   _> [T_vec T_v128])"
| binop_vec:"\<lbrakk>binop_vec_wf op\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Binop_vec op]  : ([T_vec T_v128, T_vec T_v128]   _> [T_vec T_v128])"
| ternop_vec:"\<C> \<turnstile> [Ternop_vec op]  : ([T_vec T_v128, T_vec T_v128, T_vec T_v128]   _> [T_vec T_v128])"
| test_vec:"\<C> \<turnstile> [Test_vec op]  : ([T_vec T_v128]   _> [T_num T_i32])"
| shift_vec:"\<C> \<turnstile> [Shift_vec op]  : ([T_vec T_v128, T_num T_i32]   _> [T_vec T_v128])"
| splat_vec:"\<C> \<turnstile> [Splat_vec sv]  : ([T_num (vec_lane_t sv)]   _> [T_vec T_v128])"
| extract_vec:"\<lbrakk>i < vec_num sv; sx = U \<or> vec_length sv \<le> 2\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Extract_vec sv sx i]  : ([T_vec T_v128]   _> [T_num (vec_lane_t sv)])"
| replace_vec:"i < vec_num sv \<Longrightarrow> \<C> \<turnstile> [Replace_vec sv i]  : ([T_vec T_v128, T_num (vec_lane_t sv)]   _> [T_vec T_v128])"
| convert:"\<lbrakk>(t1 \<noteq> t2); (sat_sx = None) = ((is_float_t_num t1 \<and> is_float_t_num t2) \<or> (is_int_t_num t1 \<and> is_int_t_num t2 \<and> (t_num_length t1 < t_num_length t2)))\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Cvtop t1 Convert t2 sat_sx] : ([T_num t2] _> [T_num t1])"
| reinterpret:"\<lbrakk>(t1 \<noteq> t2); t_num_length t1 = t_num_length t2\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Cvtop t1 Reinterpret t2 None] : ([T_num t2] _> [T_num t1])"
| unreachable:"\<C> \<turnstile> [Unreachable] : (ts _> ts')"
| nop:"\<C> \<turnstile> [Nop] : ([] _> [])"
| drop:"\<C> \<turnstile> [Drop] : ([t] _> [])"
| select:"(t_tag = None \<and> (is_num_type t \<or> is_vec_type t \<or> t = T_bot)) \<or> t_tag = Some t \<Longrightarrow> \<C> \<turnstile> [Select t_tag] : ([t,t,T_num T_i32] _> [t])"
| block:"\<lbrakk>tb_tf_t \<C> tb = Some (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Block tb es] : (tn _> tm)"
| loop:"\<lbrakk>tb_tf_t \<C> tb = Some (tn _> tm); \<C>\<lparr>label := ([tn] @ (label \<C>))\<rparr> \<turnstile> es : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Loop tb es] : (tn _> tm)"
| if_wasm:"\<lbrakk>tb_tf_t \<C> tb = Some (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es1 : (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es2 : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [If tb es1 es2] : (tn @ [T_num T_i32] _> tm)"
| br:"\<lbrakk>i < length(label \<C>); (label \<C>)!i = ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br i] : (t1s @ ts _> t2s)"
| br_if:"\<lbrakk>i < length(label \<C>); (label \<C>)!i = ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br_if i] : (ts @ [T_num T_i32] _> ts)"
| br_table:"\<lbrakk>list_all (\<lambda>i. i < length(label \<C>) \<and> ts <ts: (label \<C>)!i) (is@[i])\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br_table is i] : (t1s @ ts @ [T_num T_i32] _> t2s)"
| return:"\<lbrakk>(return \<C>) = Some ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Return] : (t1s @ ts _> t2s)"
| call:"\<lbrakk>i < length(func_t \<C>); (func_t \<C>)!i = tf\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Call i] : tf"
| call_indirect:"\<lbrakk>i < length(types_t \<C>); (types_t \<C>)!i = (t1s _> t2s); ti < length (table \<C>); (table \<C>)!ti = T_tab _  T_func_ref\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Call_indirect ti i] : (t1s @ [T_num T_i32] _> t2s)"
| local_get:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Local_get i] : ([] _> [t])"
| local_set:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Local_set i] : ([t] _> [])"
| local_tee:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Local_tee i] : ([t] _> [t])"
| global_get:"\<lbrakk>i < length(global \<C>); tg_t ((global \<C>)!i) = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Global_get i] : ([] _> [t])"
| global_set:"\<lbrakk>i < length(global \<C>); tg_t ((global \<C>)!i) = t; is_mut ((global \<C>)!i)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Global_set i] : ([t] _> [])"
| load:"\<lbrakk>length (memory \<C>) \<ge> 1; load_store_t_bounds a (option_projl tp_sx) t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Load t tp_sx a off] : ([T_num T_i32] _> [T_num t])"
| store:"\<lbrakk>length (memory \<C>) \<ge> 1; load_store_t_bounds a tp t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Store t tp a off] : ([T_num T_i32,T_num t] _> [])"
| load_vec:"\<lbrakk>length (memory \<C>) \<ge> 1; load_vec_t_bounds lvop a\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Load_vec lvop a off] : ([T_num T_i32] _> [T_vec T_v128])"
| load_lane_vec:"\<lbrakk>length (memory \<C>) \<ge> 1; i < vec_i_num svi \<and> 2^a \<le> (vec_i_length svi)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Load_lane_vec svi i a off] : ([T_num T_i32, T_vec T_v128] _> [T_vec T_v128])"
| store_vec:"\<lbrakk>length (memory \<C>) \<ge> 1; store_vec_t_bounds svop a\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Store_vec svop a off] : ([T_num T_i32,T_vec T_v128] _> [])"
| memory_size:"length (memory \<C>) \<ge> 1 \<Longrightarrow> \<C> \<turnstile> [Memory_size] : ([] _> [T_num T_i32])"
| memory_grow:"length (memory \<C>) \<ge> 1 \<Longrightarrow> \<C> \<turnstile> [Memory_grow] : ([T_num T_i32] _> [T_num T_i32])"
| table_set: "\<lbrakk>ti < length (table \<C>); tab_t_reftype ((table \<C>)!ti) = tr\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Table_set ti] : ([T_num T_i32, T_ref tr] _> [])"
| table_get: "\<lbrakk>ti < length (table \<C>); tab_t_reftype ((table \<C>)!ti) = tr\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Table_get ti] : ([T_num T_i32] _> [T_ref tr])"
| table_size: "ti < length (table \<C>) \<Longrightarrow> \<C> \<turnstile> [Table_size ti] : ([] _> [T_num T_i32])"
| table_grow: "\<lbrakk>ti < length (table \<C>); tab_t_reftype ((table \<C>)!ti) = tr\<rbrakk>  \<Longrightarrow> \<C> \<turnstile> [Table_grow ti] : ([T_ref tr, T_num T_i32] _> [T_num T_i32])"
| empty:"\<C> \<turnstile> [] : ([] _> [])"
| composition:"\<lbrakk>\<C> \<turnstile> es : (t1s _> t2s); \<C> \<turnstile> [e] : (t2s _> t3s)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> es @ [e] : (t1s _> t3s)"
| subsumption:"\<lbrakk>\<C> \<turnstile> es : (tf1 _> tf2); instr_subtyping (tf1 _> tf2) (tf1' _> tf2')\<rbrakk> \<Longrightarrow> \<C> \<turnstile> es : (tf1' _> tf2')"
| memory_init: "\<lbrakk>length (memory \<C>) \<ge> 1; i < length (data \<C>)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Memory_init i] : ([T_num T_i32, T_num T_i32, T_num T_i32] _> [])"
| memory_copy: "\<lbrakk>length (memory \<C>) \<ge> 1\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Memory_copy] : ([T_num T_i32, T_num T_i32, T_num T_i32] _> [])"
| memory_fill: "\<lbrakk>length (memory \<C>) \<ge> 1\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Memory_fill] : ([T_num T_i32, T_num T_i32, T_num T_i32] _> [])"
| table_init: "\<lbrakk>x < length (table \<C>); y < length (elem \<C>); tr = tab_t_reftype (table \<C>!x); tr = elem \<C>!y\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Table_init x y] : ([T_num T_i32, T_num T_i32, T_num T_i32] _> [])"
| table_copy: "\<lbrakk>x < length (table \<C>); tr = tab_t_reftype (table \<C>!x); y < length (table \<C>); tr = tab_t_reftype (table \<C>!y)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Table_copy x y] : ([T_num T_i32, T_num T_i32, T_num T_i32] _> [])"
| table_fill: "\<lbrakk>x < length (table \<C>); tr = tab_t_reftype (table \<C>!x)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Table_fill x ] : ([T_num T_i32, T_ref tr, T_num T_i32] _> [])"
| elem_drop: "x < length (elem \<C>) \<Longrightarrow> \<C> \<turnstile> [Elem_drop x] : ([] _> [])"
| data_drop: "x < length (data \<C>) \<Longrightarrow> \<C> \<turnstile> [Data_drop x] : ([] _> [])"

inductive ref_typing :: "[s, v_ref, t_ref] => bool" where
   "ref_typing s (ConstNull t) (t)"
 | "f < length (funcs s) \<Longrightarrow> ref_typing s (ConstRefFunc f) (T_func_ref)"
 | "ref_typing s (ConstRefExtern _) (T_ext_ref)"

inductive v_typing :: "s \<Rightarrow> v \<Rightarrow> t \<Rightarrow> bool" where
  "v_typing s (V_num vn) (T_num (typeof_num vn))" |
  "v_typing s (V_vec vv) (T_vec (typeof_vec vv))" |
  "ref_typing s vr t \<Longrightarrow> v_typing s (V_ref vr) (T_ref t)"

definition "glob_typing g tg = (tg_mut tg = g_mut g \<and> tg_t tg = typeof (g_val g))"

definition "globi_agree gs n g = (n < length gs \<and> glob_typing (gs!n) g)"

definition "tabi_agree ts n tab_t =
  (n < length ts \<and> tab_subtyping (fst(ts!n)) tab_t)"

definition "memi_agree ms n mem_t =
  (n < length ms \<and> mem_subtyping (fst(ms!n)) mem_t)"

definition "funci_agree fs n f = (n < length fs \<and> (cl_type (fs!n)) = f)"

definition data_typing :: "datainst \<Rightarrow> data_t \<Rightarrow> bool "where
  "data_typing d dt = True"

definition datai_agree :: "datainst list \<Rightarrow> nat \<Rightarrow> data_t \<Rightarrow> bool" where
  "datai_agree ds n dt = (n < length ds \<and> data_typing (ds!n) dt)"

definition "elem_typing" :: "s \<Rightarrow> eleminst \<Rightarrow> elem_t \<Rightarrow> bool" where
  "elem_typing s ei et = (fst ei = et \<and> list_all (\<lambda> vr. ref_typing s vr et) (snd ei))"

definition "elemi_agree s es n et = (n < length es \<and> elem_typing s (es!n) et)"

inductive inst_typing :: "[s, inst, t_context] \<Rightarrow> bool" where
  "\<lbrakk>list_all2 (funci_agree (funcs s)) fs tfs;
    list_all2 (globi_agree (globs s)) gs tgs;
    list_all2 (tabi_agree (tabs s)) tbs tabs_t;
    list_all2 (memi_agree (mems s)) ms mems_t;
    list_all2 (elemi_agree s (elems s)) es elems_t;
    list_all2 (datai_agree (datas s)) ds datas_t\<rbrakk>
      \<Longrightarrow> inst_typing s \<lparr>types = ts, funcs = fs, tabs = tbs, mems = ms, globs = gs, elems = es, datas = ds\<rparr>
                        \<lparr>types_t = ts, func_t = tfs, global = tgs, elem = elems_t, data = datas_t, table = tabs_t, memory = mems_t, local = [], label = [], return = None, refs = [0..<length fs]\<rparr>"

inductive frame_typing :: "[s, f, t_context] \<Rightarrow> bool" where
"\<lbrakk>list_all2 (\<lambda> v t. v_typing s v t) (f_locs f) tvs; inst_typing s (f_inst f) \<C>\<rbrakk> \<Longrightarrow> frame_typing s f (\<C>\<lparr>local := tvs\<rparr>)"

inductive cl_typing :: "[s, cl, tf] \<Rightarrow> bool" where
   "\<lbrakk>inst_typing s i \<C>; tf = (t1s _> t2s); \<C>\<lparr>local := t1s @ ts, label := ([t2s] @ (label \<C>)), return := Some t2s\<rparr> \<turnstile> es : ([] _> t2s); n_zeros ts \<noteq> None\<rbrakk> \<Longrightarrow> cl_typing s (Func_native i tf ts es) (t1s _> t2s)"
 |  "cl_typing s (Func_host tf h) tf"

inductive e_typing :: "[s, t_context, e list, tf] \<Rightarrow> bool" ("_\<bullet>_ \<turnstile> _ : _" 60)
and       thread_typing :: "[s, (t list) option, f, e list, t list] \<Rightarrow> bool" ("_\<bullet>_ \<tturnstile>' _;_ : _" 60) where
  "\<C> \<turnstile> b_es : tf \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> $*b_es : tf"
| "\<lbrakk>\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s); \<S>\<bullet>\<C> \<turnstile> [e] : (t2s _> t3s)\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> es @ [e] : (t1s _> t3s)"
| "\<lbrakk>\<S>\<bullet>\<C> \<turnstile> es : (tf1 _> tf2); instr_subtyping (tf1 _> tf2) (tf1' _> tf2')\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> es : (tf1' _> tf2')"
| "ref_typing \<S> v_r t \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> [Ref v_r] :([] _> [T_ref t])"
| "\<S>\<bullet>\<C> \<turnstile> [Trap] : tf"
| "\<lbrakk>\<S>\<bullet>Some ts \<tturnstile> f;es : ts; length ts = n\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> [Frame n f es] : ([] _> ts)"
| "\<lbrakk>i < length (funcs \<S>); cl_type ((funcs \<S>)!i) = tf\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C>  \<turnstile> [Invoke i] : tf"
| "\<lbrakk>\<S>\<bullet>\<C> \<turnstile> e0s : (ts _> t2s); \<S>\<bullet>\<C>\<lparr>label := ([ts] @ (label \<C>))\<rparr> \<turnstile> es : ([] _> t2s); length ts = n\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> [Label n e0s es] : ([] _> t2s)"
| "\<lbrakk>frame_typing \<S> f \<C>; \<S>\<bullet>\<C>\<lparr>return := rs\<rparr> \<turnstile> es : ([] _> ts)\<rbrakk> \<Longrightarrow> \<S>\<bullet>rs \<tturnstile> f;es : ts"

definition "glob_agree" :: "s \<Rightarrow> global \<Rightarrow> bool" where
  "glob_agree s glob = (\<exists> t. v_typing s (g_val glob) t)"

definition tab_agree  :: "[s, tabinst] => bool" where
"tab_agree s t = (case t of
 ((T_tab lims tr, tab_elems)) \<Rightarrow>
  l_min lims = (tab_size t) \<and>
  pred_option (\<lambda> max. tab_size t \<le> max) (tab_max t) \<and>
  list_all (\<lambda> vr. ref_typing s vr tr) tab_elems)"

definition elem_agree :: "[s, eleminst] \<Rightarrow> bool" where
  "elem_agree s ei = (list_all (\<lambda> vr. ref_typing s vr (fst ei)) (snd ei))"

definition data_agree :: "[s, datainst] \<Rightarrow> bool" where
  "data_agree s di = True"

inductive store_typing :: "s \<Rightarrow> bool" where
  "\<lbrakk>list_all (\<lambda>cl. \<exists>tf. cl_typing s cl tf) (funcs s);
    list_all (tab_agree s) (tabs s);
    list_all mem_agree (mems s);
    list_all (glob_agree s) (globs s);
    list_all (elem_agree s) (elems s);
    list_all (data_agree s) (datas s)
    \<rbrakk> \<Longrightarrow> store_typing s"

inductive config_typing :: "[s, f, e list, t list] \<Rightarrow> bool" ("\<turnstile> _;_;_ : _" 60) where
  "\<lbrakk>store_typing s; s\<bullet>None \<tturnstile> f;es : ts\<rbrakk> \<Longrightarrow> \<turnstile> s;f;es : ts"

inductive reduce_simple :: "[e list, e list] \<Rightarrow> bool" ("\<lparr>_\<rparr> \<leadsto> \<lparr>_\<rparr>" 60) where
  unop:"\<lparr>[$EConstNum v, $(Unop t op)]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_unop op v)]\<rparr>"
| binop_Some:"\<lbrakk>app_binop op v1 v2 = (Some v)\<rbrakk> \<Longrightarrow> \<lparr>[$EConstNum v1, $EConstNum v2, $(Binop t op)]\<rparr> \<leadsto> \<lparr>[$EConstNum v]\<rparr>"
| binop_None:"\<lbrakk>app_binop op v1 v2 = None\<rbrakk> \<Longrightarrow> \<lparr>[$EConstNum v1, $EConstNum v2, $(Binop t op)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
| testop:"\<lparr>[$EConstNum v, $(Testop t op)]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_testop op v)]\<rparr>"
| relop:"\<lparr>[$EConstNum v1, $EConstNum v2, $(Relop t op)]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_relop op v1 v2)]\<rparr>"
| convert_Some:"\<lbrakk>(typeof_num v) = t1; cvt t2 sat_sx v = (Some v')\<rbrakk> \<Longrightarrow> \<lparr>[$(EConstNum v), $(Cvtop t2 Convert t1 sat_sx)]\<rparr> \<leadsto> \<lparr>[$(EConstNum v')]\<rparr>"
| convert_None:"\<lbrakk>(typeof_num v) = t1; cvt t2 sat_sx v = None\<rbrakk> \<Longrightarrow> \<lparr>[$(EConstNum v), $(Cvtop t2 Convert t1 sat_sx)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
| reinterpret:"(typeof_num v) = t1 \<Longrightarrow> \<lparr>[$(EConstNum v), $(Cvtop t2 Reinterpret t1 None)]\<rparr> \<leadsto> \<lparr>[$(EConstNum (wasm_reinterpret t2 v))]\<rparr>"
| null: "\<lparr>[$(Ref_null t)]\<rparr> \<leadsto> \<lparr>[Ref (ConstNull t)]\<rparr>"
| is_null_true: "is_null_ref v_r \<Longrightarrow> \<lparr>[Ref v_r, $Ref_is_null]\<rparr> \<leadsto> \<lparr>[$EConstNum (ConstInt32 (wasm_bool True))]\<rparr>"
| is_null_false: "\<not>is_null_ref v_r \<Longrightarrow> \<lparr>[Ref v_r, $Ref_is_null]\<rparr> \<leadsto> \<lparr>[$EConstNum (ConstInt32 (wasm_bool False))]\<rparr>"
| unop_vec:"\<lparr>[$EConstVec v, $(Unop_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_unop_vec op v)]\<rparr>"
| binop_vec_Some:"\<lbrakk>app_binop_vec op v1 v2 = Some v\<rbrakk> \<Longrightarrow> \<lparr>[$EConstVec v1, $EConstVec v2, $(Binop_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstVec v]\<rparr>"
| binop_vec_None:"\<lbrakk>app_binop_vec op v1 v2 = None\<rbrakk> \<Longrightarrow> \<lparr>[$EConstVec v1, $EConstVec v2, $(Binop_vec op)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
| ternop_vec:"\<lparr>[$EConstVec v1, $EConstVec v2, $EConstVec v3, $(Ternop_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_ternop_vec op v1 v2 v3)]\<rparr>"
| test_vec:"\<lparr>[$EConstVec v, $(Test_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstNum (ConstInt32 (app_test_vec op v))]\<rparr>"
| shift_vec:"\<lparr>[$EConstVec v, $EConstNum (ConstInt32 n), $(Shift_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_shift_vec op v n)]\<rparr>"
| splat_vec:"\<lparr>[$EConstNum v, $(Splat_vec sv)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_splat_vec sv v)]\<rparr>"
| extract_vec:"\<lparr>[$EConstVec v, $(Extract_vec sv sx i)]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_extract_vec sv sx i v)]\<rparr>"
| replace_vec:"\<lparr>[$EConstVec v, $EConstNum vn, $(Replace_vec sv i)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_replace_vec sv i v vn)]\<rparr>"
| unreachable:"\<lparr>[$ Unreachable]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
| nop:"\<lparr>[$ Nop]\<rparr> \<leadsto> \<lparr>[]\<rparr>"

| drop:"\<lparr>[$C v, ($ Drop)]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
| select_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$C v1, $C v2, $EConstNum (ConstInt32 n), ($ Select t_tag)]\<rparr> \<leadsto> \<lparr>[$C v2]\<rparr>"
| select_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$C v1, $C v2, $EConstNum (ConstInt32 n), ($ Select t_tag)]\<rparr> \<leadsto> \<lparr>[$C v1]\<rparr>"
| if_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 n), $(If tb e1s e2s)]\<rparr> \<leadsto> \<lparr>[$(Block tb e2s)]\<rparr>"
| if_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 n), $(If tb e1s e2s)]\<rparr> \<leadsto> \<lparr>[$(Block tb e1s)]\<rparr>"
| label_const:"\<lparr>[Label n es ($C* vs)]\<rparr> \<leadsto> \<lparr>($C* vs)\<rparr>"
| label_trap:"\<lparr>[Label n es [Trap]]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
| br:"\<lbrakk>length vs = n; Lfilled i lholed (($C* vs) @ [$(Br i)]) LI\<rbrakk> \<Longrightarrow> \<lparr>[Label n es LI]\<rparr> \<leadsto> \<lparr>($C* vs) @ es\<rparr>"
| br_if_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 n), $(Br_if i)]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
| br_if_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 n), $(Br_if i)]\<rparr> \<leadsto> \<lparr>[$(Br i)]\<rparr>"
| br_table:"\<lbrakk>length is > (nat_of_int c)\<rbrakk> \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 c), $(Br_table is i)]\<rparr> \<leadsto> \<lparr>[$(Br (is!(nat_of_int c)))]\<rparr>"
| br_table_length:"\<lbrakk>length is \<le> (nat_of_int c)\<rbrakk> \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 c), $(Br_table is i)]\<rparr> \<leadsto> \<lparr>[$(Br i)]\<rparr>"
| local_const:"\<lparr>[Frame n f ($C* vs)]\<rparr> \<leadsto> \<lparr>($C* vs)\<rparr>"
| local_trap:"\<lparr>[Frame n f [Trap]]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
| return:"\<lbrakk>length vs = n; Lfilled j lholed (($C* vs) @ [$Return]) es\<rbrakk>  \<Longrightarrow> \<lparr>[Frame n f es]\<rparr> \<leadsto> \<lparr>($C* vs)\<rparr>"
| local_tee:"\<lparr>[$C v, $(Local_tee i)]\<rparr> \<leadsto> \<lparr>[$C v, $C v, $(Local_set i)]\<rparr>"
| trap:"\<lbrakk>es \<noteq> [Trap]; Lfilled 0 lholed [Trap] es\<rbrakk> \<Longrightarrow> \<lparr>es\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"

inductive reduce :: "[s, f, e list, s, f, e list] \<Rightarrow> bool" ("\<lparr>_;_;_\<rparr> \<leadsto> \<lparr>_;_;_\<rparr>" 60) where
  basic:"\<lparr>e\<rparr> \<leadsto> \<lparr>e'\<rparr> \<Longrightarrow> \<lparr>s;f;e\<rparr> \<leadsto> \<lparr>s;f;e'\<rparr>"
| call:"\<lparr>s;f;[$(Call j)]\<rparr> \<leadsto> \<lparr>s;f;[Invoke (sfunc_ind (f_inst f) j)]\<rparr>"
| call_indirect_Some:"\<lbrakk>(f_inst f) = i; stab s i ti (nat_of_int c) = Some (ConstRefFunc i_cl); stypes i j = tf; cl_type (funcs s!i_cl) = tf\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 c), $(Call_indirect ti j)]\<rparr> \<leadsto> \<lparr>s;f;[Invoke i_cl]\<rparr>"
| call_indirect_None:"\<lbrakk>(f_inst f) = i; (stab s i ti (nat_of_int c) = Some (ConstRefFunc i_cl) \<and> stypes i j \<noteq> cl_type (funcs s!i_cl)) \<or> \<not> is_some_const_ref_func (stab s i ti (nat_of_int c))\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 c), $(Call_indirect ti j)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| invoke_native:"\<lbrakk>(funcs s!i_cl) = Func_native j (t1s _> t2s) ts es; ves = ($C* vcs); length vcs = n; length ts = k; length t1s = n; length t2s = m; (n_zeros ts = Some zs) \<rbrakk> \<Longrightarrow> \<lparr>s;f;ves @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s;f;[Frame m \<lparr> f_locs = vcs@zs, f_inst = j \<rparr> [(Label m [] ($*es))]]\<rparr>"
| invoke_host_Some:"\<lbrakk>(funcs s!i_cl) = Func_host (t1s _> t2s) (Host_func hf); ves = ($C* vcs); length vcs = n; length t1s = n; length t2s = m; host_func_apply s (t1s _> t2s) hf vcs hs (Some (s', vcs'))\<rbrakk> \<Longrightarrow> \<lparr>s;f;ves @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s';f;($C* vcs')\<rparr>"
| invoke_host_None:"\<lbrakk>(funcs s!i_cl) = Func_host (t1s _> t2s) h; ves = ($C* vcs); length vcs = n; length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>s;f;ves @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| ref_func: "fa = (inst.funcs (f_inst f))!j \<Longrightarrow> \<lparr>s;f;[$(Ref_func j)]\<rparr> \<leadsto> \<lparr>s;f;[Ref (ConstRefFunc (fa))]\<rparr>"
| local_get:"\<lbrakk>length vi = j; f_locs f = (vi @ [v] @ vs)\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$(Local_get j)]\<rparr> \<leadsto> \<lparr>s;f;[$C v]\<rparr>"
| local_set:"\<lbrakk>length vi = j\<rbrakk> \<Longrightarrow> \<lparr>s;\<lparr> f_locs = (vi @ [v] @ vs), f_inst = i \<rparr>;[$C v', $(Local_set j)]\<rparr> \<leadsto> \<lparr>s;\<lparr> f_locs = (vi @ [v'] @ vs), f_inst = i \<rparr>;[]\<rparr>"
| global_get:"\<lparr>s;f;[$(Global_get j)]\<rparr> \<leadsto> \<lparr>s;f;[$C(sglob_val s (f_inst f) j)]\<rparr>"
| global_set:"supdate_glob s (f_inst f) j v = s' \<Longrightarrow> \<lparr>s;f;[$C v, $(Global_set j)]\<rparr> \<leadsto> \<lparr>s';f;[]\<rparr>"
| load_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load m (nat_of_int k) off (t_num_length t) = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load t None a off)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (wasm_deserialise_num bs t)]\<rparr>"
| load_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load m (nat_of_int k) off (t_num_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load t None a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| load_packed_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load_packed sx m (nat_of_int k) off (tp_num_length tp) (t_num_length t) = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load t (Some (tp, sx)) a off)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (wasm_deserialise_num bs t)]\<rparr>"
| load_packed_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load_packed sx m (nat_of_int k) off (tp_num_length tp) (t_num_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load t (Some (tp, sx)) a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| store_Some:"\<lbrakk>(typeof_num v) = t; smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store m (nat_of_int k) off (bits_num v) (t_num_length t) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstNum v, $(Store t None a off)]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[]\<rparr>"
| store_None:"\<lbrakk>(typeof_num v) = t; smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store m (nat_of_int k) off (bits_num v) (t_num_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstNum v, $(Store t None a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| store_packed_Some:"\<lbrakk>(typeof_num v) = t; smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store_packed m (nat_of_int k) off (bits_num v) (tp_num_length tp) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstNum v, $(Store t (Some tp) a off)]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[]\<rparr>"
| store_packed_None:"\<lbrakk>(typeof_num v) = t; smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store_packed m (nat_of_int k) off (bits_num v) (tp_num_length tp) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstNum v, $(Store t (Some tp) a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| load_vec_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load_vec lv m (nat_of_int k) off = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load_vec lv a off)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstVec (ConstVec128 (deserialise_v128 bs))]\<rparr>"
| load_vec_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load_vec lv m (nat_of_int k) off = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load_vec lv a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| load_lane_vec_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load m (nat_of_int k) off (vec_i_length svi) = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $(Load_lane_vec svi i a off)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstVec (ConstVec128 (insert_lane_vec svi i bs v))]\<rparr>"
| load_lane_vec_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load m (nat_of_int k) off (vec_i_length svi) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $(Load_lane_vec svi i a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| store_vec_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; (store_serialise_vec sv v) = bs; store m (nat_of_int k) off bs (length bs) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $(Store_vec sv a off)]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[]\<rparr>"
| store_vec_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; (store_serialise_vec sv v) = bs; store m (nat_of_int k) off bs (length bs) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $(Store_vec sv a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| memory_size:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$Memory_size]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int_of_nat n))]\<rparr>"
| memory_grow:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; mem_size m = n; mem_grow m (nat_of_int c) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 c), $(Memory_grow)]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[$EConstNum (ConstInt32 (int_of_nat n))]\<rparr>"
| memory_grow_fail:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 c),$(Memory_grow)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 int32_minus_one)]\<rparr>"
| table_get: "\<lbrakk>stab_ind (f_inst f) ti = Some a; load_tabs1 (tabs s) a (nat_of_int n) = Some val \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$(EConstNum (ConstInt32 n)), $(Table_get ti)]\<rparr> \<leadsto> \<lparr>s;f;[Ref val]\<rparr>"
| table_get_fail: "\<lbrakk>stab_ind (f_inst f) ti = Some a; load_tabs1 (tabs s) a (nat_of_int n) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$(EConstNum (ConstInt32 n)), $(Table_get ti)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| table_set: "\<lbrakk>stab_ind (f_inst f) ti = Some a; store_tabs1 (tabs s) a (nat_of_int n) vr = Some tabs'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$(EConstNum (ConstInt32 n)), Ref vr, $(Table_set ti)]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:= tabs'\<rparr>;f;[]\<rparr>"
| table_set_fail: "\<lbrakk>stab_ind (f_inst f) ti = Some a; store_tabs1 (tabs s) a (nat_of_int n) vr = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$(EConstNum (ConstInt32 n)), Ref vr, $(Table_set ti)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| table_size: "\<lbrakk>stab_ind (f_inst f) ti = Some a; (tabs s)!a = t; tab_size t = n\<rbrakk> \<Longrightarrow>  \<lparr>s;f;[ $(Table_size ti)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int_of_nat n))]\<rparr>"
| table_grow: "\<lbrakk>stab_ind (f_inst f) ti = Some a; (tabs s)!a = tab; sz = tab_size tab; grow_tab tab (nat_of_int n) vr = Some tab'\<rbrakk> \<Longrightarrow>  \<lparr>s;f;[Ref vr, $EConstNum (ConstInt32 n), $(Table_grow ti)]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:= ((tabs s)[a := tab'])\<rparr>;f;[$EConstNum (ConstInt32 (int_of_nat sz))]\<rparr>"
| table_grow_fail: "\<lparr>s;f;[Ref vr, $EConstNum (ConstInt32 n), $(Table_grow ti)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int32_minus_one))]\<rparr>"
| block:"\<lbrakk>length vs = n; tb_tf (f_inst f) tb = (t1s _> t2s); length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>s;f;($C* vs) @ [$(Block tb es)]\<rparr> \<leadsto> \<lparr>s;f;[Label m [] (($C* vs) @ ($* es))]\<rparr>"
| loop:"\<lbrakk>length vs = n; tb_tf (f_inst f) tb = (t1s _> t2s); length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>s;f;($C* vs) @ [$(Loop tb es)]\<rparr> \<leadsto> \<lparr>s;f;[Label n [$(Loop tb es)] (($C* vs) @ ($* es))]\<rparr>"
| label:"\<lbrakk>\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>; Lfilled k lholed es les; Lfilled k lholed es' les'\<rbrakk> \<Longrightarrow> \<lparr>s;f;les\<rparr> \<leadsto> \<lparr>s';f';les'\<rparr>"
| local:"\<lbrakk>\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>\<rbrakk> \<Longrightarrow> \<lparr>s;f0;[Frame n f es]\<rparr> \<leadsto> \<lparr>s';f0;[Frame n f' es']\<rparr>"
| memory_init_trap: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; da =(inst.datas (f_inst f))!x; dat = (datas s)!da; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc+nn > length dat \<or>  ndest+nn > mem_length m \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| memory_init_done: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; da =(inst.datas (f_inst f))!x; dat = (datas s)!da; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc+nn \<le> length dat;  ndest+nn \<le> mem_length m; nn = 0 \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
| memory_init: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; da =(inst.datas (f_inst f))!x; dat = (datas s)!da; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc+nn \<le> length dat;  ndest+nn \<le> mem_length m; nn = nn_pred+1; b = nat_of_uint8 (dat!nsrc) \<rbrakk> \<Longrightarrow>
  \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Memory_init x]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int_of_nat (ndest))), $EConstNum (ConstInt32 (int_of_nat b)), $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 (int_of_nat (ndest+1))), $EConstNum (ConstInt32 (int_of_nat (nsrc+1))), $EConstNum (ConstInt32 (int_of_nat (nn_pred))) ,$Memory_init x]\<rparr>"
| memory_copy_trap: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc+nn > mem_length m \<or>  ndest+nn > mem_length m \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Memory_copy]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| memory_copy_done: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc+nn \<le> mem_length m; ndest+nn \<le> mem_length m; nn=0 \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Memory_copy]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
| memory_copy_1: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc+nn \<le> mem_length m; ndest+nn \<le> mem_length m; nn=nn_pred+1; ndest \<le> nsrc \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n), $Memory_copy]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $Load T_i32 (Some (Tp_i8, U)) 0 0, $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 (int_of_nat (ndest+1))), $EConstNum (ConstInt32 (int_of_nat (nsrc+1))), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Memory_copy]\<rparr>"
| memory_copy_2: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc+nn \<le> mem_length m; ndest+nn \<le> mem_length m; nn=nn_pred+1; ndest > nsrc \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n), $Memory_copy]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int_of_nat (ndest+nn_pred))), $EConstNum (ConstInt32 (int_of_nat (nsrc+nn_pred))), $Load T_i32 (Some (Tp_i8, U)) 0 0, $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Memory_copy]\<rparr>"
| memory_fill_trap: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; ndest = nat_of_int dest; nn = nat_of_int n; ndest+nn > mem_length m \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n),$Memory_fill]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| memory_fill_done: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; ndest = nat_of_int dest; nn = nat_of_int n; ndest+nn \<le> mem_length m; nn=0 \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n),$Memory_fill]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
| memory_fill: "\<lbrakk>smem_ind (f_inst f) = Some ma; (mems s)!ma = m; ndest = nat_of_int dest; nn = nat_of_int n; ndest+nn \<le> mem_length m; nn=nn_pred+1 \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 n),$Memory_fill]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 val), $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 (int_of_nat (ndest+1))), $EConstNum (ConstInt32 val), $EConstNum (ConstInt32 (int_of_nat nn_pred)) ,$Memory_fill]\<rparr>"
| table_init_trap: "\<lbrakk>stab_ind (f_inst f) x = Some ta; (tabs s)!ta = tab;  ea = (inst.elems (f_inst f))!y; el = (elems s)!ea; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc+nn > length (snd el) \<or> ndest+nn > length (snd tab)\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| table_init_done: "\<lbrakk>stab_ind (f_inst f) x = Some ta; (tabs s)!ta = tab; ea = (inst.elems (f_inst f))!y; el = (elems s)!ea; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc + nn \<le> length (snd el); ndest + nn  \<le> length (snd tab); nn = 0\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
| table_init: "\<lbrakk>stab_ind (f_inst f) x = Some ta; (tabs s)!ta = tab; ea = (inst.elems (f_inst f))!y; el = (elems s)!ea; ndest = nat_of_int dest; nsrc = nat_of_int src; nn = nat_of_int n; nsrc + nn \<le> length (snd el); ndest + nn  \<le> length (snd tab); nn = nn_pred+1; val = (snd el)!nsrc\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $C (V_ref val), $Table_set x, $EConstNum (ConstInt32 (int_of_nat (ndest+1))), $EConstNum (ConstInt32 (int_of_nat (nsrc+1))), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_init x y]\<rparr>"
| table_fill_trap: "\<lbrakk>stab_ind (f_inst f) x = Some ta; (tabs s)!ta = tab; ni = nat_of_int i; nn = nat_of_int n; ni+nn > length (snd tab) \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 i), $C (V_ref vr), $EConstNum (ConstInt32  n),$Table_fill x]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| table_fill_done: "\<lbrakk>stab_ind (f_inst f) x = Some ta; (tabs s)!ta = tab; ni = nat_of_int i; nn = nat_of_int n; ni+nn \<le> length (snd tab); nn = 0 \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 i), $C (V_ref vr), $EConstNum (ConstInt32 n),$Table_fill x]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
| table_fill: "\<lbrakk>stab_ind (f_inst f) x = Some ta; (tabs s)!ta = tab; ni = nat_of_int i; nn = nat_of_int n; ni+nn \<le> length (snd tab); nn = nn_pred+1 \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 i), $C (V_ref vr), $EConstNum (ConstInt32 n),$Table_fill x]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 i), $C (V_ref vr), $Table_set x, $EConstNum (ConstInt32 (int_of_nat (ni+1))), $C (V_ref vr), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_fill x]\<rparr>"
| table_copy_trap: "\<lbrakk>stab_ind (f_inst f) x = Some tax; (tabs s)!tax = tabx; stab_ind (f_inst f) y = Some tay; (tabs s)!ty = taby; ndest = nat_of_int dest; nrsc = nat_of_int src; nn = nat_of_int n; nsrc+nn > length (snd tabx) \<or> ndest + nn > length (snd taby) \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| table_copy_done: "\<lbrakk>stab_ind (f_inst f) x = Some tax; (tabs s)!tax = tabx; stab_ind (f_inst f) y = Some tay; (tabs s)!ty = taby; ndest = nat_of_int dest; nrsc = nat_of_int src; nn = nat_of_int n; nsrc+nn \<le> length (snd tabx); ndest+nn \<le> length (snd taby); nn = 0 \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;[]\<rparr>"
| table_copy_1: "\<lbrakk>stab_ind (f_inst f) x = Some tax; (tabs s)!tax = tabx; stab_ind (f_inst f) y = Some tay; (tabs s)!ty = taby; ndest = nat_of_int dest; nrsc = nat_of_int src; nn = nat_of_int n; nsrc+nn \<le> length (snd tabx); ndest+nn \<le> length (snd taby); nn = nn_pred+1; ndest \<le> nsrc \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $Table_get y, $Table_set x, $EConstNum (ConstInt32 (int_of_nat (ndest+1))), $EConstNum (ConstInt32 (int_of_nat (nsrc+1))), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_copy x y]\<rparr>"
| table_copy_2: "\<lbrakk>stab_ind (f_inst f) x = Some tax; (tabs s)!tax = tabx; stab_ind (f_inst f) y = Some tay; (tabs s)!ty = taby; ndest = nat_of_int dest; nrsc = nat_of_int src; nn = nat_of_int n; nsrc+nn \<le> length (snd tabx); ndest+nn \<le> length (snd taby); nn = nn_pred+1; ndest > nsrc \<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 n),$Table_copy x y]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int_of_nat (ndest+nn_pred))), $EConstNum (ConstInt32 (int_of_nat (nsrc+nn_pred))), $Table_get y, $Table_set x, $EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_copy x y]\<rparr>"
| elem_drop: "a = (inst.elems (f_inst f))!x \<Longrightarrow> \<lparr>s;f;[$Elem_drop x]\<rparr> \<leadsto> \<lparr>s\<lparr>elems := (elems s)[a := (fst ((elems s)!a), [])]\<rparr>;f;[]\<rparr>"
| data_drop: "a = (inst.datas (f_inst f))!x \<Longrightarrow> \<lparr>s;f;[$Data_drop x]\<rparr> \<leadsto> \<lparr>s\<lparr>datas := (datas s)[a := []]\<rparr>;f;[]\<rparr>"

definition reduce_trans where
  "reduce_trans \<equiv> (\<lambda>(s,f,es) (s',f',es'). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>)^**"

definition reduce_irrtrans where
  "reduce_irrtrans \<equiv> (\<lambda>(s,f,es) (s',f',es'). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>)^++"

lemma reduce_irrtrans_trans:"reduce_irrtrans a b \<Longrightarrow> reduce_trans a b"
  unfolding reduce_irrtrans_def reduce_trans_def
  by simp

type_synonym v_stack = "v list"

abbreviation v_stack_to_es :: " v_stack \<Rightarrow> e list"
  where "v_stack_to_es v \<equiv> $C* (rev v)"

definition "computes cfg s' vs \<equiv> \<exists>f'. reduce_trans cfg (s', f', v_stack_to_es vs)"
  
definition "traps cfg s' \<equiv> \<exists>f'. reduce_trans cfg (s',f',[Trap])"

definition "empty_frame \<equiv> \<lparr>f_locs = [],f_inst = \<lparr> types = [], funcs = [], tabs = [], mems = [], globs = [], elems = [], datas = []\<rparr>\<rparr>"

definition "invoke_config s vargs i \<equiv> (s, empty_frame, ($C* vargs) @ [Invoke i])"

end
