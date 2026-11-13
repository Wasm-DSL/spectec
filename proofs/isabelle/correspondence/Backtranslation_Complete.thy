(* Completeness of the back-translation for runtime structures, administrative
   instructions and configurations: the back-translation of a translation gives the
   SpecTec term back.  Isabelle counterpart of the [*_complete] lemmas of
   ../wasmcert-rocq/backtranslation_props.v for these levels; the levels below
   (types, contexts, numbers, instructions) are in Completeness.thy.

   WasmCert-Isabelle drops three pieces of SpecTec information, which the
   back-translation fills in canonically (Backtranslation.thy, DIFFERENCES.md):
   module instances have no exports, a global's type is its value's type, and a
   function's type index is the first index of its type.  So completeness holds for
   SpecTec terms in this canonical form ([inst_canon], [global_canon],
   [funcinst_canon], [store_canon], [admin_ok]).  The Rocq bridge needs only
   well-formedness, because WasmCert-Coq keeps this information.

   As in Completeness.thy, instructions must satisfy [rt_ok] (the Rocq bridge's
   [ext_free]), and the back-translation's holes must invert the translation's
   (locale [back_complete]). *)
theory Backtranslation_Complete
  imports Backtranslation_Sound
begin

locale back_complete = vec_complete +
  assumes of_hostref_complete: "of_hostref (hostref a) = Some a"

section \<open>Canonical forms\<close>

definition inst_canon :: "moduleinst \<Rightarrow> bool" where
  "inst_canon mi \<longleftrightarrow> EXPORTS mi = []"

definition global_canon :: "globalinst \<Rightarrow> bool" where
  "global_canon gi \<longleftrightarrow> (case globalinst_TYPE gi of mk_globaltype m t \<Rightarrow> t = typeofval (VALUE gi))"

definition funcinst_canon :: "funcinst \<Rightarrow> bool" where
  "funcinst_canon fi \<longleftrightarrow> inst_canon (funcinst_MODULE fi) \<and>
     (case CODE fi of func_FUNC x ls body \<Rightarrow>
        first_index (funcinst_TYPE fi) (TYPES (funcinst_MODULE fi)) = Some (un x) \<and> list_all rt_ok body)"

definition store_canon :: "store \<Rightarrow> bool" where
  "store_canon st \<longleftrightarrow> list_all funcinst_canon (store_FUNCS st) \<and> list_all global_canon (store_GLOBALS st)"

primrec admin_ok :: "admininstr \<Rightarrow> bool" and admin_ok7 :: "admininstr_st7 \<Rightarrow> bool"
    and admin_ok8 :: "admininstr_st8 \<Rightarrow> bool" where
  "admin_ok (admininstr_sc0 x) = rt_ok (instr_of_a0 x)"
| "admin_ok (admininstr_sc1 x) = rt_ok (instr_of_a1 x)"
| "admin_ok (admininstr_sc2 x) = rt_ok (instr_of_a2 x)"
| "admin_ok (admininstr_sc3 x) = rt_ok (instr_of_a3 x)"
| "admin_ok (admininstr_sc4 x) = rt_ok (instr_of_a4 x)"
| "admin_ok (admininstr_sc5 x) = rt_ok (instr_of_a5 x)"
| "admin_ok (admininstr_sc6 x) = rt_ok (instr_of_a6 x)"
| "admin_ok (admininstr_sc7 x) = admin_ok7 x"
| "admin_ok (admininstr_sc8 x) = admin_ok8 x"
| "admin_ok7 (LABEL_underscore n ins es) = (list_all rt_ok ins \<and> list_all admin_ok es)"
| "admin_ok7 admininstr_st7_TRAP = True"
| "admin_ok7 (CALL_ADDR a) = True"
| "admin_ok7 (admininstr_st7_REF_HOST_ADDR a) = True"
| "admin_ok7 (admininstr_st7_REF_FUNC_ADDR a) = True"
| "admin_ok7 (admininstr_st7_DATA_DROP x) = True"
| "admin_ok7 (admininstr_st7_MEMORY_INIT x) = True"
| "admin_ok7 admininstr_st7_MEMORY_COPY = True"
| "admin_ok7 admininstr_st7_MEMORY_FILL = True"
| "admin_ok8 (FRAME_underscore n fr es) = (inst_canon (frame_MODULE fr) \<and> list_all admin_ok es)"

section \<open>Values\<close>

lemma (in back_complete) of_tr_ref[simp]: "of_ref (tr_ref r) = Some r"
  by (cases r) (simp_all add: tr_host_def of_hostref_complete)

lemma (in back_complete) of_tr_val: "wf_val v \<Longrightarrow> of_val (tr_val v) = Some v"
proof (induction rule: wf_val.induct)
  case (val_case_0 nt c)
  then show ?case using of_tr_num[OF val_case_0] by simp
next
  case (val_case_1 vt c)
  then show ?case by (cases vt) (simp add: of_tr_vec)
qed (simp_all add: tr_host_def of_hostref_complete)

lemma of_valtype_typeof: "wf_val v \<Longrightarrow> of_valtype (typeof (tr_val v)) = typeofval v"
proof (induction rule: wf_val.induct)
  case (val_case_0 nt c)
  then show ?case using of_tr_num[OF val_case_0] by (simp add: typeof_def)
next
  case (val_case_1 vt c)
  then show ?case by (cases vt) (simp add: typeof_def typeof_vec_def tr_vec_def)
qed (simp_all add: typeof_def typeof_ref_def)

section \<open>Runtime structures\<close>

lemma of_tr_byte: "wf_byte b \<Longrightarrow> of_byte (tr_byte b) = b"
  by (erule wf_byte.cases)
     (simp add: of_byte_def byte_of_nat_def uint8_of_nat.abs_eq nat_of_uint8.abs_eq unat_of_nat)

lemma of_tr_bytes: "list_all wf_byte bs \<Longrightarrow> map of_byte (map tr_byte bs) = bs"
  by (induction bs) (simp_all add: of_tr_byte)

lemma of_tr_local[simp]: "of_local (tr_local l) = l"
  by (cases l) (simp add: of_local_def)

lemma tr_moduleinst_types[simp]: "inst.types (tr_moduleinst mi) = map tr_functype (TYPES mi)"
  by (simp add: tr_moduleinst_def)

lemma of_tr_inst: "inst_canon mi \<Longrightarrow> of_inst (tr_moduleinst mi) = mi"
  by (cases mi) (simp add: inst_canon_def of_inst_def tr_moduleinst_def comp_def)

lemma inj_tr_functype: "inj tr_functype"
  by (rule inj_on_inverseI[of _ of_functype]) simp

lemma first_index_map: "inj f \<Longrightarrow> first_index (f x) (map f ys) = first_index x ys"
  by (induction ys) (simp_all add: inj_eq)

lemma (in vec_complete) of_tr_instrs_map:
  "list_all wf_instr ins \<Longrightarrow> list_all rt_ok ins \<Longrightarrow> those (map of_instr (map tr_instr ins)) = Some ins"
proof -
  assume "list_all wf_instr ins" "list_all rt_ok ins"
  then have "those (map (\<lambda>i. of_instr (tr_instr i)) ins) = Some ins"
    by (intro those_map_id) (simp add: list_all_iff of_tr_instr)
  then show ?thesis by (simp add: comp_def)
qed

lemma (in back_complete) of_tr_funcinst:
  assumes w: "wf_funcinst fi" and c: "funcinst_canon fi"
  shows "of_cl (tr_funcinst fi) = Some fi"
proof -
  obtain ft mi cd where fi: "fi = \<lparr>funcinst_TYPE = ft, funcinst_MODULE = mi, CODE = cd\<rparr>"
    by (cases fi)
  obtain x ls body where cd: "cd = func_FUNC x ls body" by (cases cd)
  have wx: "wf_uN 32 x" and wb: "list_all wf_instr body"
    using w unfolding fi cd by (auto elim!: wf_funcinst.cases wf_func.cases)
  have mi: "inst_canon mi" and fx: "first_index ft (TYPES mi) = Some (un x)" and rb: "list_all rt_ok body"
    using c unfolding fi cd funcinst_canon_def by simp_all
  have fx': "first_index (tr_functype ft) (map tr_functype (TYPES mi)) = Some (un x)"
    using fx by (simp add: first_index_map[OF inj_tr_functype])
  have ix: "Option.bind (first_index (tr_functype ft) (inst.types (tr_moduleinst mi))) of_u32 = Some x"
    using fx' un_lt_32[OF wx] by (cases x) (simp add: of_u32_def)
  have bd: "those (map of_instr (tr_instrs body)) = Some body"
    using of_tr_instrs_map[OF wb rb] by (simp add: tr_instrs_def)
  have tf: "tr_funcinst fi = Func_native (tr_moduleinst mi) (tr_functype ft) (map tr_local ls) (tr_instrs body)"
    unfolding fi cd by (simp add: tr_funcinst_def)
  have "of_cl (tr_funcinst fi) =
          Some \<lparr>funcinst_TYPE = of_functype (tr_functype ft), funcinst_MODULE = of_inst (tr_moduleinst mi),
                CODE = func_FUNC x (map of_local (map tr_local ls)) body\<rparr>"
    unfolding tf using ix bd by simp
  then show ?thesis using of_tr_inst[OF mi] by (simp add: fi cd comp_def)
qed

lemma (in back_complete) of_tr_globalinst:
  assumes w: "wf_globalinst gi" and c: "global_canon gi"
  shows "of_global (tr_globalinst gi) = Some gi"
proof -
  obtain gt v where gi: "gi = \<lparr>globalinst_TYPE = gt, VALUE = v\<rparr>" by (cases gi)
  obtain m t where gt: "gt = mk_globaltype m t" by (cases gt)
  have wv: "wf_val v" using w unfolding gi by (auto elim: wf_globalinst.cases)
  have t: "t = typeofval v" using c unfolding gi gt global_canon_def by simp
  show ?thesis
    unfolding gi gt using of_tr_val[OF wv] of_valtype_typeof[OF wv] t
    by (simp add: of_global_def tr_globalinst_def)
qed

lemma (in back_complete) of_tr_tableinst: "wf_tableinst ti \<Longrightarrow> of_tabinst (tr_tableinst ti) = Some ti"
  by (cases ti) (auto elim!: wf_tableinst.cases simp: of_tabinst_def tr_tableinst_def of_tr_tabletype
                      comp_def those_map_id)

lemma of_tr_meminst:
  assumes "wf_meminst mi"
  shows "of_mem (tr_meminst mi) = Some mi"
proof -
  obtain mt bs where mi: "mi = \<lparr>meminst_TYPE = mt, BYTES = bs\<rparr>" by (cases mi)
  have w: "wf_memtype mt" "list_all wf_byte bs" using assms unfolding mi by (auto elim: wf_meminst.cases)
  have "Rep_mem_rep (Abs_mem_rep (map tr_byte bs)) = map tr_byte bs" by (simp add: Abs_mem_rep_inverse)
  moreover have "map of_byte (map tr_byte bs) = bs" by (rule of_tr_bytes[OF w(2)])
  ultimately show ?thesis
    unfolding mi using of_tr_memtype[OF w(1)] by (simp add: of_mem_def tr_meminst_def del: map_map)
qed

lemma (in back_complete) of_tr_eleminst: "of_eleminst (tr_eleminst ei) = Some ei"
  by (cases ei) (simp add: of_eleminst_def tr_eleminst_def comp_def those_map_id)

lemma of_tr_datainst: "wf_datainst d \<Longrightarrow> of_datainst (tr_datainst d) = d"
  by (cases d) (auto elim!: wf_datainst.cases simp: of_datainst_def tr_datainst_def of_tr_bytes simp del: map_map)

lemma those_map_Some_id[simp]: "those (map Some xs) = Some xs"
  by (induction xs) simp_all

lemma those_map_comp_id:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f (g x) = Some x) \<Longrightarrow> those (map f (map g xs)) = Some xs"
  by (induction xs) auto

lemma map_comp_id: "(\<And>x. x \<in> set xs \<Longrightarrow> f (g x) = x) \<Longrightarrow> map f (map g xs) = xs"
  by (induction xs) auto

lemma (in back_complete) of_tr_store:
  assumes w: "wf_store st" and c: "store_canon st"
  shows "of_store (tr_store st) = Some st"
proof -
  obtain fs gs ts ms es ds where st: "st = \<lparr>store_FUNCS = fs, store_GLOBALS = gs, store_TABLES = ts,
      store_MEMS = ms, store_ELEMS = es, store_DATAS = ds\<rparr>"
    by (cases st)
  have wf: "list_all wf_funcinst fs" "list_all wf_globalinst gs" "list_all wf_tableinst ts"
    "list_all wf_meminst ms" "list_all wf_datainst ds"
    using w unfolding st by (auto elim: wf_store.cases)
  have cf: "list_all funcinst_canon fs" "list_all global_canon gs"
    using c unfolding st store_canon_def by simp_all
  have "those (map of_cl (map tr_funcinst fs)) = Some fs"
    using wf(1) cf(1) by (intro those_map_comp_id) (auto simp: list_all_iff intro: of_tr_funcinst)
  moreover have "those (map of_global (map tr_globalinst gs)) = Some gs"
    using wf(2) cf(2) by (intro those_map_comp_id) (auto simp: list_all_iff intro: of_tr_globalinst)
  moreover have "those (map of_tabinst (map tr_tableinst ts)) = Some ts"
    using wf(3) by (intro those_map_comp_id) (auto simp: list_all_iff intro: of_tr_tableinst)
  moreover have "those (map of_mem (map tr_meminst ms)) = Some ms"
    using wf(4) by (intro those_map_comp_id) (auto simp: list_all_iff intro: of_tr_meminst)
  moreover have "those (map of_eleminst (map tr_eleminst es)) = Some es"
    by (intro those_map_comp_id) (rule of_tr_eleminst)
  moreover have "map of_datainst (map tr_datainst ds) = ds"
    using wf(5) by (intro map_comp_id) (auto simp: list_all_iff intro: of_tr_datainst)
  ultimately show ?thesis unfolding st by (simp add: of_store_def tr_store_def)
qed

lemma (in back_complete) of_tr_frame:
  assumes w: "wf_frame fr" and c: "inst_canon (frame_MODULE fr)"
  shows "of_frame (tr_frame fr) = Some fr"
proof -
  obtain vs mi where fr: "fr = \<lparr>LOCALS = vs, frame_MODULE = mi\<rparr>" by (cases fr)
  have wv: "list_all wf_val vs" using w unfolding fr by (auto elim: wf_frame.cases)
  have "those (map of_val (map tr_val vs)) = Some vs"
    using wv by (intro those_map_comp_id) (auto simp: list_all_iff intro: of_tr_val)
  then show ?thesis using c unfolding fr by (simp add: of_frame_def tr_frame_def of_tr_inst)
qed

section \<open>Administrative instructions and configurations\<close>

(* An administrative instruction that stands for a plain instruction. *)
lemma (in vec_complete) of_tr_admin_instr:
  assumes "wf_admininstr (admininstr_instr i)" "rt_ok i"
  shows "of_admin (Basic (tr_instr i)) = Some (admininstr_instr i)"
proof -
  have "wf_instr i" using assms(1) by (rule wf_admininstr_instr_inv)
  then have "of_instr (tr_instr i) = Some i" using assms(2) by (rule of_tr_instr)
  then show ?thesis by simp
qed

lemma admininstr_instr_of_a:
  "admininstr_instr (instr_of_a0 x0) = admininstr_sc0 x0"
  "admininstr_instr (instr_of_a1 x1) = admininstr_sc1 x1"
  "admininstr_instr (instr_of_a2 x2) = admininstr_sc2 x2"
  "admininstr_instr (instr_of_a3 x3) = admininstr_sc3 x3"
  "admininstr_instr (instr_of_a4 x4) = admininstr_sc4 x4"
  "admininstr_instr (instr_of_a5 x5) = admininstr_sc5 x5"
  "admininstr_instr (instr_of_a6 x6) = admininstr_sc6 x6"
        apply (cases x0; simp)
       apply (cases x1; simp)
      apply (cases x2; simp)
     apply (cases x3; simp)
    apply (cases x4; simp)
   apply (cases x5; simp)
  apply (cases x6; simp)
  done

(* The plain-instruction cases: [tr_admin a = Basic (tr_instr i)] with
   [admininstr_instr i = a]. *)
lemma (in vec_complete) of_tr_admin_via:
  assumes "admininstr_instr i = a" "tr_admin a = Basic (tr_instr i)" "wf_admininstr a" "rt_ok i"
  shows "of_admin (tr_admin a) = Some a"
proof -
  have "of_admin (Basic (tr_instr i)) = Some (admininstr_instr i)"
    using assms(1,3,4) by (intro of_tr_admin_instr) simp_all
  then show ?thesis using assms(1,2) by simp
qed

lemma (in back_complete) of_tr_admin_gen:
  shows "wf_admininstr a \<Longrightarrow> admin_ok a \<Longrightarrow> of_admin (tr_admin a) = Some a"
    and "wf_admininstr (admininstr_sc7 y) \<Longrightarrow> admin_ok7 y \<Longrightarrow> of_admin (tr_a7 y) = Some (admininstr_sc7 y)"
    and "wf_admininstr (admininstr_sc8 x) \<Longrightarrow> admin_ok8 x \<Longrightarrow> of_admin (tr_admin8 x) = Some (admininstr_sc8 x)"
proof (induction a and y and x)
  case (admininstr_sc0 x)
  show ?case by (rule of_tr_admin_via[OF admininstr_instr_of_a(1)]) (use admininstr_sc0.prems in simp_all)
next
  case (admininstr_sc1 x)
  show ?case by (rule of_tr_admin_via[OF admininstr_instr_of_a(2)]) (use admininstr_sc1.prems in simp_all)
next
  case (admininstr_sc2 x)
  show ?case by (rule of_tr_admin_via[OF admininstr_instr_of_a(3)]) (use admininstr_sc2.prems in simp_all)
next
  case (admininstr_sc3 x)
  show ?case by (rule of_tr_admin_via[OF admininstr_instr_of_a(4)]) (use admininstr_sc3.prems in simp_all)
next
  case (admininstr_sc4 x)
  show ?case by (rule of_tr_admin_via[OF admininstr_instr_of_a(5)]) (use admininstr_sc4.prems in simp_all)
next
  case (admininstr_sc5 x)
  show ?case by (rule of_tr_admin_via[OF admininstr_instr_of_a(6)]) (use admininstr_sc5.prems in simp_all)
next
  case (admininstr_sc6 x)
  show ?case by (rule of_tr_admin_via[OF admininstr_instr_of_a(7)]) (use admininstr_sc6.prems in simp_all)
next
  case (admininstr_sc7 x)
  have "of_admin (tr_a7 x) = Some (admininstr_sc7 x)"
    using admininstr_sc7.prems by (intro admininstr_sc7.IH) simp_all
  then show ?case by simp
next
  case (admininstr_st7_DATA_DROP y)
  have "of_admin (tr_admin (admininstr_sc7 (admininstr_st7_DATA_DROP y))) = Some (admininstr_sc7 (admininstr_st7_DATA_DROP y))"
    by (rule of_tr_admin_via[of "instr_sc7 (DATA_DROP y)"]) (use admininstr_st7_DATA_DROP.prems in simp_all)
  then show ?case by simp
next
  case (admininstr_st7_MEMORY_INIT y)
  have "of_admin (tr_admin (admininstr_sc7 (admininstr_st7_MEMORY_INIT y))) = Some (admininstr_sc7 (admininstr_st7_MEMORY_INIT y))"
    by (rule of_tr_admin_via[of "instr_sc6 (MEMORY_INIT y)"]) (use admininstr_st7_MEMORY_INIT.prems in simp_all)
  then show ?case by simp
next
  case admininstr_st7_MEMORY_COPY
  have "of_admin (tr_admin (admininstr_sc7 admininstr_st7_MEMORY_COPY)) = Some (admininstr_sc7 admininstr_st7_MEMORY_COPY)"
    by (rule of_tr_admin_via[of "instr_sc6 MEMORY_COPY"]) (use admininstr_st7_MEMORY_COPY.prems in simp_all)
  then show ?case by simp
next
  case admininstr_st7_MEMORY_FILL
  have "of_admin (tr_admin (admininstr_sc7 admininstr_st7_MEMORY_FILL)) = Some (admininstr_sc7 admininstr_st7_MEMORY_FILL)"
    by (rule of_tr_admin_via[of "instr_sc6 MEMORY_FILL"]) (use admininstr_st7_MEMORY_FILL.prems in simp_all)
  then show ?case by simp
next
  case admininstr_st7_TRAP
  then show ?case by simp
next
  case (CALL_ADDR a)
  then show ?case by simp
next
  case (admininstr_st7_REF_HOST_ADDR a)
  then show ?case by (simp add: tr_host_def of_hostref_complete)
next
  case (admininstr_st7_REF_FUNC_ADDR a)
  then show ?case by simp
next
  case (admininstr_sc8 x)
  have "of_admin (tr_admin8 x) = Some (admininstr_sc8 x)"
    using admininstr_sc8.prems by (intro admininstr_sc8.IH) simp_all
  then show ?case by simp
next
  case (FRAME_underscore n fr es)
  have w: "wf_frame fr" "wfl es" using FRAME_underscore.prems(1) by (simp_all add: wf_frame_iff)
  have c: "inst_canon (frame_MODULE fr)" "list_all admin_ok es" using FRAME_underscore.prems(2) by simp_all
  have f: "of_frame (tr_frame fr) = Some fr" by (rule of_tr_frame[OF w(1) c(1)])
  have e: "those (map of_admin (tr_admins es)) = Some es"
    unfolding tr_admins_def
  proof (rule those_map_comp_id)
    fix y assume y: "y \<in> set es"
    show "of_admin (tr_admin y) = Some y"
      using y w(2) c(2) by (intro FRAME_underscore.IH) (simp_all add: list_all_iff)
  qed
  show ?case using f e by simp
next
  case (LABEL_underscore n ins es)
  have w: "list_all wf_instr ins" "wfl es" using LABEL_underscore.prems(1) by (simp_all add: wf_label_iff)
  have c: "list_all rt_ok ins" "list_all admin_ok es" using LABEL_underscore.prems(2) by simp_all
  have e: "those (map of_admin (tr_admins es)) = Some es"
    unfolding tr_admins_def
  proof (rule those_map_comp_id)
    fix y assume y: "y \<in> set es"
    show "of_admin (tr_admin y) = Some y"
      using y w(2) c(2) by (intro LABEL_underscore.IH) (simp_all add: list_all_iff)
  qed
  have i: "of_instrs (tr_instrs ins) = Some ins"
    using of_tr_instrs_map[OF w(1) c(1)] by (simp add: of_instrs_def tr_instrs_def)
  have b: "those (map of_basic (map Basic (tr_instrs ins))) = Some (tr_instrs ins)"
    by (simp add: comp_def)
  show ?case using e i b by simp
qed

lemma (in back_complete) of_tr_admin: "wf_admininstr a \<Longrightarrow> admin_ok a \<Longrightarrow> of_admin (tr_admin a) = Some a"
  by (rule of_tr_admin_gen(1))

lemma (in back_complete) of_tr_admins: "wfl es \<Longrightarrow> list_all admin_ok es \<Longrightarrow> of_admins (tr_admins es) = Some es"
  unfolding of_admins_def tr_admins_def
  by (intro those_map_comp_id) (auto simp: list_all_iff intro: of_tr_admin)

(* The Rocq bridge's [of_config_complete], for configurations in canonical form. *)
theorem (in back_complete) of_tr_config:
  assumes "wf_config (mk_config (mk_state st fr) es)" "store_canon st" "inst_canon (frame_MODULE fr)"
    "list_all admin_ok es"
  shows "of_config (tr_config (mk_config (mk_state st fr) es)) = Some (mk_config (mk_state st fr) es)"
proof -
  have w: "wf_store st" "wf_frame fr" "wfl es" using assms(1) by (simp_all add: wf_config_simps wf_state_simps)
  show ?thesis
    using of_tr_store[OF w(1) assms(2)] of_tr_frame[OF w(2) assms(3)] of_tr_admins[OF w(3) assms(4)] by simp
qed

end
