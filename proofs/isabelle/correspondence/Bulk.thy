(* Bulk: the bulk table and memory instructions (fill, copy, init) in the
   reduction simulation, one lemma per SpecTec rule (trap, zero, step).

   Both semantics unfold a bulk instruction into a single-element access and
   the rest of the bulk instruction; the steps correspond one to one.  The
   exception is WasmCert-Isabelle's [table.copy] (see DIFFERENCES.md): its
   rules test an unbound [nsrc] and an unbound table [ty], and check the source
   range against the destination table.  The simulation picks [nsrc] and [ty]
   (the destination table), so every SpecTec step is matched except a copy
   whose source range does not fit the destination table: [sim_table_copy_le]
   and [sim_table_copy_gt] require [wc].

   Premises left to the typing invariant: the i32 operands are 32-bit values,
   the filled value is a reference ([table.fill]) or an i32 ([memory.fill]),
   and the data bytes are bytes ([memory.init]). *)
theory Bulk
  imports Reduction
begin

section \<open>Bulk table instructions\<close>

lemma nat_of_int_false[simp]: "nat_of_int (wasm_bool False) = 0"
  using nat_of_int_tr_i32[of "mk_uN 0"] by simp

lemma eval_val_2nd:
  "reduce_trans (St, Fr, ($EConstNum c) # tr_admin (admininstr_val v) # es) (St, Fr, ($EConstNum c) # ($C (tr_val v)) # es)"
  using eval_val[of St Fr "[V_num c]" v es] by simp

lemma table_fill_eval:
  "reduce_trans (tr_store s, tr_frame f, tr_admins [i32c i, admininstr_val v, i32c n, admininstr_sc5 (admininstr_st5_TABLE_FILL x)])
                (tr_store s, tr_frame f, [$EConstNum (ConstInt32 (tr_i32 i)), ($C (tr_val v)), $EConstNum (ConstInt32 (tr_i32 n)), $Table_fill (un x)])"
  using eval_val_2nd[of "tr_store s" "tr_frame f" "ConstInt32 (tr_i32 i)" v] by simp

lemma sim_table_fill_trap:
  assumes t: "fun_table (mk_state s f) x ti" and v: "tr_val v = V_ref vr"
    and b: "un i < 2 ^ 32" "n < 2 ^ 32" "length (REFS ti) < un i + n"
  shows "sim (mk_config (mk_state s f) [i32c i, admininstr_val v, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_FILL x)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "ti = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using t by (rule fun_table_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 i)), ($C (V_ref vr)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Table_fill (un x)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.table_fill_trap[OF stab_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl]) (use x1 b in \<open>simp add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_rt[OF table_fill_eval wsim_step[OF st[folded v] wsim_refl[OF nls_refl]]] by simp
qed

lemma sim_table_fill_zero:
  assumes t: "fun_table (mk_state s f) x ti" and v: "tr_val v = V_ref vr"
    and b: "un i < 2 ^ 32" "un i \<le> length (REFS ti)"
  shows "sim (mk_config (mk_state s f) [i32c i, admininstr_val v, i32c (mk_uN 0), admininstr_sc5 (admininstr_st5_TABLE_FILL x)])
             (mk_config (mk_state s f) [])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "ti = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using t by (rule fun_table_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 i)), ($C (V_ref vr)), $EConstNum (ConstInt32 (tr_i32 (mk_uN 0))), $Table_fill (un x)]
              (tr_store s) (tr_frame f) []"
    by (rule reduce.table_fill_done[OF stab_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl]) (use x1 b in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_rt[OF table_fill_eval wsim_step[OF st[folded v] wsim_refl[OF nls_refl]]] by simp
qed

lemma sim_table_fill_succ:
  assumes t: "fun_table (mk_state s f) x ti" and v: "tr_val v = V_ref vr"
    and b: "un i < 2 ^ 32" "n < 2 ^ 32" "n \<noteq> 0" "un i + n \<le> length (REFS ti)"
  shows "sim (mk_config (mk_state s f) [i32c i, admininstr_val v, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_FILL x)])
             (mk_config (mk_state s f) [i32c i, admininstr_val v, admininstr_sc5 (admininstr_st5_TABLE_SET x),
                                         i32c (mk_uN (un i + 1)), admininstr_val v, i32c (mk_uN (n - 1)),
                                         admininstr_sc5 (admininstr_st5_TABLE_FILL x)])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "ti = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using t by (rule fun_table_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 i)), ($C (V_ref vr)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Table_fill (un x)]
              (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 i)), ($C (V_ref vr)), $Table_set (un x), $EConstNum (ConstInt32 (int_of_nat (un i + 1))),
               ($C (V_ref vr)), $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Table_fill (un x)]"
    by (rule reduce.table_fill[OF stab_ind_tr[OF x1(2)] HOL.refl]) (use x1 b in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  have nn: "nls [$EConstNum (ConstInt32 (tr_i32 i)), ($C (tr_val v)), $Table_set (un x), $EConstNum (ConstInt32 (int_of_nat (un i + 1))),
                 ($C (tr_val v)), $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Table_fill (un x)]
                (tr_admins [i32c i, admininstr_val v, admininstr_sc5 (admininstr_st5_TABLE_SET x),
                            i32c (mk_uN (un i + 1)), admininstr_val v, i32c (mk_uN (n - 1)), admininstr_sc5 (admininstr_st5_TABLE_FILL x)])"
    by (simp add: nl_val)
  show ?thesis unfolding sim_def using wsim_rt[OF table_fill_eval wsim_step[OF st[folded v] wsim_refl[OF nn]]] by simp
qed

(* table.copy.  WasmCert-Isabelle's rules bind [nrsc] but test the unbound [nsrc],
   and test [(tabs s)!ty] for an unbound [ty] (see DIFFERENCES.md).  Choosing
   [nsrc] and [ty] suitably matches every SpecTec step, except that a copy
   needs its source range to fit the destination table ([wc]). *)
lemma sim_table_copy_trap:
  assumes tx: "fun_table (mk_state s f) x tx" and ty: "fun_table (mk_state s f) y ty"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_COPY x y)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "tx = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using tx by (rule fun_table_E)
  obtain y1: "TABLES (frame_MODULE f) ! un y < length (store_TABLES s)" "un y < length (TABLES (frame_MODULE f))"
      "ty = store_TABLES s ! (TABLES (frame_MODULE f) ! un y)"
    using ty by (rule fun_table_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))),
               $Table_copy (un x) (un y)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.table_copy_trap[OF stab_ind_tr[OF x1(2)] HOL.refl stab_ind_tr[OF y1(2)] HOL.refl HOL.refl HOL.refl HOL.refl,
             where nsrc = "Suc (length (REFS tx))"])
       (use x1 in simp)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_table_copy_zero:
  assumes tx: "fun_table (mk_state s f) x tx" and ty: "fun_table (mk_state s f) y ty"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "un j \<le> length (REFS tx)"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN 0), admininstr_sc5 (admininstr_st5_TABLE_COPY x y)])
             (mk_config (mk_state s f) [])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "tx = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using tx by (rule fun_table_E)
  obtain y1: "TABLES (frame_MODULE f) ! un y < length (store_TABLES s)" "un y < length (TABLES (frame_MODULE f))"
      "ty = store_TABLES s ! (TABLES (frame_MODULE f) ! un y)"
    using ty by (rule fun_table_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN 0))),
               $Table_copy (un x) (un y)]
              (tr_store s) (tr_frame f) []"
    by (rule reduce.table_copy_done[OF stab_ind_tr[OF x1(2)] HOL.refl stab_ind_tr[OF y1(2)] HOL.refl HOL.refl HOL.refl HOL.refl,
             where nsrc = 0 and ty = "TABLES (frame_MODULE f) ! un x"])
       (use x1 b in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_table_copy_le:
  assumes tx: "fun_table (mk_state s f) x tx" and ty: "fun_table (mk_state s f) y ty"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32" "n \<noteq> 0" "un j + n \<le> length (REFS tx)" "un j \<le> un i"
    and wc: "un i + n \<le> length (REFS tx)"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_COPY x y)])
             (mk_config (mk_state s f) [i32c j, i32c i, admininstr_sc5 (admininstr_st5_TABLE_GET y), admininstr_sc5 (admininstr_st5_TABLE_SET x),
                                         i32c (mk_uN (un j + 1)), i32c (mk_uN (un i + 1)), i32c (mk_uN (n - 1)),
                                         admininstr_sc5 (admininstr_st5_TABLE_COPY x y)])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "tx = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using tx by (rule fun_table_E)
  obtain y1: "TABLES (frame_MODULE f) ! un y < length (store_TABLES s)" "un y < length (TABLES (frame_MODULE f))"
      "ty = store_TABLES s ! (TABLES (frame_MODULE f) ! un y)"
    using ty by (rule fun_table_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))),
               $Table_copy (un x) (un y)]
              (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $Table_get (un y), $Table_set (un x),
               $EConstNum (ConstInt32 (int_of_nat (un j + 1))), $EConstNum (ConstInt32 (int_of_nat (un i + 1))),
               $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Table_copy (un x) (un y)]"
    by (rule reduce.table_copy_1[OF stab_ind_tr[OF x1(2)] HOL.refl stab_ind_tr[OF y1(2)] HOL.refl, where ty = "TABLES (frame_MODULE f) ! un x"])
       (use x1 b wc in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_table_copy_gt:
  assumes tx: "fun_table (mk_state s f) x tx" and ty: "fun_table (mk_state s f) y ty"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32" "n \<noteq> 0" "un j + n \<le> length (REFS tx)" "un i < un j"
    and wc: "un i + n \<le> length (REFS tx)"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_COPY x y)])
             (mk_config (mk_state s f) [i32c (mk_uN (un j + n - 1)), i32c (mk_uN (un i + n - 1)),
                                         admininstr_sc5 (admininstr_st5_TABLE_GET y), admininstr_sc5 (admininstr_st5_TABLE_SET x),
                                         i32c j, i32c i, i32c (mk_uN (n - 1)), admininstr_sc5 (admininstr_st5_TABLE_COPY x y)])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "tx = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using tx by (rule fun_table_E)
  obtain y1: "TABLES (frame_MODULE f) ! un y < length (store_TABLES s)" "un y < length (TABLES (frame_MODULE f))"
      "ty = store_TABLES s ! (TABLES (frame_MODULE f) ! un y)"
    using ty by (rule fun_table_E)
  have e: "un j + n - 1 = un j + (n - 1)" "un i + n - 1 = un i + (n - 1)" using b(4) by simp_all
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))),
               $Table_copy (un x) (un y)]
              (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (int_of_nat (un j + (n - 1)))), $EConstNum (ConstInt32 (int_of_nat (un i + (n - 1)))),
               $Table_get (un y), $Table_set (un x),
               $EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)),
               $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Table_copy (un x) (un y)]"
    by (rule reduce.table_copy_2[OF stab_ind_tr[OF x1(2)] HOL.refl stab_ind_tr[OF y1(2)] HOL.refl, where ty = "TABLES (frame_MODULE f) ! un x"])
       (use x1 b wc in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] e by simp
qed

lemma fun_elem_E:
  assumes "fun_elem (mk_state s f) y ei"
  obtains "ELEMS (frame_MODULE f) ! un y < length (store_ELEMS s)" "un y < length (ELEMS (frame_MODULE f))"
    "ei = store_ELEMS s ! (ELEMS (frame_MODULE f) ! un y)"
  using assms by (auto elim: fun_elem.cases)

lemma sim_table_init_trap:
  assumes tx: "fun_table (mk_state s f) x tx" and e: "fun_elem (mk_state s f) y ei"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32"
    and c: "length (eleminst_REFS ei) < un i + n \<or> length (REFS tx) < un j + n"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_INIT x y)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "tx = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using tx by (rule fun_table_E)
  obtain e1: "ELEMS (frame_MODULE f) ! un y < length (store_ELEMS s)" "un y < length (ELEMS (frame_MODULE f))"
      "ei = store_ELEMS s ! (ELEMS (frame_MODULE f) ! un y)"
    using e by (rule fun_elem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))),
               $Table_init (un x) (un y)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.table_init_trap[OF stab_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl HOL.refl HOL.refl HOL.refl])
       (use x1 e1 b c in \<open>auto simp: nat_of_int_tr_i32 tr_eleminst_def\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_table_init_zero:
  assumes tx: "fun_table (mk_state s f) x tx" and e: "fun_elem (mk_state s f) y ei"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "un i \<le> length (eleminst_REFS ei)" "un j \<le> length (REFS tx)"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN 0), admininstr_sc5 (admininstr_st5_TABLE_INIT x y)])
             (mk_config (mk_state s f) [])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "tx = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using tx by (rule fun_table_E)
  obtain e1: "ELEMS (frame_MODULE f) ! un y < length (store_ELEMS s)" "un y < length (ELEMS (frame_MODULE f))"
      "ei = store_ELEMS s ! (ELEMS (frame_MODULE f) ! un y)"
    using e by (rule fun_elem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN 0))),
               $Table_init (un x) (un y)]
              (tr_store s) (tr_frame f) []"
    by (rule reduce.table_init_done[OF stab_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl HOL.refl HOL.refl HOL.refl])
       (use x1 e1 b in \<open>simp_all add: nat_of_int_tr_i32 tr_eleminst_def\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_table_init_succ:
  assumes tx: "fun_table (mk_state s f) x tx" and e: "fun_elem (mk_state s f) y ei"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32" "n \<noteq> 0"
      "un i + n \<le> length (eleminst_REFS ei)" "un j + n \<le> length (REFS tx)"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc5 (admininstr_st5_TABLE_INIT x y)])
             (mk_config (mk_state s f) [i32c j, admininstr_ref (eleminst_REFS ei ! un i), admininstr_sc5 (admininstr_st5_TABLE_SET x),
                                         i32c (mk_uN (un j + 1)), i32c (mk_uN (un i + 1)), i32c (mk_uN (n - 1)),
                                         admininstr_sc5 (admininstr_st5_TABLE_INIT x y)])"
proof -
  obtain x1: "TABLES (frame_MODULE f) ! un x < length (store_TABLES s)" "un x < length (TABLES (frame_MODULE f))"
      "tx = store_TABLES s ! (TABLES (frame_MODULE f) ! un x)"
    using tx by (rule fun_table_E)
  obtain e1: "ELEMS (frame_MODULE f) ! un y < length (store_ELEMS s)" "un y < length (ELEMS (frame_MODULE f))"
      "ei = store_ELEMS s ! (ELEMS (frame_MODULE f) ! un y)"
    using e by (rule fun_elem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))),
               $Table_init (un x) (un y)]
              (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), ($C (V_ref (tr_ref (eleminst_REFS ei ! un i)))), $Table_set (un x),
               $EConstNum (ConstInt32 (int_of_nat (un j + 1))), $EConstNum (ConstInt32 (int_of_nat (un i + 1))),
               $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Table_init (un x) (un y)]"
    by (rule reduce.table_init[OF stab_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl])
       (use x1 e1 b in \<open>simp_all add: nat_of_int_tr_i32 tr_eleminst_def\<close>)
  have nn: "nls [$EConstNum (ConstInt32 (tr_i32 j)), ($C (V_ref (tr_ref (eleminst_REFS ei ! un i)))), $Table_set (un x),
                 $EConstNum (ConstInt32 (int_of_nat (un j + 1))), $EConstNum (ConstInt32 (int_of_nat (un i + 1))),
                 $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Table_init (un x) (un y)]
                (tr_admins [i32c j, admininstr_ref (eleminst_REFS ei ! un i), admininstr_sc5 (admininstr_st5_TABLE_SET x),
                            i32c (mk_uN (un j + 1)), i32c (mk_uN (un i + 1)), i32c (mk_uN (n - 1)),
                            admininstr_sc5 (admininstr_st5_TABLE_INIT x y)])"
    using nl_ref[of "eleminst_REFS ei ! un i"] by (simp add: v_to_e_def)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nn]] by simp
qed

section \<open>Bulk memory instructions\<close>

lemma mk_uN_un[simp]: "mk_uN (un u) = u"
  by (cases u) simp

lemma tr_i32_mod32[simp]: "tr_i32 (mk_uN (k mod 4294967296)) = tr_i32 (mk_uN k)"
  by (simp add: tr_i32_def of_nat_mod_32)

lemma tr_i32_iadd1: "tr_i32 (iadd_underscore 32 i (mk_uN 1)) = tr_i32 (mk_uN (un i + 1))"
  by (cases i) simp

termination proj_byte_0 by lexicographic_order

(* The byte-sized accesses that SpecTec's bulk memory rules unfold into. *)
lemma tr_memarg0[simp]: "tr_align memarg0 = 0" "tr_offset memarg0 = 0"
  by (simp_all add: tr_align_def tr_offset_def memarg0_def)

lemma tr_tp_8[simp]: "tr_tp (mk_sz 8) = Tp_i8"
  by (simp add: tr_tp_def tp_of_bits_def)

lemma nat_of_uint8_tr_byte: "proj_byte_0 b < 256 \<Longrightarrow> nat_of_uint8 (tr_byte b) = proj_byte_0 b"
  by (cases b) (simp add: byte_of_nat_def uint8_of_nat.abs_eq nat_of_uint8.abs_eq unat_of_nat)

lemma fun_data_E:
  assumes "fun_data (mk_state s f) x di"
  obtains "DATAS (frame_MODULE f) ! un x < length (store_DATAS s)" "un x < length (DATAS (frame_MODULE f))"
    "di = store_DATAS s ! (DATAS (frame_MODULE f) ! un x)"
  using assms by (auto elim: fun_data.cases)

lemma sim_memory_fill_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and b: "un i < 2 ^ 32" "n < 2 ^ 32" "length (BYTES mi) < un i + n"
  shows "sim (mk_config (mk_state s f) [i32c i, i32c c, i32c (mk_uN n), admininstr_sc7 admininstr_st7_MEMORY_FILL])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 c)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_fill]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.memory_fill_trap[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl]) (use x1 b in \<open>simp add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_memory_fill_zero:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and b: "un i < 2 ^ 32" "un i \<le> length (BYTES mi)"
  shows "sim (mk_config (mk_state s f) [i32c i, i32c c, i32c (mk_uN 0), admininstr_sc7 admininstr_st7_MEMORY_FILL])
             (mk_config (mk_state s f) [])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 c)), $EConstNum (ConstInt32 (tr_i32 (mk_uN 0))), $Memory_fill]
              (tr_store s) (tr_frame f) []"
    by (rule reduce.memory_fill_done[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl]) (use x1 b in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_memory_fill_succ:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi"
    and b: "un i < 2 ^ 32" "n < 2 ^ 32" "n \<noteq> 0" "un i + n \<le> length (BYTES mi)"
  shows "sim (mk_config (mk_state s f) [i32c i, i32c c, i32c (mk_uN n), admininstr_sc7 admininstr_st7_MEMORY_FILL])
             (mk_config (mk_state s f) [i32c i, i32c c, admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) memarg0),
                                         i32c (iadd_underscore 32 i (mk_uN 1)), i32c c, i32c (mk_uN (n - 1)),
                                         admininstr_sc7 admininstr_st7_MEMORY_FILL])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 c)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_fill]
              (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 c)), $Store T_i32 (Some Tp_i8) 0 0,
               $EConstNum (ConstInt32 (int_of_nat (un i + 1))), $EConstNum (ConstInt32 (tr_i32 c)),
               $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Memory_fill]"
    by (rule reduce.memory_fill[OF smem_ind_tr[OF x1(2)] HOL.refl]) (use x1 b in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_i32_iadd1)
qed

lemma sim_memory_copy_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32"
    and c: "length (BYTES mi) < un i + n \<or> length (BYTES mi) < un j + n"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc7 admininstr_st7_MEMORY_COPY])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_copy]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.memory_copy_trap[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl HOL.refl])
       (use x1 b c in \<open>auto simp: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_memory_copy_zero:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "un i \<le> length (BYTES mi)" "un j \<le> length (BYTES mi)"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN 0), admininstr_sc7 admininstr_st7_MEMORY_COPY])
             (mk_config (mk_state s f) [])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN 0))), $Memory_copy]
              (tr_store s) (tr_frame f) []"
    by (rule reduce.memory_copy_done[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl HOL.refl])
       (use x1 b in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_memory_copy_le:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32" "n \<noteq> 0"
      "un i + n \<le> length (BYTES mi)" "un j + n \<le> length (BYTES mi)" "un j \<le> un i"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc7 admininstr_st7_MEMORY_COPY])
             (mk_config (mk_state s f) [i32c j, i32c i,
                admininstr_sc6 (admininstr_st6_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) isabelle_reference_output_wasm2.U))) memarg0),
                admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) memarg0),
                i32c (iadd_underscore 32 j (mk_uN 1)), i32c (iadd_underscore 32 i (mk_uN 1)), i32c (mk_uN (n - 1)),
                admininstr_sc7 admininstr_st7_MEMORY_COPY])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_copy]
              (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $Load T_i32 (Some (Tp_i8, Wasm_Ast.U)) 0 0,
               $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 (int_of_nat (un j + 1))),
               $EConstNum (ConstInt32 (int_of_nat (un i + 1))), $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Memory_copy]"
    by (rule reduce.memory_copy_1[OF smem_ind_tr[OF x1(2)] HOL.refl]) (use x1 b in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_i32_iadd1 tr_tp_def tp_of_bits_def)
qed

lemma sim_memory_copy_gt:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32" "n \<noteq> 0"
      "un i + n \<le> length (BYTES mi)" "un j + n \<le> length (BYTES mi)" "un i < un j"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc7 admininstr_st7_MEMORY_COPY])
             (mk_config (mk_state s f) [i32c (mk_uN (un j + n - 1)), i32c (mk_uN (un i + n - 1)),
                admininstr_sc6 (admininstr_st6_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) isabelle_reference_output_wasm2.U))) memarg0),
                admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) memarg0),
                i32c j, i32c i, i32c (mk_uN (n - 1)), admininstr_sc7 admininstr_st7_MEMORY_COPY])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have e: "un j + n - 1 = un j + (n - 1)" "un i + n - 1 = un i + (n - 1)" using b(4) by simp_all
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_copy]
              (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (int_of_nat (un j + (n - 1)))), $EConstNum (ConstInt32 (int_of_nat (un i + (n - 1)))),
               $Load T_i32 (Some (Tp_i8, Wasm_Ast.U)) 0 0, $Store T_i32 (Some Tp_i8) 0 0,
               $EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)),
               $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Memory_copy]"
    by (rule reduce.memory_copy_2[OF smem_ind_tr[OF x1(2)] HOL.refl]) (use x1 b in \<open>simp_all add: nat_of_int_tr_i32\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] e by (simp add: tr_tp_def tp_of_bits_def)
qed

lemma sim_memory_init_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and d: "fun_data (mk_state s f) x di"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32"
    and c: "length (datainst_BYTES di) < un i + n \<or> length (BYTES mi) < un j + n"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc7 (admininstr_st7_MEMORY_INIT x)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  obtain d1: "DATAS (frame_MODULE f) ! un x < length (store_DATAS s)" "un x < length (DATAS (frame_MODULE f))"
      "di = store_DATAS s ! (DATAS (frame_MODULE f) ! un x)"
    using d by (rule fun_data_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_init (un x)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.memory_init_trap[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl HOL.refl HOL.refl HOL.refl])
       (use x1 d1 b c in \<open>auto simp: nat_of_int_tr_i32 tr_datainst_def\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_memory_init_zero:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and d: "fun_data (mk_state s f) x di"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "un i \<le> length (datainst_BYTES di)" "un j \<le> length (BYTES mi)"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN 0), admininstr_sc7 (admininstr_st7_MEMORY_INIT x)])
             (mk_config (mk_state s f) [])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  obtain d1: "DATAS (frame_MODULE f) ! un x < length (store_DATAS s)" "un x < length (DATAS (frame_MODULE f))"
      "di = store_DATAS s ! (DATAS (frame_MODULE f) ! un x)"
    using d by (rule fun_data_E)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN 0))), $Memory_init (un x)]
              (tr_store s) (tr_frame f) []"
    by (rule reduce.memory_init_done[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl HOL.refl HOL.refl HOL.refl])
       (use x1 d1 b in \<open>simp_all add: nat_of_int_tr_i32 tr_datainst_def\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

(* The copied byte is below 256 by store validity. *)
lemma sim_memory_init_succ:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and d: "fun_data (mk_state s f) x di"
    and b: "un j < 2 ^ 32" "un i < 2 ^ 32" "n < 2 ^ 32" "n \<noteq> 0"
      "un i + n \<le> length (datainst_BYTES di)" "un j + n \<le> length (BYTES mi)"
    and bt: "proj_byte_0 (datainst_BYTES di ! un i) < 256"
  shows "sim (mk_config (mk_state s f) [i32c j, i32c i, i32c (mk_uN n), admininstr_sc7 (admininstr_st7_MEMORY_INIT x)])
             (mk_config (mk_state s f) [i32c j, i32c (mk_uN (proj_byte_0 (datainst_BYTES di ! un i))),
                admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) memarg0),
                i32c (iadd_underscore 32 j (mk_uN 1)), i32c (iadd_underscore 32 i (mk_uN 1)), i32c (mk_uN (n - 1)),
                admininstr_sc7 (admininstr_st7_MEMORY_INIT x)])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  obtain d1: "DATAS (frame_MODULE f) ! un x < length (store_DATAS s)" "un x < length (DATAS (frame_MODULE f))"
      "di = store_DATAS s ! (DATAS (frame_MODULE f) ! un x)"
    using d by (rule fun_data_E)
  have i: "un i < length (datainst_BYTES di)" using b(4,5) by simp
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 j)), $EConstNum (ConstInt32 (tr_i32 i)), $EConstNum (ConstInt32 (tr_i32 (mk_uN n))), $Memory_init (un x)]
              (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (int_of_nat (un j))), $EConstNum (ConstInt32 (int_of_nat (proj_byte_0 (datainst_BYTES di ! un i)))),
               $Store T_i32 (Some Tp_i8) 0 0, $EConstNum (ConstInt32 (int_of_nat (un j + 1))),
               $EConstNum (ConstInt32 (int_of_nat (un i + 1))), $EConstNum (ConstInt32 (int_of_nat (n - 1))), $Memory_init (un x)]"
    by (rule reduce.memory_init[OF smem_ind_tr[OF x1(2)] HOL.refl HOL.refl HOL.refl])
       (use x1 d1 b bt i in \<open>simp_all add: nat_of_int_tr_i32 tr_datainst_def nat_of_uint8_tr_byte\<close>)
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_i32_iadd1)
qed

end
