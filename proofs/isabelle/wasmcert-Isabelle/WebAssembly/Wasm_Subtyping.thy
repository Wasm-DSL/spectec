section \<open>Wasm Subtyping\<close>

theory Wasm_Subtyping imports Wasm_Ast begin

definition "limits_compat lt1 lt2 =
  ((l_min lt1) \<ge> (l_min lt2) \<and>
  pred_option (\<lambda>lt2_the. (case (l_max lt1) of
                            Some lt1_the \<Rightarrow> (lt1_the \<le> lt2_the)
                          | None \<Rightarrow> False)) (l_max lt2))"


definition t_subtyping :: "[t, t] \<Rightarrow> bool" ("_ '<t: _" 60) where
  "t_subtyping t1 t2 = (t1 = T_bot \<or> t1 = t2)"

definition t_list_subtyping :: "[t list, t list] \<Rightarrow> bool" ("_ '<ts: _" 60) where
  "t_list_subtyping t1s t2s = list_all2 t_subtyping t1s t2s"

definition instr_subtyping :: "[tf, tf] \<Rightarrow> bool" ("_ '<ti: _" 60) where
  "instr_subtyping tf1 tf2 \<equiv> \<exists> ts ts' tf1_dom_sub tf1_ran_sub.
    (tf.dom tf2) = ts@tf1_dom_sub
  \<and> (tf.ran tf2) = ts'@tf1_ran_sub
  \<and> t_list_subtyping ts ts'
  \<and> t_list_subtyping tf1_dom_sub (tf.dom tf1)
  \<and> t_list_subtyping (tf.ran tf1)(tf1_ran_sub)"


definition mem_subtyping :: "[mem_t, mem_t] \<Rightarrow> bool" where
"mem_subtyping t1 t2 = limits_compat t1 t2"
 
definition tab_subtyping :: "[tab_t, tab_t] \<Rightarrow> bool" where
"tab_subtyping t1 t2 = (case (t1, t2) of
  (T_tab lims1 tr1, T_tab lims2 tr2) \<Rightarrow> limits_compat lims1 lims2 \<and> tr1 = tr2) "

end