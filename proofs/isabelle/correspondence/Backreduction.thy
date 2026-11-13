(* Reduction of back-translated configurations.  Isabelle counterpart of
   ../wasmcert-rocq/backreduction.v.

   A WasmCert configuration that back-translates to a typed SpecTec configuration
   [c] agrees with the translation of [c] up to evaluated nulls
   ([of_config_sound], Backtranslation_Sound.thy).  The simulation of
   [Step_sim_eventually] (Step_Typing.thy) runs WasmCert from the translation of
   [c]; the commutation lemma ([nls_wsim], Null_Commute.thy) transfers it to the
   original configuration.  So every SpecTec step of [c] that is none of the named
   disagreements is matched by WasmCert reduction of the original configuration,
   directly or after further SpecTec steps.

   In the Rocq bridge the round trip is exact (WasmCert-Coq has one null form), so
   the last step is not needed there. *)
theory Backreduction
  imports Step_Typing Backtranslation_Sound Null_Commute
begin

locale back_sim = sim_all + back_sound

theorem (in back_sim) Step_sim_back:
  assumes oc: "of_config (st, fr, es) = Some (mk_config z ces)"
    and step: "Step (mk_config z ces) (mk_config z' ces')"
    and ok: "Config_ok (mk_config z ces) ts"
    and nd: "\<not> Exc z ces z' ces'"
  shows "wsim (st, fr, es) (tr_config (mk_config z' ces')) \<or>
         (\<exists>c''. Steps (mk_config z' ces') c'' \<and> wsim (st, fr, es) (tr_config c''))"
proof -
  obtain st' fr' where z: "z = mk_state st' fr'" and s: "tr_store st' = st" and f: "tr_frame fr' = fr"
    and n: "nls es (tr_admins ces)"
    using of_config_sound[OF oc] by auto
  have tr: "tr_config (mk_config z ces) = (st, fr, tr_admins ces)" using z s f by simp
  have move: "\<And>c''. sim (mk_config z ces) c'' \<Longrightarrow> wsim (st, fr, es) (tr_config c'')"
  proof -
    fix c'' assume "sim (mk_config z ces) c''"
    then have "wsim (st, fr, tr_admins ces) (tr_config c'')" using tr by (simp add: sim_def)
    then show "wsim (st, fr, es) (tr_config c'')" by (rule nls_wsim[OF _ n])
  qed
  show ?thesis using Step_sim_eventually[OF step ok nd] move by blast
qed

end
