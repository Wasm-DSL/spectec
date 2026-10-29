(* Reduction of back-translated configurations.

   A WasmCert configuration that back-translates to a well-typed SpecTec
   configuration [c] is the forward translation of [c]
   ([backtranslation_props.of_config_sound]), so the simulation of
   [reduction.v] applies to it: every SpecTec step of [c] is matched by
   WasmCert reduction of the original configuration, directly or eventually
   (after further SpecTec steps that restore the relation), outside the
   exceptions of [Step_exc]. *)

From Stdlib Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem.
From WasmSpectec Require wasm.
From WasmCertBridge Require Import translation backtranslation backtranslation_props reduction.

Module S := WasmSpectec.wasm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BackReduction.

Context `{hfc : host_function_class} `{ho : @host hfc memory_tr}.

Variable vec_instr : basic_instruction -> option S.instr.
Hypothesis vec_instr_sound :
  forall b i, vec_instr b = Some i -> tr_instr i = b /\ S.wf_instr i.

Lemma tr_cfg_of_config s f es c hs :
  of_config vec_instr s f es = Some c -> tr_cfg hs c = (hs, s, f, es).
Proof.
  case/(of_config_sound vec_instr_sound) => s' [f' [es' [-> [<- [<- [<- _]]]]]]. by [].
Qed.

Theorem Step_sim_back s f es c c' ts :
  of_config vec_instr s f es = Some c -> S.Step c c' -> S.Config_ok c ts ->
  (forall hs, reduce_trans (hs, s, f, es) (tr_cfg hs c')) \/
  (exists c'', S.Steps c' c'' /\ forall hs, reduce_trans (hs, s, f, es) (tr_cfg hs c'')) \/
  Step_exc c c'.
Proof.
  move=> Hc Hst Hok. case: (Step_sim_eventually Hst Hok) => [Hsim | [[c'' [Hs Hsim]] | Hexc]].
  - left => hs. rewrite -(tr_cfg_of_config hs Hc). exact: Hsim.
  - right; left. exists c''. split => // hs. rewrite -(tr_cfg_of_config hs Hc). exact: Hsim.
  - by right; right.
Qed.

End BackReduction.
