From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.


Import RecordSetNotations.

From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping type_preservation_pure extension_lemmas.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat.
Open Scope wasm_scope.
Import ListNotations.

Definition ratdiv8 nt :=
  (rat.divq (ssrint.Posz nt)
	(ssralg.GRing.natmul
	(V:=ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule rat.rat_rat__canonical__GRing_PzSemiRing)
	(ssralg.GRing.one rat.rat_rat__canonical__GRing_PzSemiRing) 8)).


Axiom nbytes_len: forall v_nt v_c,
  length (nbytes_ v_nt v_c) =
  (Nat.divmod (the (res_size (valtype_numtype v_nt))) 7 0 7).1.

Axiom ibytes_len: forall size v_n v_c,
  length (ibytes_ v_n (wrap__ size v_n v_c)) = 
		(Nat.divmod v_n 7 0 7).1.

Axiom nbytes_len': forall v_nt v_c,
  size (nbytes_ v_nt v_c) = ratdiv8 ((!( res_size (valtype_numtype v_nt)))).

Axiom ibytes_len': forall s v_n v_c,
  seq.size (ibytes_ v_n (wrap__ s v_n v_c)) = ratdiv8 v_n.
  

