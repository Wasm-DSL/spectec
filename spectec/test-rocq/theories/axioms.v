From Stdlib Require Import String List Unicode.Utf8 NArith Arith QArith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.


Import RecordSetNotations.

From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping type_preservation_pure extension_lemmas.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Open Scope wasm_scope.
Import ListNotations.

Axiom nbytes_len: forall v_nt v_c,
  length (nbytes_ v_nt v_c) =
  (Nat.divmod (the (res_size (valtype_numtype v_nt))) 7 0 7).1.

Axiom ibytes_len: forall size v_n v_c,
  length (ibytes_ v_n (wrap__ size v_n v_c)) = 
		(Nat.divmod v_n 7 0 7).1.

Axiom nbytes_len': forall v_nt v_c,
  |nbytes_ v_nt v_c| = ((!( res_size (valtype_numtype v_nt))) / 8)%Q.

Axiom ibytes_len': forall s v_n v_c,
  |ibytes_ v_n (wrap__ s v_n v_c)| = (v_n / 8)%Q.
  


Axiom vbytes_len': forall v_vt v_c,
  |vbytes_ v_vt v_c| = ((!( res_size (valtype_vectype v_vt))) / 8)%Q.

Axiom ibytes_len'': forall v_n v_c,
  |ibytes_ v_n v_c| = (v_n / 8)%Q.

(* `truncz` (truncation of a rational towards zero) is an uninterpreted Axiom
   in wasm.v.  On a quotient of two integers - the only way the integer
   operators of the spec ever use it - it coincides with Z.quot. *)
Axiom truncz_quot : forall (a b : Z), b <> 0%Z ->
  truncz (inject_Z a / inject_Z b)%Q = Z.quot a b.

(* `lanes_` is an uninterpreted Axiom in wasm.v.  By its definition in the
   specification it splits a 128-bit vector into exactly `dim` lanes. *)
Axiom lanes_len : forall (lt : lanetype) (v_N : N) (c : vec_),
  (|lanes_ (X lt (mk_dim v_N)) c|) = v_N.

(* `nbytes_`/`ibytes_` and their inverses `inv_nbytes_`/`inv_ibytes_` are
   uninterpreted Axioms in wasm.v.  In the specification they are mutually
   inverse bijections between values and byte sequences of the right width. *)
Axiom nbytes_inv : forall (nt : numtype) (bs : seq byte),
  (|bs|) = ((((!(res_size (valtype_numtype nt))) : Q) / (8%num : Q))%Q : N) ->
  nbytes_ nt (inv_nbytes_ nt bs) = bs.

Axiom ibytes_inv : forall (v_N : res_N) (bs : seq byte),
  (|bs|) = (((v_N : Q) / (8%num : Q))%Q : N) ->
  ibytes_ v_N (inv_ibytes_ v_N bs) = bs.

Axiom vbytes_inv : forall (vt : vectype) (bs : seq byte),
  (|bs|) = ((((!(res_size (valtype_vectype vt))) : Q) / (8%num : Q))%Q : N) ->
  vbytes_ vt (inv_vbytes_ vt bs) = bs.
