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

(* Likewise `ibits_` and `inv_ibits_` are mutually inverse between iN(N) and
   bit sequences of length N.  The bits must be well-formed (0 or 1), since
   `ibits_` only ever produces such bits. *)
Axiom ibits_inv : forall (v_N : res_N) (bs : seq bit),
  (|bs|) = v_N ->
  List.Forall (fun b => wf_bit b) bs ->
  ibits_ v_N (inv_ibits_ v_N bs) = bs.


(* The float comparisons `feq_` .. `fge_` are uninterpreted Axioms in wasm.v
   returning a u32.  In the specification they return a boolean, i.e. 0 or 1. *)
Axiom feq_bit : forall (v_N : res_N) (a b : fN), wf_uN 1 (feq_ v_N a b).
Axiom fne_bit : forall (v_N : res_N) (a b : fN), wf_uN 1 (fne_ v_N a b).
Axiom flt_bit : forall (v_N : res_N) (a b : fN), wf_uN 1 (flt_ v_N a b).
Axiom fgt_bit : forall (v_N : res_N) (a b : fN), wf_uN 1 (fgt_ v_N a b).
Axiom fle_bit : forall (v_N : res_N) (a b : fN), wf_uN 1 (fle_ v_N a b).
Axiom fge_bit : forall (v_N : res_N) (a b : fN), wf_uN 1 (fge_ v_N a b).
(* `ishl_` / `ishr_` are uninterpreted builtins in wasm.v, typed as taking a
   u32 shift amount.  $binop_ however passes them the full operand (a 64-bit
   value for I64 SHL / SHR; Wasm 3.0 does the same), for which ishl__is_wf /
   ishr__is_wf do not apply.  By the specification the shift amount is taken
   modulo N, so the result is in iN(N) whatever the shift amount. *)
Axiom ishl_wf : forall (v_N : res_N) (i : iN) (k : u32),
  wf_uN v_N i -> wf_uN v_N (ishl_ v_N i k).
Axiom ishr_wf : forall (v_N : res_N) (v_sx : sx) (i : iN) (k : u32),
  wf_uN v_N i -> wf_uN v_N (ishr_ v_N v_sx i k).
