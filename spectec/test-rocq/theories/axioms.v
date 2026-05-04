From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping type_preservation_pure extension_lemmas.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Import ListNotations.


Axiom nbytes_len: forall v_nt v_c,
    length (nbytes_ v_nt v_c) =
    (Nat.divmod (the (res_size (valtype_numtype v_nt))) 7 0 7).1.

Axiom ibytes_len: forall size v_n v_c,
    length (ibytes_ v_n (wrap__ size v_n v_c)) = 
			(Nat.divmod v_n 7 0 7).1.