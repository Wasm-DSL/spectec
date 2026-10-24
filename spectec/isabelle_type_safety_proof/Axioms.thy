theory Axioms
(* Imported Code *)
	imports isabelle_reference_output_wasm2 

begin

(*The byte encoders are uninterpreted in the generated theory, so nothing fixes the
  length of their output. These axioms mirror `nbytes_len'`, `ibytes_len''` and
  `vbytes_len'` in rocq/axioms.v (`ibytes_len''` also covers Rocq's `ibytes_len'`).*)
axiomatization where
  nbytes_length: "length (nbytes_underscore nt c) = the (size (valtype_numtype nt)) div 8" and
  ibytes_length: "length (ibytes_underscore v_N x) = v_N div 8" and
  vbytes_length: "length (vbytes_underscore vt v) = the (size (valtype_vectype vt)) div 8"

axiomatization where truncz_spec:
  "truncz x = x"

axiomatization where nbytes_inv:
  "length bs = the (size (valtype_numtype nt)) div 8 \<Longrightarrow>
   nbytes_underscore nt (inv_nbytes_underscore nt bs) = bs" 

axiomatization where ibytes_inv:
  "length bs = v_n div 8 \<Longrightarrow>
   ibytes_underscore v_n (inv_ibytes_underscore v_n bs) = bs"
  

axiomatization where vbytes_inv:
  "length bs = the (size (valtype_vectype nt)) div 8 \<Longrightarrow>
   vbytes_underscore nt (inv_vbytes_underscore nt bs) = bs" 
  

axiomatization where length_lanes:
  "length (lanes_underscore (X a (mk_dim d)) b) = d"
  

end