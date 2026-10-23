theory Axioms
(* Imported Code *)
	imports isabelle_reference_output_wasm2 

begin

lemma truncz_spec:
  shows "truncz x = x"
  sorry

lemma nbytes_inv:
  assumes "length bs = the (size (valtype_numtype nt)) div 8"
  shows "nbytes_underscore nt (inv_nbytes_underscore nt bs) = bs" 
  sorry

lemma ibytes_inv:
  assumes "length bs = v_n div 8"
  shows "ibytes_underscore v_n (inv_ibytes_underscore v_n bs) = bs"
  sorry

lemma vbytes_inv:
  assumes "length bs = the (size (valtype_vectype nt)) div 8"
  shows "vbytes_underscore nt (inv_vbytes_underscore nt bs) = bs" 
  sorry

lemma length_lanes:
  shows "length (lanes_underscore (X a (mk_dim d)) b) = d"
  sorry

end