(* Both formalisations in one theory: the SpecTec-generated Wasm 2.0 semantics and
   WasmCert-Isabelle's definitions, plus WasmCert's typing lemmas
   (Wasm_Properties_Aux: composition, weakening, inversion) and its reduction
   lemmas (Wasm_Properties: reduction under evaluation contexts).

   Names declared by both are disambiguated by theory qualification, e.g.
   isabelle_reference_output_wasm2.U vs Wasm_Ast.U (signedness), and the types
   i32, i64, f32, f64, byte, sx, mut, eleminst, datainst. *)
theory Base
  imports
    "../type-soundness/isabelle_reference_output_wasm2"
    "../wasmcert-Isabelle/WebAssembly/Wasm"
    "../wasmcert-Isabelle/WebAssembly/Wasm_Properties_Aux"
    "../wasmcert-Isabelle/WebAssembly/Wasm_Properties"
begin

end
