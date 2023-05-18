open Reference_interpreter
open Source
open Al

let al_of_wasm_num n =
  let s = Values.string_of_num n in
  let t = Values.type_of_num n in
  match t with
  | I32Type | I64Type ->
      ConstructV ("const", [ WasmTypeV (NumType t); IntV (int_of_string s) ])
  | F32Type | F64Type ->
      ConstructV ("const", [ WasmTypeV (NumType t); FloatV (float_of_string s) ])

let al_of_wasm_blocktype types wtype =
  match wtype with
  | Ast.VarBlockType idx ->
    let Types.FuncType (param_types, result_types) = (Lib.List32.nth types idx.it).it in
    let result_type_to_listV result_type =
      ListV (List.map (fun t -> WasmTypeV t) result_type |> Array.of_list)
    in
    ArrowV(result_type_to_listV param_types, result_type_to_listV result_types)
  | Ast.ValBlockType None -> ArrowV(ListV [||], ListV [||])
  | Ast.ValBlockType (Some val_type) -> ArrowV(ListV [||], ListV[| WasmTypeV val_type |])

let rec al_of_wasm_instr types winstr =
  let f_i32 f i32 = ConstructV (f, [ IntV (Int32.to_int i32.it) ]) in

  match winstr.it with
  (* wasm values *)
  | Ast.Const num -> al_of_wasm_num num.it
  | Ast.RefNull t -> ConstructV ("ref.null", [ WasmTypeV (RefType t) ])
  (* wasm instructions *)
  | Ast.Nop -> ConstructV ("nop", [])
  | Ast.Drop -> ConstructV ("drop", [])
  | Ast.Binary (Values.I32 Ast.I32Op.Add) ->
      ConstructV
        ("binop", [ WasmTypeV (Types.NumType Types.I32Type); StringV "Add" ])
  | Ast.Binary (Values.I32 Ast.I32Op.Sub) ->
      ConstructV
        ("binop", [ WasmTypeV (Types.NumType Types.I32Type); StringV "Sub" ])
  | Ast.Test (Values.I32 Ast.I32Op.Eqz) ->
      ConstructV
        ("testop", [ WasmTypeV (Types.NumType Types.I32Type); StringV "Eqz" ])
  | Ast.Compare (Values.F32 Ast.F32Op.Gt) ->
      ConstructV
        ("relop", [ WasmTypeV (Types.NumType Types.F32Type); StringV "Gt" ])
  | Ast.Compare (Values.I32 Ast.I32Op.GtS) ->
      ConstructV
        ("relop", [ WasmTypeV (Types.NumType Types.I32Type); StringV "GtS" ])
  | Ast.Select None -> ConstructV ("select", [ StringV "TODO: None" ])
  | Ast.LocalGet i32 -> f_i32 "local.get" i32
  | Ast.LocalSet i32 -> f_i32 "local.set" i32
  | Ast.LocalTee i32 -> f_i32 "local.tee" i32
  | Ast.GlobalGet i32 -> f_i32 "global.get" i32
  | Ast.GlobalSet i32 -> f_i32 "global.set" i32
  | Ast.TableGet i32 -> f_i32 "table.get" i32
  | Ast.Call i32 -> f_i32 "call" i32
  | Ast.Block (bt, instrs) ->
      ConstructV
        ("block", [
            al_of_wasm_blocktype types bt;
            ListV (instrs |> al_of_wasm_instrs types |> Array.of_list)])
  | Ast.Loop (bt, instrs) ->
      ConstructV
        ("loop", [
            al_of_wasm_blocktype types bt;
            ListV (instrs |> al_of_wasm_instrs types |> Array.of_list)])
  | Ast.If (bt, instrs1, instrs2) ->
      ConstructV
        ("if", [
            al_of_wasm_blocktype types bt;
            ListV (instrs1 |> al_of_wasm_instrs types |> Array.of_list);
            ListV (instrs2 |> al_of_wasm_instrs types |> Array.of_list);
            ])
  | Ast.Br i32 -> f_i32 "br" i32
  | Ast.Return -> ConstructV ("return", [])
  | _ -> failwith "al_of_wasm_instr for this instr is not implemented"

and al_of_wasm_instrs types winstrs = List.map (al_of_wasm_instr types) winstrs

(* Test Interpreter *)

let al_of_wasm_func wasm_module wasm_func =

  (* Get function type from module *)
  (* Note: function type will be placed in function in DSL *)
  let { it = Types.FuncType (wtl1, wtl2); _ } =
    Int32.to_int wasm_func.it.Ast.ftype.it
    |> List.nth wasm_module.it.Ast.types in

  (* Construct function type *)
  let ftype =
    let al_of_wasm_type ty = WasmTypeV ty in
    let al_tl1 = List.map al_of_wasm_type wtl1 in
    let al_tl2 = List.map al_of_wasm_type wtl2 in
    ArrowV (ListV (Array.of_list al_tl1), ListV (Array.of_list al_tl2)) in

  (* Construct code *)
  let code = al_of_wasm_instrs wasm_module.it.types wasm_func.it.Ast.body |> Array.of_list in

  ConstructV ("FUNC", [ftype; ListV [||]; ListV (code)])

let al_of_wasm_module wasm_module =

  (* Construct functions *)
  let func_list =
    List.map (al_of_wasm_func wasm_module) wasm_module.it.funcs
    |> Array.of_list
    in

  ConstructV ("MODULE", [ListV func_list])
