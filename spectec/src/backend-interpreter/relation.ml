open Reference_interpreter
open Al
open Ast
open Al_util
open Ds

module FuncMap = Map.Make (String)

let ref_ok =
  (* TODO: some / none *)
  let null = some "NULL" in
  let nonull = none "NULL" in
  let none = nullary "NONE" in
  let nofunc = nullary "NOFUNC" in
  let noexn = nullary "NOEXN" in
  let noextern = nullary "NOEXTERN" in

  let match_heap_type v1 v2 =
    let ht1 = Construct.al_to_heap_type v1 in
    let ht2 = Construct.al_to_heap_type v2 in
    Match.match_ref_type [] (Types.Null, ht1) (Types.Null, ht2)
  in

  function
  (* null *)
  | [CaseV ("REF.NULL", [ ht ]) as v] ->
    if match_heap_type none ht then
      CaseV ("REF", [ null; none])
    else if match_heap_type nofunc ht then
      CaseV ("REF", [ null; nofunc])
    else if match_heap_type noexn ht then
      CaseV ("REF", [ null; noexn])
    else if match_heap_type noextern ht then
      CaseV ("REF", [ null; noextern])
    else
      Numerics.error_typ_value "$Ref_type" "null reference" v
  (* i31 *)
  | [CaseV ("REF.I31_NUM", [ _ ])] -> CaseV ("REF", [ nonull; nullary "I31"])
  (* host *)
  | [CaseV ("REF.HOST_ADDR", [ _ ])] -> CaseV ("REF", [ nonull; nullary "ANY"])
  (* exception *)
  | [CaseV ("REF.EXN_ADDR", [ _ ])] -> CaseV ("REF", [ nonull; nullary "EXN"])
  (* array/func/struct addr *)
  | [CaseV (name, [ NumV (`Nat i) ])]
  when String.starts_with ~prefix:"REF." name && String.ends_with ~suffix:"_ADDR" name ->
    let field_name = String.sub name 4 (String.length name - 9) in
    let object_ = listv_nth (Ds.Store.access (field_name ^ "S")) (Z.to_int i) in
    let dt = strv_access "TYPE" object_ in
    CaseV ("REF", [ nonull; dt])
  (* extern *)
  (* TODO: check null *)
  | [CaseV ("REF.EXTERN", [ _ ])] -> CaseV ("REF", [ nonull; nullary "EXTERN"])
  | vs -> Numerics.error_values "$Ref_type" vs

let module_ok v =
  if !Construct.version <> 3 then failwith "This hardcoded function ($Module_ok) should be only called with test version 3.0";
  match v with
  | [
    CaseV (
      "MODULE",
      [
        ListV _types;
        ListV imports;
        _funcs;
        _globals;
        _tables;
        _mems;
        _tags;
        _elems;
        _datas;
        _start_opt;
        ListV exports;
      ]
    ) as m
  ] ->
    (try
      let module_ = Construct.al_to_module m in
      Reference_interpreter.Valid.check_module module_;

      let tys = Reference_interpreter.Ast.def_types_of module_ in


      let get_clos_externtype = function
        | CaseV ("IMPORT", [ _name1; _name2; externtype ]) ->
          let s = function
            | Types.StatX x when Int32.to_int x < List.length tys ->
              let dt = List.nth tys (Int32.to_int x) in
              Types.DefHT dt
            | x -> Types.VarHT x
          in
          externtype
          |> Construct.al_to_extern_type tys
          |> Types.subst_extern_type s
          |> Construct.al_of_extern_type
        | _ -> Numerics.error_values "$Module_ok" [ m ]
      in
      let get_externidx = function
        | CaseV ("EXPORT", [ _name; externidx ]) -> externidx
        | _ -> Numerics.error_values "$Module_ok" [ m ]
      in

      let externtypes =
        !imports
        |> Array.map get_clos_externtype
        |> listV
      in
      let externidxs =
        !exports
        |> Array.map get_externidx
        |> listV
      in

      CaseV ("->", [ externtypes; externidxs ])
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ()))
    )

  | vs -> Numerics.error_values "$Module_ok" vs

let externaddr_ok = function
  | [ CaseV (name, [ NumV (`Nat z) ]); t ] ->
    (try
      let addr = Z.to_int z in
      let externaddr_type =
        name^"S"
        |> Store.access
        |> unwrap_listv_to_array
        |> fun arr -> Array.get arr addr
        |> strv_access "TYPE"
        |> fun type_ -> CaseV (name, [type_])
        |> Construct.al_to_extern_type []
      in
      let extern_type = Construct.al_to_extern_type [] t in
      boolV (Match.match_extern_type [] externaddr_type extern_type)
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ())))
  | vs -> Numerics.error_values "$Externaddr_ok" vs

let val_ok = function
  | [ v; t ] ->
    let value = Construct.al_to_value v in
    let val_type = Construct.al_to_val_type t in
    (try
      boolV (Match.match_val_type [] (Value.type_of_value value) val_type)
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ())))
  | vs -> Numerics.error_values "$Val_ok" vs

let expand = function
  | [ v ] ->
    (try
      v
      |> Construct.al_to_def_type
      |> Types.expand_def_type
      |> Construct.al_of_str_type
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ())))
  | vs -> Numerics.error_values "$Expand" vs

let manual_map =
  FuncMap.empty
  |> FuncMap.add "Ref_ok" ref_ok
  |> FuncMap.add "Module_ok" module_ok
  |> FuncMap.add "Val_ok" val_ok
  |> FuncMap.add "Externaddr_ok" externaddr_ok
  |> FuncMap.add "Expand" expand

let mem name =

  let interpreter_manual_names =
    manual_map
    |> FuncMap.bindings
    |> List.map fst
  in

  let il2al_manual_names =
    Il2al.Manual.manual_algos
    |> List.map name_of_algo
  in

  List.mem name (interpreter_manual_names @ il2al_manual_names)

let call_func name args =
  let func = FuncMap.find name manual_map in
  func args
