open Script
open Source

(* Printing *)

let print_import m im =
  let open Types in
  let category, annotation =
    match Ast.import_type m im with
    | ExternFuncType t -> "func", string_of_func_type t
    | ExternTableType t -> "table", string_of_table_type t
    | ExternMemoryType t -> "memory", string_of_memory_type t
    | ExternGlobalType t -> "global", string_of_global_type t
  in
  Printf.printf "  import %s \"%s\" \"%s\" : %s\n"
    category (Ast.string_of_name im.it.Ast.module_name)
      (Ast.string_of_name im.it.Ast.item_name) annotation

let print_export m ex =
  let open Types in
  let category, annotation =
    match Ast.export_type m ex with
    | ExternFuncType t -> "func", string_of_func_type t
    | ExternTableType t -> "table", string_of_table_type t
    | ExternMemoryType t -> "memory", string_of_memory_type t
    | ExternGlobalType t -> "global", string_of_global_type t
  in
  Printf.printf "  export %s \"%s\" : %s\n"
    category (Ast.string_of_name ex.it.Ast.name) annotation

let print_module x_opt m =
  Printf.printf "module%s :\n"
    (match x_opt with None -> "" | Some x -> " " ^ x.it);
  List.iter (print_import m) m.it.Ast.imports;
  List.iter (print_export m) m.it.Ast.exports;
  flush_all ()

let print_values vs =
  let ts = List.map Values.type_of_value vs in
  Printf.printf "%s : %s\n"
    (Values.string_of_values vs) (Types.string_of_value_types ts);
  flush_all ()

let string_of_nan = function
  | CanonicalNan -> "nan:canonical"
  | ArithmeticNan -> "nan:arithmetic"

let type_of_result r =
  match r with
  | NumResult (NumPat n) -> Types.NumType (Values.type_of_num n.it)
  | NumResult (NanPat n) -> Types.NumType (Values.type_of_num n.it)
  | VecResult (VecPat _) -> Types.VecType Types.V128Type
  | RefResult (RefPat r) -> Types.RefType (Values.type_of_ref r.it)
  | RefResult (RefTypePat t) -> Types.RefType t

let string_of_num_pat (p : num_pat) =
  match p with
  | NumPat n -> Values.string_of_num n.it
  | NanPat nanop ->
    match nanop.it with
    | Values.I32 _ | Values.I64 _ -> assert false
    | Values.F32 n | Values.F64 n -> string_of_nan n

let string_of_vec_pat (p : vec_pat) =
  match p with
  | VecPat (Values.V128 (shape, ns)) ->
    String.concat " " (List.map string_of_num_pat ns)

let string_of_ref_pat (p : ref_pat) =
  match p with
  | RefPat r -> Values.string_of_ref r.it
  | RefTypePat t -> Types.string_of_refed_type t

let string_of_result r =
  match r with
  | NumResult np -> string_of_num_pat np
  | VecResult vp -> string_of_vec_pat vp
  | RefResult rp -> string_of_ref_pat rp

let string_of_results = function
  | [r] -> string_of_result r
  | rs -> "[" ^ String.concat " " (List.map string_of_result rs) ^ "]"

let print_results rs =
  let ts = List.map type_of_result rs in
  Printf.printf "%s : %s\n"
    (string_of_results rs) (Types.string_of_value_types ts);
  flush_all ()
