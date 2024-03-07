open Al
open Ast
open Al_util
open Print

(* Map *)

module InfoMap = Map.Make (Int)
module Env = Map.Make (String)
module Map = Map.Make (String)


(* Program *)

type rule_map = algorithm Map.t
type func_map = algorithm Map.t

let rule_map: rule_map ref = ref Map.empty
let func_map: func_map ref = ref Map.empty

let to_map algos =
  let f acc algo =
    let rmap, fmap = acc in
    match algo with
    | RuleA ((name, _), _, _) -> Map.add name algo rmap, fmap
    | FuncA (name, _, _) -> rmap, Map.add name algo fmap
  in
  List.fold_left f (Map.empty, Map.empty) algos

let bound_rule name = Map.mem name !rule_map
let bound_func name = Map.mem name !func_map

let lookup_algo name =
  if bound_rule name then
    Map.find name !rule_map
  else if bound_func name then
    Map.find name !func_map
  else failwith ("Algorithm not found: " ^ name)

module Store = struct
  let store = ref Record.empty

  let init () =
    store :=
      Record.empty
      |> Record.add "FUNC" (listV_of_list [])
      |> Record.add "GLOBAL" (listV_of_list [])
      |> Record.add "TABLE" (listV_of_list [])
      |> Record.add "MEM" (listV_of_list [])
      |> Record.add "ELEM" (listV_of_list [])
      |> Record.add "DATA" (listV_of_list [])
      |> Record.add "STRUCT" (listV_of_list [])
      |> Record.add "ARRAY" (listV_of_list [])

  let assign r = store := r

  let get () = RecordV !store

  let access field = Record.find field !store
end

let init algos = let rmap, fmap = to_map algos in
  Store.init ();
  rule_map := rmap;
  func_map := fmap


(* Environmet *)

type env = value Env.t

let string_of_env env =
  "\n{" ^
  Print.string_of_list
    (fun (k, v) ->
      k ^ ": " ^ Print.string_of_value v)
    "" ",\n  " ""
    (Env.bindings env) ^
  "\n}"

let lookup_env key env =
  try Env.find key env
  with Not_found ->
    Printf.sprintf "The key '%s' is not in the map: %s."
      key (string_of_env env)
    |> prerr_endline;
    raise Not_found

(* AL Context *)
module AlContext = struct
  type mode =
    (* Al context *)
    | Al of string * instr list * env
    (* Wasm context *)
    | Wasm of int
    (* Special context for enter/execute *)
    | Enter of instr list * env
    | Execute of value
    (* Return register *)
    | Return of value

  let al (name, il, env) = Al (name, il, env)
  let wasm n = Wasm n
  let enter (il, env) = Enter (il, env)
  let execute v = Execute v
  let return v = Return v

  type t = mode list

  let tl = List.tl

  let is_reducible = function
    | [] | [ Return _ ] -> false
    | _ -> true

  let can_tail_call = function
    | IfI _ | EitherI _ | PopI _ | LetI _ | ReturnI _ -> false
    | _ -> true

  let get_name ctx =
    match List.hd ctx with
    | Al (name, _, _) -> name
    | Wasm _ -> "Wasm"
    | Execute _ -> "Execute"
    | Enter _ -> "Enter"
    | Return _ -> "Return"

  let add_instrs il = function
    | Al (name, il', env) :: t -> Al (name, il @ il', env) :: t
    | Enter (il', env) :: t -> Enter (il @ il', env) :: t
    | _ -> failwith "Not in AL context"

  let get_env = function
    | Al (_, _, env) :: _ -> env
    | Enter (_, env) :: _ -> env
    | _ -> failwith "Not in AL context"

  let set_env env = function
    | Al (name, instrs, _) :: t -> Al (name, instrs, env) :: t
    | Enter (instrs, _) :: t -> Enter (instrs, env) :: t
    | _ -> failwith "Not in AL context"

  let update_env k v = function
    | Al (name, il, env) :: t -> Al (name, il, Env.add k v env) :: t
    | Enter (instrs, env) :: t -> Enter (instrs, Env.add k v env) :: t
    | _ -> failwith "Not in AL context"

  let get_return_value = function
    | [ Return v ] -> Some v
    | [] -> None
    | _ -> failwith "Unreachable"

  let rec decrease_depth = function
    | Wasm 1 :: t -> t
    | Wasm n :: t -> Wasm (n - 1) :: t
    | Al _ as mode :: t -> mode :: decrease_depth t
    | _ -> failwith "Not in AL or Wasm context"
end


(* Wasm Context *)
module WasmContext = struct
  type t = value * value list * value list

  let top_level_context = StringV "TopLevelContexet", [], []
  let context_stack: t list ref = ref [top_level_context]

  let get_context () =
    match !context_stack with
    | h :: _ -> h
    | _ -> failwith "Wasm context stack underflow"

  let init_context () = context_stack := [top_level_context]

  let push_context ctx = context_stack := ctx :: !context_stack

  let pop_context () =
    match !context_stack with
    | h :: t -> context_stack := t; h
    | _ -> failwith "Wasm context stack underflow"


  (* Context *)

  let get_value_with_condition f =
    match List.find_opt (fun (v, _, _) -> f v) !context_stack with
    | Some (v, _, _) -> v
    | None -> failwith "Wasm context stack underflow"

  let get_current_context () =
    let ctx, _, _ = get_context () in
    ctx

  let get_current_frame () =
    let match_frame = function
      | FrameV _ -> true
      | _ -> false
    in get_value_with_condition match_frame

  let get_module_instance () =
    match get_current_frame () with
    | FrameV (_, mm) -> mm
    | _ -> failwith "Invalid frame"

  let get_current_label () =
    let match_label = function
      | LabelV _ -> true
      | _ -> false
    in get_value_with_condition match_label

  (* Value stack *)

  let is_value = function
    | ConstructV ("CONST", _) -> true
    | ConstructV ("VCONST", _) -> true
    | ConstructV (ref, _)
      when String.starts_with ~prefix:"REF." ref -> true
    | _ -> false

  let get_value_stack () =
    let _, vs, _ = get_context () in
    vs

  let pop_value_stack () =
    let v, vs, ws = pop_context () in
    push_context (v, [], ws);
    vs

  let push_value v =
    let v_ctx, vs, vs_instr = pop_context () in
    if is_value v then
      push_context (v_ctx, v :: vs, vs_instr)
    else
      string_of_value v
      |> Printf.sprintf "%s is not a Wasm value"
      |> failwith

  let pop_value () =
    let v_ctx, vs, vs_instr = pop_context () in
    match vs with
    | h :: t -> push_context (v_ctx, t, vs_instr); h
    | _ -> failwith "Wasm value stack underflow"

  (* Instr stack *)

  let pop_instr () =
    let v_ctx, vs, vs_instr = pop_context () in
    match vs_instr with
    | h :: t -> push_context (v_ctx, vs, t); h
    | _ -> failwith "Wasm instr stack underflow"
end
