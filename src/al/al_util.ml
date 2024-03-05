open Ast


let numV i = NumV i
let numV_of_int i = Int64.of_int i |> numV
let strV r = RecordE r
let caseV (s, vl) = ConstructV (s, vl)
let optV v_opt = OptV v_opt
let nullary s = ConstructV (String.uppercase_ascii s, [])
let listV a = ListV (ref a)
let listV_of_list l = Array.of_list l |> listV
let zero = numV Int64.zero
let one = numV Int64 .one
let empty_list = listV [||]
let singleton v = listV [|v|]


let some x = caseV (x, [optV (Some (listV_of_list []))])
let none x = caseV (x, [optV None])


(* Helper functions *)

let listv_map f = function
  | ListV arr_ref -> ListV (ref (Array.map f !arr_ref))
  | _ -> failwith "Not a list"


let listv_find f = function
  | ListV arr_ref -> Array.find_opt f !arr_ref |> Option.get
  | _ -> failwith "Not a list"

let listv_nth l n =
  match l with
  | ListV arr_ref -> Array.get !arr_ref n
  | _ -> failwith "Not a list"

let strv_access field = function
  | RecordV r -> Record.find field r
  | _ -> failwith "Not a record"

let map
  (destruct: value -> 'a)
  (construct: 'b -> value)
  (op: 'a -> 'b)
  (v: value): value =
    destruct v |> op |> construct
let map2
  (destruct: value -> 'a)
  (construct: 'b -> value)
  (op: 'a -> 'a -> 'b)
  (v1: value)
  (v2: value): value =
    op (destruct v1) (destruct v2) |> construct


(* Destruct *)

(* TODO: move to error file *)
let fail ty v =
  Print.string_of_value v
  |> Printf.sprintf "Invalid %s: %s" ty
  |> failwith

let unwrap_optv: value -> value option = function
  | OptV opt -> opt
  | v -> fail "OptV" v
let unwrap_listv: value -> value growable_array = function
  | ListV ga -> ga
  | v -> fail "ListV" v
let unwrap_listv_to_array (v: value): value array = !(unwrap_listv v)
let unwrap_listv_to_list (v: value): value list = unwrap_listv_to_array v |> Array.to_list

let get_name = function
  | RuleA ((name, _), _, _) -> name
  | FuncA (name, _, _) -> name

let get_param = function
  | RuleA (_, params, _) -> params
  | FuncA (_, params, _) -> params

let get_body = function
  | RuleA (_, _, body) -> body
  | FuncA (_, _, body) -> body

let unwrap_textv: value -> string = function
  | StringV str -> str
  | v -> fail "text" v
let unwrap_numv: value -> Int64.t = function
  | NumV i -> i
  | v -> fail "int64" v
let unwrap_numv_to_int (v: value): int = unwrap_numv v |> Int64.to_int
let casev_of_case = function
  | ConstructV (s, _) -> s
  | v -> fail "case" v
let casev_replace_nth_arg i v = function
  | ConstructV (s, args) -> ConstructV (s, List.mapi (fun index e -> if index = i then v else e) args)
  | v -> fail "case" v
let casev_nth_arg n = function
  | ConstructV (_, l) when List.length l > n -> List.nth l n
  | v -> fail "case" v
let unwrap_strv = function
  | RecordV r -> r
  | v -> fail "struct" v

let arity_of_frame: value -> value = function
  | FrameV (Some v, _) -> v
  | v -> fail "frame" v
let unwrap_frame: value -> value = function
  | FrameV (_, v) -> v
  | v -> fail "frame" v
