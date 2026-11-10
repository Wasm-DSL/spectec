open Ast
open Util.Source

(* Types for mode hint *)
type mode = In | Out
type side = L | R
module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)

type t = {
  mutable modes : mode IntMap.t StringMap.t
}
 
let empty = {
  modes = StringMap.empty
}

let find_opt = StringMap.find_opt

let parse_mode err : El.Ast.exp -> mode IntMap.t =
  let rec go side (exp: El.Ast.exp) mm = match exp.it with
  | HoleE (`Num i) -> if side = L then IntMap.add i In mm else IntMap.add i Out mm
  | VarE (b, []) when b.it = "bool" -> mm
  | ParenE e -> go side e mm
  | TupE es | SeqE es -> List.fold_left (fun acc e -> go side e acc) mm es
  | _ -> mm
  in
  fun exp -> match exp.it with
  | InfixE (lhs, atom, rhs) when atom.it = Xl.Atom.Arrow ->
    let lm = go L lhs IntMap.empty in
    let rm = go R rhs lm in
    rm
  | _ -> err exp.at ("Ill-formed mode hint: " ^ El.Print.string_of_exp exp)

let build_il_hints err (il : script) : t =
  let hints = List.filter_map (fun d -> match d.it with
  | HintD hintdef -> Some hintdef
  | _ -> None 
  ) il in
  List.fold_left (fun hintenv hdef -> 
    match hdef.it with
    | RelH (rid, hints) -> 
      List.fold_left (fun hintenv' hint -> 
        match hint.hintid.it with
        | "mode" -> 
          { modes = StringMap.add rid.it (parse_mode err hint.hintexp) hintenv'.modes }
        | _ -> hintenv'
      ) hintenv hints 
    | _ -> hintenv
  ) empty hints 