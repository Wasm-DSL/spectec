(*
This transformation removes uses of the `otherwise` (`ElsePr`) premise from
inductive relations.

It only supports binary relations.

1. It figures out which rules are meant by “otherwise”:

   * All previous rules
   * Excluding those that definitely can’t apply when the present rule applies
     (decided by a simple and conservative comparision of the LHS).

2. It creates an auxillary inductive unary predicate with these rules (LHS only).

3. It replaces the `ElsePr` with the negation of that rule.

*)

open Util
open Source
open Il.Ast

(* Errors *)

let error at msg = Source.error at "else removal" msg

let unary_mixfix : mixop = [[Atom ""]; [Atom ""]]

let is_else prem = prem.it = ElsePr

let replace_else aux_name lhs prem = match prem.it with
  | ElsePr -> NegPr (RulePr (aux_name, unary_mixfix, lhs) $ prem.at) $ prem.at
  | _ -> prem

let unarize rule = match rule.it with 
    | RuleD (rid, binds, _mixop, exp, prems) ->
      let lhs = match exp.it with
        | TupE [lhs; _] -> lhs
        | _ -> error exp.at "expected manifest pair"
      in
      { rule with it = RuleD (rid, binds, unary_mixfix, lhs, prems) }

let not_apart lhs rule = match rule.it with
    | RuleD (_, _, _, lhs2, _) -> not (Il.Apart.apart lhs lhs2)

let rec go at id mixop typ typ1 prev_rules : rule list -> def list = function
  | [] -> [ RelD (id, mixop, typ, List.rev prev_rules) $ at ]
  | r :: rules -> match r.it with
    | RuleD (rid, binds, rmixop, exp, prems) ->
      if List.exists is_else prems
      then
        let lhs = match exp.it with
          | TupE [lhs; _] -> lhs
          | _ -> error exp.at "expected manifest pair"
        in
        let aux_name = id.it ^ "_before_" ^ rid.it $ rid.at in
        let applicable_prev_rules = prev_rules
              |> List.map unarize
              |> List.filter (not_apart lhs)
              |> List.rev in
        [ RelD (aux_name, unary_mixfix, typ1, List.rev applicable_prev_rules) $ r.at ] @
        let prems' = List.map (replace_else aux_name lhs) prems in
        let rule' = { r with it = RuleD (rid, binds, rmixop, exp, prems') } in
        go at id mixop typ typ1 (rule' :: prev_rules) rules
      else
        go at id mixop typ typ1 (r :: prev_rules) rules

let rec t_def (def : def) : def list = match def.it with
  | RecD defs -> [ { def with it = RecD (List.concat_map t_def defs) } ]
  | RelD (id, mixop, typ, rules) -> begin match typ.it with
    | TupT [typ1; _typ2] ->
      go def.at id mixop typ typ1 [] rules
    | _ -> [def]
    end
  | _ -> [ def ]

let transform (defs : script) =
  List.concat_map t_def defs

