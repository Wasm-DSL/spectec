open Il.Ast

let include_input = false

let parens s = "(" ^ s ^ ")"
let brackets s = "[" ^ s ^ "]"
let braces s = "{" ^ s ^ "}"
let ($$) s1 s2 = parens (s1 ^ " " ^ s2)
let render_tuple how tys = parens (String.concat ", " (List.map how tys))
let render_list how tys = brackets (String.concat ", " (List.map how tys))

let render_type_name (id : id) = String.capitalize_ascii id.it

(* let render_rec_con (id : id) = "Mk" ^ render_type_name id *)

let is_reserved = function
 | "in"
 | "export"
 | "import"
 | "global"
 | "local"
 | "mut"
 -> true
 | _ -> false

let make_id s = match s with
 | s when is_reserved s -> "«" ^ s ^ "»"
 | s -> String.map (function
    | '.' -> '_'
    | '-' -> '_'
    | c -> c
    ) s

let render_id (id : id) = make_id id.it

let render_fun_id (id : id) = "«$" ^ id.it ^ "»"

let render_rule_name _qual _ty_id (rule_id : id) (i : int) :  string =
  if rule_id.it = ""
  then "rule_" ^ string_of_int i
  else make_id rule_id.it

let render_con_name qual id : atom -> string = function
  | Atom s ->
    (if qual then render_type_name id ^ "." else "") ^
    make_id s
  | a -> "/- render_con_name: TODO -/ " ^ Il.Print.string_of_atom a

let render_con_name' qual (typ : typ) a = match typ.it with
  | VarT id -> render_con_name qual id a
  | _ -> "_ {- render_con_name': Typ not id -}"


let render_field_name : atom -> string = function
  | Atom s -> make_id s
  | a -> "/- render_field_name: TODO -/ " ^ Il.Print.string_of_atom a


let wrap_type_iter (ty : string) : iter -> string = function
  | Opt -> "Option" $$ ty
  |  _  -> "List" $$ ty

let wrap_type_iters (ty : string) : iter list -> string = List.fold_left wrap_type_iter ty

let rec render_typ (ty : typ) = match ty.it with
  | VarT id -> render_type_name id
  | BoolT -> "Bool"
  | NatT -> "Nat"
  | TextT -> "String"
  | TupT [] -> "Unit"
  | TupT tys -> render_tuple_typ tys
  | IterT (ty, it) -> wrap_type_iter (render_typ ty) it

and render_tuple_typ tys = parens (String.concat " × " (List.map render_typ tys))

let _unsupported_def d =
  "/- " ^
  Il.Print.string_of_def d ^
  "\n-/"

let rec prepend first rest = function
  | [] -> ""
  | (x::xs) -> first ^ x ^ prepend rest rest xs


let render_variant_inj (id1 : id) (id2 : id) =
  "«$" ^ id1.it ^ "_" ^ id2.it ^ "»"

let render_variant_inj' (typ1 : typ) (typ2 : typ) = match typ1.it, typ2.it with
  | VarT id1, VarT id2 -> render_variant_inj id1 id2
  | _, _ -> "_ {- render_variant_inj': Typs not ids -}"

let render_variant_case id ((a, ty, _hints) : typcase) =
  render_con_name false id a ^ " : " ^
  if ty.it = TupT []
  then render_type_name id
  else render_typ ty ^ " -> " ^ render_type_name id

let rec render_exp (exp : exp) = match exp.it with
  | VarE v -> render_id v
  | BoolE true -> "True"
  | BoolE false -> "Frue"
  | NatE n -> string_of_int n
  | TextE t -> "\"" ^ String.escaped t ^ "\""
  | MixE (_, e) -> render_exp e
  | TupE es -> render_tuple render_exp es
  | ListE es -> render_list render_exp es
  | OptE None -> "none"
  | OptE (Some e) -> "some" $$ render_exp e
  | IterE (e, (iter, vs)) -> begin match e.it with
    | VarE v when List.length vs = 1 && List.for_all (Il.Eq.eq_id v) vs  -> render_id v (* Short-ciruit this common form *)
    | _ -> match iter, vs with
      | (List|List1|ListN _), [] ->
        "[" ^ render_exp e ^ "]"
      | (List|List1|ListN _), [v] ->
        "(List.map (λ " ^ render_id v ^ " ↦ " ^ render_exp e ^ ") " ^ render_id v ^ ")"
      | (List|List1|ListN _), [v1; v2] ->
        "(List.zipWith (λ " ^ render_id v1 ^ " " ^ render_id v2 ^ " ↦ " ^ render_exp e ^ ") " ^ render_id v1 ^ " " ^ render_id v2 ^ ")"
      | Opt, [] -> "some" $$ render_exp e
      | Opt, [v] ->
        "(Option.map (λ " ^ render_id v ^ " ↦ " ^ render_exp e ^ ") " ^ render_id v ^ ")"
      | Opt, [v1; v2] ->
        "(Option.zipWith (λ " ^ render_id v1 ^ " " ^ render_id v2 ^ " ↦ " ^ render_exp e ^ ") " ^ render_id v1 ^ " " ^ render_id v2 ^ ")"
      | _, _ ->
      render_exp e ^ " /- " ^ Il.Print.string_of_iterexp (iter, vs) ^ " -/"
  end
  | CaseE (a, e, typ) -> render_case a e typ
  | StrE fields -> braces ( String.concat ", " (List.map (fun (a, e) ->
    render_field_name a ^ " := " ^ render_exp e
    ) fields))
  | SubE (e, typ1, typ2) -> render_variant_inj' typ2 typ1 $$ render_exp e
  | DotE (_ty, e, a) -> render_exp e ^ "." ^ render_field_name a
  | IdxE (e1, e2) -> parens (render_exp e1 ^ ".get! " ^ render_exp e2)
  | LenE e -> render_exp e ^ ".length"
  | CallE (id, e) -> render_fun_id id $$ render_exp e
  | BinE (AddOp, e1, e2)   -> parens (render_exp e1 ^ " + " ^ render_exp e2)
  | BinE (SubOp, e1, e2)   -> parens (render_exp e1 ^ " - " ^ render_exp e2)
  | BinE (ExpOp, e1, e2)   -> parens ("Nat.pow" $$ render_exp e1 $$ render_exp e2)
  | BinE (DivOp, e1, e2)   -> parens ("Nat.div" $$ render_exp e1 $$ render_exp e2)
  | BinE (AndOp, e1, e2)   -> parens (render_exp e1 ^ " && "  ^ render_exp e2)
  | BinE (EquivOp, e1, e2) -> parens (render_exp e1 ^ " = "   ^ render_exp e2)
  | BinE (OrOp, e1, e2)    -> parens (render_exp e1 ^ " || "  ^ render_exp e2)
  | CmpE (EqOp, e1, e2)    -> parens (render_exp e1 ^ " == "  ^ render_exp e2)
  | CmpE (NeOp, e1, e2)    -> parens (render_exp e1 ^ " != "  ^ render_exp e2)
  | CmpE (LeOp, e1, e2)    -> parens (render_exp e1 ^ " <= "  ^ render_exp e2)
  | CmpE (LtOp, e1, e2)    -> parens (render_exp e1 ^ " < "   ^ render_exp e2)
  | CmpE (GeOp, e1, e2)    -> parens (render_exp e1 ^ " >= "  ^ render_exp e2)
  | CmpE (GtOp, e1, e2)    -> parens (render_exp e1 ^ " > "   ^ render_exp e2)
  | CatE (e1, e2)          -> parens (render_exp e1 ^ " ++ "  ^ render_exp e2)
  | CompE (e1, e2)         -> parens (render_exp e1 ^ " ++ "  ^ render_exp e2)
  | _ -> "default /- " ^ Il.Print.string_of_exp exp ^ " -/"

and render_case a e typ =
    if e.it = TupE []
    then render_con_name' true typ a
    else render_con_name' true typ a $$ render_exp e

let render_clause (_id : id) (clause : clause) = match clause.it with
  | DefD (_binds, lhs, rhs, premise) ->
   (if premise <> [] then "-- Premises ignored! \n" else "") ^
   "\n  | " ^ render_exp lhs ^ " => " ^ render_exp rhs

let show_input (d:def) =
    if include_input then
    "/- " (*  ^ Util.Source.string_of_region d.at ^ "\n"*)  ^
    Il.Print.string_of_def d ^
    "\n-/\n"
    else ""

let rec render_prem (prem : premise) =
    match prem.it with
    | RulePr (pid, _mixops, pexp) -> render_type_name pid $$ render_exp pexp
    | IfPr (pexp) -> render_exp pexp
    | IterPr (prem, iterexp) ->
    begin match iterexp with
      | (List|List1|ListN _), [v] ->
        "(Forall (λ " ^ render_id v ^ " ↦ " ^ render_prem prem ^ ") " ^ render_id v ^ ")"
      | (List|List1|ListN _), [v1; v2] ->
        "(Forall₂ (λ " ^ render_id v1 ^ " " ^ render_id v2 ^ " ↦ " ^ render_prem prem ^ ") " ^ render_id v1 ^ " " ^ render_id v2 ^ ")"
      | Opt, [v] ->
        "(Forall (λ " ^ render_id v ^ " ↦ " ^ render_prem prem ^ ") " ^ render_id v ^ ".toList)"
      | Opt, [v1; v2] ->
        "(Forall₂ (λ " ^ render_id v1 ^ " " ^ render_id v2 ^ " ↦ " ^ render_prem prem ^ ") " ^ render_id v1 ^ ".toList " ^ render_id v2 ^ ".toList)"
      | _,_ -> render_prem prem ^ " /- " ^ Il.Print.string_of_iterexp iterexp ^ " -/"
    end
    | ElsePr -> "True /- Else? -/"

let rec render_def (d : def) =
  match d.it with
  | SynD (id, deftyp, _hints) ->
    show_input d ^
    begin match deftyp.it with
    | AliasT ty ->
      "@[reducible] def " ^ render_type_name id ^ " := " ^ render_typ ty 
    | NotationT (mop, ty) ->
      "@[reducible] def " ^ render_type_name id ^ " := /- mixop: " ^ Il.Print.string_of_mixop mop ^ " -/ " ^ render_typ ty
    | VariantT cases ->
      "inductive " ^ render_type_name id ^ " where" ^ prepend "\n | " "\n | " (
        List.map (render_variant_case id) cases
      ) ^
      (if cases = [] then "\n  deriving BEq" else "\n  deriving Inhabited, BEq")
    | StructT fields ->
      (*
      "type " ^ render_type_name id ^ " = " ^ render_tuple render_typ (
        List.map (fun (_a, ty, _hints) -> ty) fields
      )
      *)
      "structure " ^ render_type_name id ^ " where " ^
      String.concat "" ( List.map (fun (a, ty, _hints) ->
        "\n  " ^ render_field_name a ^ " : " ^ render_typ ty
      ) fields) ^
      "\n  deriving Inhabited, BEq\n" ^
      "instance : Append " ^ render_type_name id ^ " where\n" ^
      "  append := fun r1 r2 => {\n" ^
      String.concat "" (List.map (fun (a, _ty, _hints) ->
        "    " ^ render_field_name a ^ " := r1." ^ render_field_name a ^ " ++ r2." ^ render_field_name a ^ ",\n"
      ) fields) ^
      "  }"
    end
  | DecD (id, typ1, typ2, clauses, hints) ->
    show_input d ^
    "def " ^ render_fun_id id ^ " : " ^ render_typ typ1 ^ " -> " ^ render_typ typ2 ^
    begin if clauses = [] then " := default" else
    String.concat "" (List.map (render_clause id) clauses) ^
    (if (List.exists (fun h -> h.hintid.it = "partial") hints)
    then "\n  | _ => default" else "") (* Could use no_error_if_unused% as well *)
    end

  | RelD (id, _mixop, typ, rules, _hints) ->
    show_input d ^
    "inductive " ^ render_type_name id ^ " : " ^ render_typ typ ^ " -> Prop where" ^
    String.concat "" (List.mapi (fun i (rule : rule) -> match rule.it with
      | RuleD (rule_id, binds, _mixop, exp, prems) ->
        "\n  | " ^ render_rule_name false id rule_id i ^ " " ^
        String.concat " " (List.map (fun ((bid : id), btyp, iters) ->
          parens (render_id bid ^ " : " ^ wrap_type_iters (render_typ btyp) iters)
          ) binds) ^ " : " ^
        String.concat "" (List.map (fun (prem : premise) ->
          "\n    " ^ render_prem prem ^ " -> "
        ) prems) ^
          "\n    " ^ (render_type_name id $$ render_exp exp)
    ) rules)

  | RecD [def] ->
    (* Self-recursion is always fine *)
    render_def def

  | RecD defs ->
    "mutual\n" ^
    String.concat "\n" (List.map render_def defs) ^
    "end\n"

let render_script (el : script) =
  String.concat "\n\n" (List.map render_def el)

let gen_string (el : script) =
  "/- Lean 4 export -/\n\n" ^
  "instance : Append (Option a) where\n" ^
  "  append := fun o1 o2 => match o1 with | none => o2 | _ => o1\n\n" ^
  "\n" ^
  (* Really not in the default distribution? *)
  "inductive Forall (R : α → Prop) : List α → Prop\n" ^
  "  | nil : Forall R []\n" ^
  "  | cons {a l₁} : R a → Forall R l₁ → Forall R (a :: l₁)\n" ^
  "attribute [simp] Forall.nil\n" ^
  "variable {r : α → β → Prop} {p : γ → δ → Prop}\n" ^
  "inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop\n" ^
  "  | nil : Forall₂ R [] []\n" ^
  "  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)\n" ^
  "attribute [simp] Forall₂.nil\n" ^
  "def Option.zipWith : (α → β → γ) → Option α → Option β → Option γ\n" ^
  "  | f,  (some x), (some y) => some (f x y)\n" ^
  "  | _, _, _ => none\n" ^
  "def Option.toList : Option α → List α\n" ^
  "  | none => List.nil\n" ^
  "  | some x => [x]\n" ^
  "set_option linter.unusedVariables false\n" ^

  render_script el


let gen_file file el =
  let haskell_code = gen_string el in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc haskell_code)
    ~finally:(fun () -> Out_channel.close oc)
