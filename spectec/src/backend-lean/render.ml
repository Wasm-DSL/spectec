open PPrint
open Lean_ast

module NonEmptyList = Util.Lib.NonEmptyList

(* let rec render_command (cmd : command) : string =
  match cmd with
  | DefAsgn (modifier, decl_id, opt_decl_sig, term) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let term_str = render_term term in
    Printf.sprintf "%s def %s %s := %s" modifier_str decl_id decl_sig_str term_str
  | DefCaseMatch (modifier, decl_id, opt_decl_sig, cases) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let cases_str = String.concat "\n" (List.map render_case cases) in
    Printf.sprintf "%s def %s %s\n  %s" modifier_str decl_id decl_sig_str cases_str *)

let rec render_command (cmd : command) : document =
  match cmd with
  | Def def -> render__def def
  | Inductive ind -> render__inductive ind
  | Abbrev ab -> render__abbrev ab
  | Structure s -> render__structure s
  | Opaque o -> render_opaque o
  | Mutual m -> render_mutual m
  | Instance i -> render_instance i
  | Theorem t -> render_theorem t
  | DeriveDeceq d -> render__derive_deceq d
  | Axiom a -> render_axiom a

and render_axiom (axiom : axiom) : document =
  let id_str = render_id axiom.id in
  let decl_sig_str = render_decl_sig axiom.signature in
  string "axiom "
  ^^ id_str
  ^^ space
  ^^ decl_sig_str

and render_theorem (theorem : _theorem) : document =
  let modifier_str = render_decl_modifier theorem.modifier in
  let id_str = render_id theorem.id in
  let decl_sig_str = render_decl_sig theorem.signature in
  let proof_str = render_term theorem.proof in
  modifier_str
  ^^ string "theorem "
  ^^ id_str
  ^^ space
  ^^ decl_sig_str
  ^^ string " :="
  ^^ nest 2 (hardline ^^ proof_str)

and render_instance (inst : instance) : document =
  let modifier_str = render_decl_modifier inst.modifier in
  let priority_str = match inst.priority with
    | None -> empty
    | Some p -> string " (priority := " ^^ string (string_of_int p) ^^ string ")"
  in
  let id_str = match inst.id with
    | None -> empty
    | Some id -> render_id id ^^ string " "
  in
  let decl_sig_str = render_decl_sig inst.signature in
  let body_strs = List.map render_struct_inst_field inst.body in
  let body_str = separate hardline body_strs in
  modifier_str
  ^^ string "instance "
  ^^ priority_str
  ^^ id_str
  ^^ decl_sig_str
  ^^ string " where"
  ^^ nest 2 (hardline ^^ body_str)

and render_mutual (mutual : mutual) : document =
  match mutual with
  | MutualInductiveStructure (inds, structs) ->
    let inds_str = separate (hardline) (List.map render__inductive inds) in
    let structs_str = separate (hardline) (List.map render__structure structs) in
    group (string "mutual" ^^ hardline ^^ inds_str ^^ hardline ^^ structs_str ^^ hardline ^^ string "end")

  | MutualDefAbbrev (defs, abbrevs) ->
    let defs_str = separate (hardline) (List.map render__def defs) in
    let abbrevs_str = separate (hardline) (List.map render__abbrev abbrevs) in
    group (string "mutual" ^^ hardline ^^ defs_str ^^ hardline ^^ abbrevs_str ^^ hardline ^^ string "end")

and render_opaque (op : opaque) : document =
  let modifier_str = render_decl_modifier op.modifier in
  let id_str = render_id op.id in
  let decl_sig_str = render_decl_sig op.signature in
  let rhs_str = match op.rhs with
  | None -> string ""
  | Some r -> (string ":= ") ^^ (render_term r)
  in
  group (modifier_str ^^ string "opaque " ^^ id_str ^^ string " " ^^ decl_sig_str ^^ string " " ^^ rhs_str)

and render_argument (arg : argument) : document =
  match arg with
  | Term t ->
    match t with
    | Ident _ | Num _ | Hole _ | LeadingDot _ | List _ -> render_term t
    | _ -> string "(" ^^ render_term t ^^ string ")"

and render_num (num : _numtype) : document =
  match num with
  | LeanNat n -> string (Z.to_string n)
  | LeanInt i ->
    if i >= Z.zero then
      string (Z.to_string i)
    else
      string (Printf.sprintf "-%s" (Z.to_string (Z.abs i)))
  | LeanRat q -> string (Printf.sprintf "%s/%s" (Z.to_string (Q.num q)) (Z.to_string (Q.den q)))
  | LeanReal r -> string (Printf.sprintf "%.17g" r) (* 17 significant digits seems to be minimum for exact representation of any IEEE 754 double-precision float *)

and render_struct_inst_l_val (silv : struct_inst_l_val) : document =
  match silv with
  | Ident_SILV id -> render_id id
  | Num_SILV i -> string (string_of_int i)

and render_struct_inst_field (sif : struct_inst_field) : document =
  match sif with
  | Ident_SIF id -> render_id id
  | AssignedField {
      l_val = l_val;
      is_private = is_private;
      term = term;
  } ->
    let l_val_str = render_struct_inst_l_val l_val in
    let privacy_str = if is_private then string "private " else string "" in
    let term_str = render_term term in
    group (privacy_str ^^ l_val_str ^^ string " := " ^^ term_str)

and render__index_type (index_type : _index_type) : document =
  match index_type with
  | Plain -> string ""
  | Option -> string "?"
  | Unsafe -> string "!"

and render__slice_bounds (bounds : _slice_bounds) : document =
  match bounds with
  | SliceFrom e -> string (string_of_int 0) ^^ string " : " ^^ render_term e
  | SliceTo e -> render_term e ^^ string " : _"
  | SliceBetween (e1, e2) -> render_term e1 ^^ string " : " ^^ render_term e2

and render_fun_binder (binder : fun_binder) : document =
  match binder with
  | Ident_FB id -> render_id id
  | BracketedBinder_FB bb -> render_bracketed_binder bb
  | Hole_FB -> string "_"

(* TODO: adapt more properly from original backend *)
and render_id a = match a with
  | "rec" -> string "rec_"
  | "bool" -> string "nat_of_bool"
  | "mut" | "local" | "export" | "import" | "catch" | "syntax" | "at"
    -> string (Printf.sprintf "«%s»" a)
  | _ -> string a

and render_term (term : term) : document =
  match term with
  | Hole _ -> string "_"

  | FunType (t1, t2) ->
      (* ↔ has precedence 20 in Lean 4, lower than → at 25.
         Without parens, `A ↔ B → C` parses as `A ↔ (B → C)` rather than `(A ↔ B) → C`.
         ∀ has even lower precedence (extends right), so `∀ x ∈ S, P → Q` parses
         as `∀ x ∈ S, (P → Q)` rather than `(∀ x ∈ S, P) → Q`. *)
      let t1_str = match t1 with
        | BinaryInfixFunApp (_, Ident "↔", _)
        | BoundedForall _ ->
          string "(" ^^ render_term t1 ^^ string ")"
        | _ -> render_term t1
      in
      let t2_str = render_term t2 in
      t1_str ^^ string " → " ^^ t2_str

  | Ident id -> render_id id

  | Sort level -> (string "Sort ") ^^ (render_level level)

  | Type None -> string "Type"

  | Type (Some level) -> (string "Type ") ^^ (render_level level)

  | Prop -> string "Prop"

  | ProdType (t1, t2) -> (render_term t1) ^^ string " × " ^^ (render_term t2)

  | FunApp (t1, args) ->
      let args_str = separate (string " ") (List.map render_argument (NonEmptyList.to_list args)) in
      (render_term t1) ^^ string " " ^^ args_str

  | FunAppEllipsis (t1, args) ->
      let args_str = separate (string " ") (List.map render_argument args) in
      (render_term t1) ^^ string " " ^^ args_str ^^ string " ..."

  | Num num -> render_num num

  | Text s -> string "\"" ^^ string s ^^ string "\""

  | BinaryInfixFunApp (arg1, term, arg2)
    ->
      let arg1_str = render_argument arg1 in
      let term_str = render_term term in
      let arg2_str = render_argument arg2 in
      arg1_str ^^ string " " ^^ term_str ^^ string " " ^^ arg2_str

  | Tuple terms ->
      let terms_str = separate (string ", ") (List.map render_term terms) in
      string "(" ^^ terms_str ^^ string ")"

  | DotProj (t1, t2) ->
      let t1_str = match t1 with
        | Ident _ | DotProj _ | Tuple _ | Num _ | Text _ -> render_term t1
        | _ -> string "(" ^^ render_term t1 ^^ string ")"
      in
      let t2_str = render_term t2 in
      t1_str ^^ string "." ^^ t2_str

  | LeadingDot t ->
      let t_str = render_term t in
      string "." ^^ t_str

  | Struct {
    fields = fields;
    type_annotation = type_annotation;
  } ->
      let fields = List.map render_struct_inst_field fields in
      let fields_str = separate hardline fields in
      let type_annotation_str = match type_annotation with
        | None -> empty
        | Some t -> string " : " ^^ render_term t
       in
      string "{"
      ^^ nest 2 (hardline ^^ fields_str ^^ type_annotation_str)
      ^^ hardline
      ^^ string "}"

  | List terms -> 
      let terms_str = separate (string ", ") (List.map render_term terms) in
      string "["
      ^^ terms_str
      ^^ string "]"

  | Index {
    collection = collection;
    index = index;
    index_type = index_type;
  } ->
      let collection_str = string "(" ^^ render_term collection ^^ string ")" in
      let index_str = render_term index in
      let index_type_str = render__index_type index_type in
      collection_str
      ^^ string "["
      ^^ index_str
      ^^ string "]"
      ^^ index_type_str

  | Slice {
    collection = collection;
    bounds = bounds;
  } ->
      let collection_str = render_term collection in
      let bounds_str = render__slice_bounds bounds in
      string "["
      ^^ collection_str
      ^^ string "["
      ^^ bounds_str
      ^^ string "]"
      ^^ string "]"

  | UpdateStruct {
    struct_to_update = struct_to_update;
    fields_to_update = fields_to_update;
  } ->
      let struct_to_update_str = render_term struct_to_update in
      let struct_inst_field_strs = List.map render_struct_inst_field fields_to_update in
      let fields_to_update_str = separate hardline struct_inst_field_strs in
      string "{"
      ^^ nest 2 (hardline ^^ struct_to_update_str ^^ string " with " ^^ hardline ^^ fields_to_update_str)
      ^^ hardline
      ^^ string "}"

  | Lambda {
    params = params;
    body = body;
  } ->
      let params_str = separate (string " ") (List.map render_fun_binder (NonEmptyList.to_list params)) in
      let body_str = render_term body in
      string "fun "
      ^^ params_str
      ^^ string " => "
      ^^ body_str

  | IfThenElse {
    cond = cond;
    then_branch = then_branch;
    else_branch = else_branch;
  } ->
      let cond_str = render_term cond in
      let then_branch_str = render_term then_branch in
      let else_branch_str = render_term else_branch in
      string "if "
      ^^ nest 2 (hardline ^^ cond_str)
      ^^ hardline ^^ string "then"
      ^^ nest 2 (hardline ^^ then_branch_str)
      ^^ hardline ^^ string "else"
      ^^ nest 2 (hardline ^^ else_branch_str)

  | Match {
    match_terms = match_terms;
    cases = cases;
  } ->
      let match_terms_str = separate (string ", ") (List.map render_term match_terms) in
      let cases_strs = List.map (fun (pattern, body) ->
        let pattern_str = separate (string ", ") (List.map render_term pattern) in
        let body_str = render_term body in
        string "| " ^^ pattern_str ^^ string " => " ^^ body_str
      ) cases in
      let cases_str = separate hardline cases_strs in
      string "match "
      ^^ match_terms_str
      ^^ string " with"
      ^^ hardline
      ^^ cases_str
  
  | By tactic_seq ->
      let tactic_seq_str = render_tactic_seq tactic_seq in
      string "by "
      ^^ nest 2 (hardline ^^ tactic_seq_str)

  | RightPipelineField (term1, term2) ->
      let term1_str = render_term term1 in
      let term2_str = render_term term2 in
      term1_str
      ^^ string " |>."
      ^^ term2_str

  | AnonymousApp ->
      string "(· ·)"

  | BoundedForall { var; collection; body } ->
      (* Renders as:  ∀ var ∈ collection, body
         e.g.         ∀ t ∈ ts, TypeOk t
         e.g.         ∀ p ∈ ts1 |>.zip (ts2), ValType_sub (p.1) (p.2)  *)
      string "∀ "
      ^^ render_id var
      ^^ string " ∈ "
      ^^ render_term collection
      ^^ string ", "
      ^^ render_term body

  | Not term ->
      string "¬ "
      ^^ render_term term

  | Premises lines_terms ->
      (* Each premise on its own line followed by →, then the conclusion
         (the last element -- see the Premises variant's doc comment).
         The leading hardline + nest 2 means the block starts on a new line
         indented by 2 relative to the : that precedes it, giving e.g.:

           | case_name (params...) :
               premise_1 →
               premise_2 →
               conclusion

         Premises whose outermost operator has lower or equal precedence to →
         must be parenthesised, because appending " →" would otherwise be
         parsed as part of that operator's body:
           ∀ x ∈ S, P →   parses as  ∀ x ∈ S, (P → …)   — wrong
           A ↔ B →         parses as  A ↔ (B → …)         — wrong
           P → Q →         parses as  P → (Q → …)          — wrong
      *)
      let render_premise p =
        let needs_parens = match p with
          | BoundedForall _
          | BinaryInfixFunApp (_, Ident "↔", _)
          | FunType _ -> true
          | _ -> false
        in
        let s = render_term p in
        (if needs_parens then string "(" ^^ s ^^ string ")" else s)
        ^^ string " →"
      in
      let premises, conclusion = Util.Lib.List.split_last lines_terms in
      let lines =
        List.map render_premise premises @ [render_term conclusion]
      in
      nest 2 (hardline ^^ separate hardline lines)

  (* «let» ::= "let" letConfig letDecl (";")? term
     Rendered as:
       let [config] pat [: type] := value
       body
     e.g.
       let (a, b) := pair
       a + b
  *)
  | Let { let_config; let_decl; body } ->
      let config_doc =
        List.fold_left (^^) empty (List.map render_let_config_item let_config)
      in
      let decl_doc = match let_decl with
        | LetPatDecl { pat; type_; value } ->
            space ^^ render_term pat
            ^^ (match type_ with
                | Some t -> string " : " ^^ render_term t
                | None -> empty)
            ^^ string " :=" ^^ space ^^ render_term value
      in
      string "let" ^^ config_doc ^^ decl_doc ^^ hardline ^^ render_term body

  | Sorry -> string "sorry"
  (* | _ -> failwith (Printf.sprintf "render_term: unhandled term: %s" (show_term term)) *)

and render_tactic_seq (tactic_seq : tactic_seq) : document =
  let tactic_strs = List.map render_tactic tactic_seq in
  separate (string "; ") tactic_strs

and render_tactic (tactic : tactic) : document =
  match tactic with
  | TacticExact term ->
      let term_str = render_term term in
      string "exact " ^^ term_str
  | TacticIntros idents ->
      let idents_str = separate (string " ") (List.map render_id idents) in
      string "intros " ^^ idents_str
  | TacticAssumption ->
      string "assumption"
  | TacticFirst tactic_seqs ->
      let tactic_seq_strs = List.map render_tactic_seq tactic_seqs in
      let tactic_seq_str = List.map (fun s -> string " | " ^^ s ^^ hardline) tactic_seq_strs in
      string "first" ^^ nest 2 (hardline ^^ separate empty tactic_seq_str)

and render_level (level : level) : document =
  match level with
  | LevelLit n -> string (string_of_int n)
  | LevelVar id -> render_id id

(* letOpt ::= "nondep" | "postponeValue" | "usedOnly" | "zeta" | "generalize" *)
and render_let_opt (opt : let_opt) : document =
  match opt with
  | Nondep -> string "nondep"
  | PostponeValue -> string "postponeValue"
  | UsedOnly -> string "usedOnly"
  | Zeta -> string "zeta"
  | Generalize -> string "generalize"

(* letConfigItem ::= "+" letOpt | "-" letOpt | "(" "eq" ":=" binderIdent ")"
   e.g.  +nondep     -zeta     (eq := h) *)
and render_let_config_item (item : let_config_item) : document =
  match item with
  | LetOptPos opt -> string " +" ^^ render_let_opt opt
  | LetOptNeg opt -> string " -" ^^ render_let_opt opt
  | LetOptEq id -> string " (eq := " ^^ string id ^^ string ")"

and render__structure (s : _structure) : document =
  let modifier_str = render_decl_modifier s.modifier in
  let id_str = render_id s.id in
  let binders = separate (string " ") (List.map render_bracketed_binder s.binders) in
  let universe = match s.universe with
  | None -> empty
  | Some r -> render_term r
  in
  let constructor = match s.constructor with
  | None -> None
  | Some (constructor_modifier, constructor_id) ->
      Some ((render_decl_modifier constructor_modifier) ^^ (render_id constructor_id) ^^ string " ::")
  in
  let fields_str = separate hardline (List.map render_struct_field s.fields) in
  let deriving_str = render__deriving s.deriving in
  modifier_str
  ^^ string "structure "
  ^^ id_str
  ^^ binders
  ^^ universe
  ^^ string " where"
  ^^ nest 2 (
    (match constructor with None -> empty | Some c -> hardline ^^ c)
    ^^ hardline ^^ fields_str
  )
  ^^ hardline
  ^^ deriving_str

and render_struct_field (sf : struct_field) : document =
  match sf with
  | StructSimpleBinder ssb
    ->
      (render_decl_modifier ssb.modifier)
      ^^ (render_id ssb.id)
      ^^ (render_opt_decl_sig ssb.signature)

and render__def (def : _def) : document =
  match def with
  | DefAsgn d ->
    let modifier_str = render_decl_modifier d.modifier in
    let id_str = render_id d.id in
    let decl_sig_str = render_opt_decl_sig d.signature in
    let term_str = render_term d.body in
    modifier_str
    ^^ string "def "
    ^^ id_str
    ^^ decl_sig_str
    ^^ string " :="
    ^^ nest 2 (hardline ^^ term_str)

  | DefCases d ->
    let modifier_str = render_decl_modifier d.modifier in
    let id_str = render_id d.id in
    let decl_sig_str = render_opt_decl_sig d.signature in
    let cases_str = separate hardline (List.map render__def_case d.body) in
    modifier_str
    ^^ string "def "
    ^^ id_str
    ^^ decl_sig_str
    ^^ nest 2 (hardline ^^ cases_str)

  | DefStruct d ->
    let modifier_str = render_decl_modifier d.modifier in
    let id_str = render_id d.id in
    let decl_sig_str = render_opt_decl_sig d.signature in
    let fields_str = separate hardline (List.map render_struct_inst_field d.body) in
    modifier_str
    ^^ string "def "
    ^^ id_str
    ^^ decl_sig_str
    ^^ string " where"
    ^^ nest 2 (hardline ^^ fields_str)

and render__def_case (case : _def_case) : document =
  let (pattern, body) = case in
  let pattern_str = render_term pattern in
  let body_str = render_term body in
  string "|"
  ^^ pattern_str
  ^^ string " => "
  ^^ body_str

and render__inductive (ind : _inductive) : document =
  (* let (modifier, decl_id, opt_decl_sig, cases, deriving) = ind in *)
  let modifier_str = render_decl_modifier ind.modifier in
  let id_str = render_id ind.id in
  let decl_sig_str = render_opt_decl_sig ind.signature in
  let cases_str = separate hardline (List.map render__inductive_case ind.cases) in
  let deriving_str = render__deriving ind.deriving in
  modifier_str
  ^^ string "inductive "
  ^^ id_str
  ^^ decl_sig_str
  ^^ string " where"
  ^^ nest 2 (hardline ^^ cases_str)
  ^^ hardline
  ^^ deriving_str

and render__inductive_case (case : _inductive_case) : document =
  let modifier_str = render_decl_modifier case.modifier in
  let id_str = render_id case.id in
  let decl_sig_str = render_opt_decl_sig case.signature in
  string "| "
  ^^ modifier_str
  ^^ id_str
  ^^ decl_sig_str

and render__abbrev (abbrev : _abbrev) : document =
  match abbrev with
  | AbbrevAsgn a ->
    let modifier_str = render_decl_modifier a.modifier in
    let id_str = render_id a.id in
    let decl_sig_str = render_opt_decl_sig a.signature in
    let term_str = render_term a.body in
    modifier_str
    ^^ string "abbrev "
    ^^ id_str
    ^^ decl_sig_str
    ^^ string " := "
    ^^ term_str
  | AbbrevCases a ->
    let modifier_str = render_decl_modifier a.modifier in
    let id_str = render_id a.id in
    let decl_sig_str = render_opt_decl_sig a.signature in
    let cases_str = separate hardline (List.map render__def_case a.body) in
    modifier_str
    ^^ string "abbrev "
    ^^ id_str
    ^^ decl_sig_str
    ^^ cases_str

and render__deriving (deriving : _deriving) : document =
  match deriving.deriving with
  | [] -> empty
  | idents -> string ("deriving ") ^^ (separate (string ", ") (List.map string idents))

and render__derive_deceq (d : _derive_deceq) : document =
  string "derive_deceq "
  ^^ separate (string " ") (List.map render_id (NonEmptyList.to_list d))

and render_decl_modifier (modifier : decl_modifier) : document =
  (* The comment (if any) always sits on its own line, terminated by its own
     hardline -- it's not one of the space-separated flags below, since a
     trailing `space` placed after that hardline would land as a stray
     leading blank on the next line rather than as a separator. *)
  let comment_doc = match modifier.comment with
    | Some c -> string "/- " ^^ string c ^^ string " -/" ^^ hardline
    | None -> empty
  in
  let flag_parts = List.filter_map Fun.id [
    (match modifier.visibility with Some Private -> Some (string "private") | Some Protected -> Some (string "protected") | Some Public -> Some (string "public") | None -> None);
    (if modifier.noncomputable then Some (string "noncomputable") else None);
    (if modifier.unsafe then Some (string "unsafe") else None);
    (match modifier.recursion_modifer with Some Partial -> Some (string "partial") | Some NonRec -> Some (string "nonrec") | None -> None);
  ] in
  let flags_doc = match flag_parts with
    | [] -> empty
    | _ -> separate space flag_parts ^^ space
  in
  comment_doc ^^ flags_doc

and render_decl_sig (params, term : decl_sig) : document =
  (* Technically this is a subset of opt_decl_sig, but Lean's reference found it convenient to distinguish the two *)
  let params_str = separate (string " ") (List.map render_params params) in
  let term_str = render_term term in
  params_str ^^ string " : " ^^ term_str

and render_opt_decl_sig (opt_decl_sig : opt_decl_sig) : document =
  match opt_decl_sig with
  | ([], Some term) ->
    string " : " ^^ render_term term
  | (params, Some term) ->
    let params_str = separate space (List.map render_params params) in
    space ^^ params_str ^^ string " : " ^^ render_term term
  | ([], None) ->
    empty
  | (params, None) ->
    space ^^ separate space (List.map render_params params)

and render_params (param : _params) : document =
  match param with
  | Ident_P ident -> render_id ident
  | Hole_P _ -> string "_"
  | BracketedBinder binder -> render_bracketed_binder binder

and render__ident_or_hole (ioh : _ident_or_hole) : document =
  match ioh with
  | Ident_IOH ident -> render_id ident
  | Hole_IOH _ -> string "_"

and render_bracketed_binder (binder : bracketed_binder) : document =
  match binder with
  | ExplicitParam (idents, term) ->
    let idents_str = separate (string " ") (List.map render__ident_or_hole (NonEmptyList.to_list idents)) in
    let term_str = render_term term in
    string "(" ^^ idents_str ^^ string " : " ^^ term_str ^^ string ")"
  | OptAutoParam (idents, term1, term2) ->
    let idents_str = separate (string " ") (List.map render__ident_or_hole (NonEmptyList.to_list idents)) in
    let term1_str = render_term term1 in
    let term2_str = render_term term2 in
    string "(" ^^ idents_str ^^ string " : " ^^ term1_str ^^ string " := " ^^ term2_str ^^ string ")"
  | ImplicitParam (idents, term) ->
    let idents_str = separate (string " ") (List.map render__ident_or_hole (NonEmptyList.to_list idents)) in
    let term_str = render_term term in
    string "{" ^^ idents_str ^^ string " : " ^^ term_str ^^ string "}"
  | InstanceParam term ->
    string "[" ^^ render_term term ^^ string "]"

and render__imports (imports : _imports) : document =
  separate hardline (List.map (fun m -> string "import " ^^ string m) imports)

and render__script (script : _script) : document =
  let commands_str = separate (hardline ^^ hardline) (List.map render_command script.commands) in
  match script.imports with
  | [] -> commands_str
  | _ -> render__imports script.imports ^^ hardline ^^ hardline ^^ commands_str

(* PPrint never trims whitespace on its own: a few render_term branches (e.g.
   By's "by ", opt_decl_sig's " : " before a Premises node) put a literal
   space right before a hardline, which comes straight through as trailing
   whitespace on that line. Rather than track down every such call site,
   strip trailing whitespace from every line once, here, at the single point
   where the document becomes a string. *)
let strip_trailing_whitespace_per_line (s : string) : string =
  String.split_on_char '\n' s
  |> List.map (fun line ->
      let len = String.length line in
      let rec last_non_blank i =
        if i <= 0 then 0
        else match line.[i - 1] with
          | ' ' | '\t' -> last_non_blank (i - 1)
          | _ -> i
      in
      String.sub line 0 (last_non_blank len))
  |> String.concat "\n"

(* Collapse any run of trailing newlines (PPrint's last command can leave a
   blank line dangling at the very end) down to exactly one, matching normal
   POSIX text-file convention. *)
let normalize_trailing_newline (s : string) : string =
  let len = String.length s in
  let rec last_non_newline i =
    if i <= 0 then 0
    else if s.[i - 1] = '\n' then last_non_newline (i - 1)
    else i
  in
  String.sub s 0 (last_non_newline len) ^ "\n"

let render_script_to_string (script : _script) : string =
  let buf = Buffer.create 4096 in
  PPrint.ToBuffer.pretty 1.0 80 buf (render__script script);
  Buffer.contents buf
  |> strip_trailing_whitespace_per_line
  |> normalize_trailing_newline