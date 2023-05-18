open Al

let rec walk_expr f e =
  let _, _, f_expr = f in
  match e with
  | ValueE v -> f_expr (ValueE v)
  | MinusE inner_e -> f_expr (MinusE (walk_expr f inner_e))
  | AddE (e1, e2) -> f_expr (AddE (walk_expr f e1, walk_expr f e2))
  | SubE (e1, e2) -> f_expr (SubE (walk_expr f e1, walk_expr f e2))
  | DivE (e1, e2) -> f_expr (DivE (walk_expr f e1, walk_expr f e2))
  | AppE (fname, args) -> f_expr (AppE (fname, walk_exprs f args))
  (* TODO: Implement walker for iter *)
  | MapE (fname, args, iter) -> f_expr (MapE (fname, walk_exprs f args, iter))
  | IterE (n, iter) -> f_expr (IterE (n, iter))
  | LengthE inner_e -> f_expr (LengthE (walk_expr f inner_e))
  | ArityE inner_e -> f_expr (ArityE (walk_expr f inner_e))
  | GetCurFrameE -> f_expr GetCurFrameE
  | FrameE (e1, e2) -> f_expr (FrameE (walk_expr f e1, walk_expr f e2))
  | ConcatE (e1, e2) -> f_expr (ConcatE (walk_expr f e1, walk_expr f e2))
  | ListE el -> f_expr (ListE (Array.map (walk_expr f) el))
  | AccessE (e, p) -> f_expr (AccessE (walk_expr f e, walk_path f p))
  | RecordE r -> f_expr (RecordE (Record.map (walk_expr f) r))
  | TupE el -> f_expr (TupE (List.map (walk_expr f) el))
  | OptE e -> f_expr (OptE (Option.map (walk_expr f) e))
  | ConstE (e1, e2) -> f_expr (ConstE (walk_expr f e1, walk_expr f e2))
  | RefFuncAddrE inner_e -> f_expr (RefFuncAddrE (walk_expr f inner_e))
  | RefNullE n -> f_expr (RefNullE n)
  | LabelE (e1, e2) -> f_expr (LabelE (f_expr e1, f_expr e2))
  | NameE n -> f_expr (NameE n)
  | ConstructE (cons, el) -> f_expr (ConstructE (cons, walk_exprs f el))
  | YetE s -> f_expr (YetE s)
  | _ ->
      "Walker is not implemented for " ^ Print.structured_string_of_expr e
      |> failwith

and walk_exprs f = walk_expr f |> List.map

and walk_path f p =
  let f_path p = p in
  (* TODO *)
  match p with
  | IndexP e -> f_path (IndexP (walk_expr f e))
  | SliceP (e1, e2) -> f_path (SliceP (walk_expr f e1, walk_expr f e2))
  | DotP _ -> f_path p

let rec walk_cond f c =
  let _, f_cond, _ = f in
  match c with
  | NotC inner_c -> f_cond (NotC (walk_cond f inner_c))
  | OrC (c1, c2) -> f_cond (OrC (walk_cond f c1, walk_cond f c2))
  | EqC (e1, e2) -> f_cond (EqC (walk_expr f e1, walk_expr f e2))
  | GeC (e1, e2) -> f_cond (GeC (walk_expr f e1, walk_expr f e2))
  | GtC (e1, e2) -> f_cond (GtC (walk_expr f e1, walk_expr f e2))
  | LtC (e1, e2) -> f_cond (LtC (walk_expr f e1, walk_expr f e2))
  | LeC (e1, e2) -> f_cond (LeC (walk_expr f e1, walk_expr f e2))
  | _ -> Print.structured_string_of_cond c |> failwith

let rec walk_instr f instr =
  let f_instr, _, _ = f in
  match instr with
  | IfI (c, t, e) ->
      f_instr (IfI (walk_cond f c, walk_instrs f t, walk_instrs f e))
  | OtherwiseI b -> f_instr (OtherwiseI (walk_instrs f b))
  | WhileI (c, il) -> f_instr (WhileI (walk_cond f c, walk_instrs f il))
  | RepeatI (e, il) -> f_instr (RepeatI (walk_expr f e, walk_instrs f il))
  | EitherI (il1, il2) ->
      f_instr (EitherI (walk_instrs f il1, walk_instrs f il2))
  | ForI (e, il) -> f_instr (ForI (walk_expr f e, walk_instrs f il))
  | AssertI s -> f_instr (AssertI s)
  | PushI e -> f_instr (PushI (walk_expr f e))
  | PopI e -> f_instr (PopI (walk_expr f e))
  | PopAllI e -> f_instr (PopAllI (walk_expr f e))
  | LetI (n, e) -> f_instr (LetI (n, walk_expr f e))
  | TrapI -> f_instr TrapI
  | NopI -> f_instr NopI
  | ReturnI e_opt -> f_instr (ReturnI (Option.map (walk_expr f) e_opt))
  | InvokeI e -> f_instr (InvokeI (walk_expr f e))
  | EnterI (e1, e2) -> f_instr (EnterI (walk_expr f e1, walk_expr f e2))
  | ExecuteI e -> f_instr (ExecuteI (walk_expr f e))
  | ReplaceI (e1, p, e2) ->
      f_instr (ReplaceI (walk_expr f e1, walk_path f p, walk_expr f e2))
  | JumpI e -> f_instr (JumpI (walk_expr f e))
  | PerformI e -> f_instr (PerformI (walk_expr f e))
  | ExitI n -> f_instr (ExitI n)
  | AppendI (e1, e2, s) -> f_instr (AppendI (walk_expr f e1, walk_expr f e2, s))
  | YetI s -> f_instr (YetI s)

and walk_instrs f = walk_instr f |> List.map

let walk f = function
  | Algo (name, params, body) -> (
      let new_body = walk_instrs f body in
      match params with
      | (PairE (_, f), StateT) :: rest_params ->
          Algo (name, rest_params, LetI (f, GetCurFrameE) :: new_body)
      | _ -> Algo (name, params, new_body))
