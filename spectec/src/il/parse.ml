open Ast
open Util.Source


(* Flags *)

let trace = ref false
let check_ambiguity = ref false


(* Source stream *)

type stream = {src : string; pos : int}

let stream src = {src; pos = 0}

let pos str = str.pos
let rem str = String.length str.src - str.pos
let eof str = (rem str = 0)
let get str = str.src.[str.pos]
let text str n = String.sub str.src str.pos n
let rest str = String.sub str.src str.pos (String.length str.src - str.pos)
let adv str n = {str with pos = str.pos + n}

let at str n =
  let left = {no_pos with column = str.pos} in
  let right = {no_pos with column = str.pos + n} in
  {left; right}


(* Tracing *)

type trace_entry = {id : id; args : arg list; prod : sym option}  (* for logging *)
type 'a trace = {entries : trace_entry list; print : 'a -> string}

let empty_trace = {entries = []; print = fun _ -> assert false}

let enter tr id args print =
  {print; entries = {id; args; prod = None}::tr.entries}

let alt tr prod =
  {tr with entries = {(List.hd tr.entries) with prod}::(List.tl tr.entries)}

let prod tr = (List.hd tr.entries).prod

let string_of_exps es =
  "[" ^ Print.(string_of_list string_of_exp " " es) ^ "]"

let rec string_of_sym g =
  match g.it with
  | VarG (id, as_) -> id.it ^ string_of_args as_
  | SeqG gs -> Print.string_of_list string_of_sym_paren " " gs
  | AltG gs -> Print.string_of_list string_of_sym_paren "|" gs
  | RangeG (b1, b2) -> Print.string_of_byte b1  ^ "|...|" ^ Print.string_of_byte b2
  | IterG (g1, (iter, _)) -> string_of_sym_paren g1 ^ Print.string_of_iter iter
  | AttrG (_e, g1) -> string_of_sym g1
  | _ -> Print.string_of_sym ~short:true g

and string_of_sym_paren g =
  match g.it with
  | SeqG _ | AltG _ | RangeG _ -> "(" ^ string_of_sym g ^ ")"
  | _ -> string_of_sym g

and string_of_args as_ =
  if as_ = [] then "" else
  "(" ^ String.concat "," (List.filter_map string_of_arg as_) ^ ")"

and string_of_arg a =
  match a.it with
  | ExpA e -> Some (Print.string_of_exp e)
  | TypA _ -> None
  | DefA id -> Some ("$" ^ id.it)
  | GramA g -> Some (string_of_sym g)

let string_of_trace_entry  entry =
  string_of_sym
    (VarG (entry.id, entry.args) $$ no_region % (TupT [] $ no_region))

let string_of_trace tr =
  String.concat "/" (List.map string_of_trace_entry (List.rev tr.entries))

let trace_log tr str value =
  if !trace then
  (
    let pre = string_of_trace tr in
    let src = rest str in
    let src' =
      if String.length src <= 20
      then Print.string_of_string src
      else Print.string_of_string (String.sub src 0 16) ^ "..."
    in
    let value' =
      if value = "" then ""
      else if String.length value <= 30 then " => " ^ value
      else " => " ^ String.sub value 0 26 ^ "..."
    in
    match prod tr with
    | None ->
      Printf.printf "%s%s @ %s\n%!" pre value' src'
    | Some g ->
      Printf.printf "%s ::= %s%s @ %s\n%!" pre (string_of_sym g) value' src'
  )


(* Results *)

type 'a results =
  | Success of 'a trace * stream * Subst.t * 'a * 'a results Lazy.t
  | Failure of string trace * stream * string

let string_of_results = function
  | Success (tr, _str, _s, v, _tl) -> tr.print v
  | Failure (_tr, _str, msg) -> "fail: " ^ msg

let il_results = function
  | Success (tr, str, _, v, _) ->
    Debug.(fmt "success[%s] @ %s" (tr.print v) (il_text (rest str)))
  | Failure (_, _, msg) -> "failure[" ^ msg ^ "]"

let failure tr str msg =
  Failure ({tr with print = Fun.id}, str, msg)
let unexpected tr str =
  failure tr str ("unexpected " ^ (if eof str then "end of " else "") ^ "input")
let success tr str n s e =
  Success (tr, adv str n, s, e, lazy (unexpected tr str))
let success_final tr str n s e =
  Success (tr, adv str n, s, e, lazy (failure tr str ""))

let trace_result = function
  | Failure (tr, str, msg) as r -> if msg <> "" then trace_log tr str (string_of_results r)
  | Success (tr, str, _, _, _) as r -> trace_log tr str (string_of_results r)

let rec map_results f r =
  match r with
  | Failure _ -> f r
  | Success (tr, str, s, e, tl) ->
    f (Success (tr, str, s, e, lazy (map_results f (Lazy.force tl))))

let rec append_results r1 lr2 =
  match r1 with
  | Failure (_, str1, msg1) ->
    (match Lazy.force lr2 with
    | Failure (_, str2, msg2) when msg2 = "" || msg1 <> "" && pos str1 > pos str2 -> r1
    | r2 -> r2
    )
  | Success (tr, str, s, e, tl) ->
    Success (tr, str, s, e, lazy (append_results (Lazy.force tl) lr2))

(* Using this for bind would implement breadth-first search
let rec interleave_results r1 lr2 =
  match r1 with
  | Failure _ -> Lazy.force lr2
  | Success (str, s, e, tl) ->
    Success (str, s, e, lazy (interleave_results (Lazy.force lr2) tl))
*)

let rec bind_results r f =
  match r with
  | Failure (tr, str, msg) -> Failure (tr, str, msg)  (* need to copy for polymorphism *)
  | Success (_tr, str, s, e, tl) ->
    append_results (f (str, s, e)) (lazy (bind_results (Lazy.force tl) f))

let (let*) = bind_results
let (|||) = append_results


(* Tracing *)

let trace_parse tr str f =
  trace_log tr str "";
  match f tr with
  | r ->
    map_results (function
      | Failure (_tr', str', msg) ->
        let r' = failure tr str' msg in
        trace_result r'; r'
      | Success (_tr', str', s, e, tl) ->
        let r' = Success (tr, str', s, e, tl) in
        trace_result r'; r'
    ) r
  | exception exn ->
    let bt = Printexc.get_raw_backtrace () in
    trace_log tr str ("raise " ^ Printexc.to_string exn);
    Printexc.raise_with_backtrace exn bt

let trace_alt tr str g f =
  trace_parse (alt tr (Some g)) str f


(* Parsing *)

let rec parse_sym env (tr : exp trace) str s g : exp results =
  Debug.(log "il.parse_sym"
    (fun _ -> fmt "%s: %s" (il_sym g) (il_text (rest str))) il_results
  ) @@ fun _ ->
  match g.it with
  | VarG (x, as_) ->
    let* str', _s', e = parse_gram env tr str x as_ in
    let s' = Subst.add_sizeid s x (pos str' - pos str) in
    success tr str' 0 s' e
  | NatG _ when eof str ->
    unexpected tr str
  | NatG b ->
    if get str = b then
      success_final tr str 1 s (NatE (Z.of_int (Char.code b)) $$ at str 1 % g.note)
    else
      failure tr str (Printf.sprintf "byte %s expected" (Print.string_of_byte b))
  | TextG t when t <> "" && eof str ->
    unexpected tr str
  | TextG t ->
    let n = String.length t in
    if rem str >= n && text str n = t then
      success_final tr str n s (TextE t $$ at str n % g.note)
    else
      failure tr str (Printf.sprintf "text %s expected" (Print.string_of_string t))
  | EpsG ->
    success_final tr str 0 s (TupE [] $$ at str 0 % g.note)
  | SeqG [] ->
    success_final tr str 0 s (TupE [] $$ at str 0 % g.note)
  | SeqG (g1::gs) ->
    let* str', s', _e = parse_sym env tr str s g1 in
    parse_sym env tr str' s' {g with it = SeqG gs}
  | AltG gs ->
    let id = "(_|...|_)" $ no_region in
    trace_parse (enter tr id [] Print.string_of_exp) str @@ fun tr' ->
      parse_sym_alts env tr' str s 0 gs
  | RangeG _ when eof str ->
    unexpected tr str
  | RangeG (b1, b2) when b1 <= get str && get str <= b2->
    parse_sym env tr str s (NatG (get str) $$ g.at % g.note)
  | RangeG (b1, b2) ->
    failure tr str (Printf.sprintf "byte %s..%s expected"
      (Print.string_of_byte b1) (Print.string_of_byte b2))
  | IterG (g1, (Opt, _xes)) ->
    let tr' = enter tr (string_of_sym g $ no_region) [] string_of_exps in
    let* str', s', es = parse_sym_list env tr' str s 0 1 g1 in
    let eo = match es with [] -> None | e::_ -> Some e in
    success tr str' 0 s' (OptE eo $$ g.at % g.note)
  | IterG (g1, (List, _xes)) ->
    let tr' = enter tr (string_of_sym g $ no_region) [] string_of_exps in
    let* str', s', es = parse_sym_list env tr' str s 0 max_int g1 in
    success tr str' 0 s' (ListE es $$ g.at % g.note)
  | IterG (g1, (List1, _xes)) ->
    let tr' = enter tr (string_of_sym g $ no_region) [] string_of_exps in
    let* str', s', es = parse_sym_list env tr' str s 1 max_int g1 in
    if es = [] then
      failure tr str "non-empty sequence expected"
    else
      success tr str' 0 s' (ListE es $$ g.at % g.note)
  | IterG (g1, (ListN (en, _ido), _xes)) ->
    (match (Eval.reduce_exp env (Subst.subst_exp s en)).it with
    | NatE n ->
      let tr' = enter tr (string_of_sym g $ no_region) [] string_of_exps in
      let* str', s', es = parse_sym_list env tr' str s (Z.to_int n) (Z.to_int n) g1 in
      success tr str' 0 s' (ListE es $$ g.at % g.note)
    | _ ->
      failure tr str "cannot determine expected length of sequence"
    )
  | AttrG (e, g1) ->
    let* str', s', e' = parse_sym env tr str s g1 in
    match Eval.match_exp env s' e' e with
    | Some s'' -> success_final tr str' 0 s'' e'
    | None -> failure tr str "result does not match attribute pattern"

(*
and parse_sym_opt env (tr : exp option trace) str s g1 : exp option results =
    ( trace_alt tr str (EpsG $$ g1.at % g1.note) @@ fun _tr' ->
        success_final tr str 0 s None
    ) |||
    lazy (
      trace_alt tr str g1 @@ fun tr' ->
        let tr'' = {tr' with print = Print.string_of_exp} in
        let* str', s', e = parse_sym env tr'' str s g1 in
        success tr str' 0 s' (Some e)
    )
*)

and parse_sym_list env (tr : exp list trace) str s m n g1 : exp list results =
  let r1 () =
    ( trace_alt tr str (EpsG $$ g1.at % g1.note) @@ fun _tr' ->
        success_final tr str 0 s []
    )
  in
  let r2 =
    lazy (
      let g' = IterG (g1, (List, [])) $$ g1.at % g1.note in
      trace_alt tr str (SeqG [g1; g'] $$ g1.at % g1.note) @@ fun tr' ->
        let tr1 = {tr' with print = Print.string_of_exp} in
        let* str', s', e = parse_sym env tr1 str s g1 in
        let tr2 = enter tr' (string_of_sym g' $ no_region) [] string_of_exps in
        let* str'', s'', es =
          parse_sym_list env tr2 str' s' (max 0 (m - 1)) (n - 1) g1 in
        success tr str'' 0 s'' (e::es)
    )
  in
    if n = 0 then r1 () else
    if m > 0 then Lazy.force r2 else
    r1 () ||| r2

and parse_sym_alts env tr str s i = function
  | [] -> unexpected tr str
  | g1::[] when i = 0 ->
    trace_alt tr str g1 @@ fun tr' ->
      parse_sym env tr' str s g1  (* preserve error message *)
  | g1::gs' ->
    ( trace_alt tr str g1 @@ fun tr' ->
        parse_sym env tr' str s g1
    ) |||
    lazy (parse_sym_alts env tr str s (i + 1) gs')

and parse_prod env tr str as_ prod =
  let ProdD (_bs, as', g, e, prems) = prod.it in
  Debug.(log "il.parse_prod"
    (fun _ -> fmt "%s -> %s @ %s" (il_sym g) (il_exp e) (il_text (rest str)))
    il_results
  ) @@ fun _ ->
  match Eval.match_list Eval.match_arg env Subst.empty as_ as' with
  | exception Eval.Irred -> failure tr str "irreducible grammar arguments"
  | None -> failure tr str "grammar undefined for arguments"
  | Some s ->
    let g', e', prems' =
      Subst.(subst_sym s g, subst_exp s e, subst_prems s prems) in
    trace_alt tr str g' @@ fun tr' ->
      Debug.(log_in "il.parse_prod" (fun _ -> "arg subst: " ^ mapping il_exp s.varid));
      let* str', s', _e' = parse_sym env tr' str Subst.empty g' in
      Debug.(log_in "il.parse_prod" (fun _ -> "prem subst: " ^ mapping il_exp s'.varid));
      match Eval.reduce_prems env (Subst.subst_prems s' prems') with
      | None -> failure tr' str "cannot verify side condition"
      | Some false -> failure tr' str "violating side condition"
      | Some true ->
        success_final tr' str' 0 Subst.empty (Eval.reduce_exp env (Subst.subst_exp s' e'))

and parse_prods env tr str id as_ i = function
  | [] -> unexpected tr str
  | prod::[] when i = 0 ->
    parse_prod env tr str as_ prod  (* preserve error message *)
  | prod::prods' ->
    parse_prod env tr str as_ prod ||| lazy (parse_prods env tr str id as_ (i + 1) prods')

and parse_gram env tr str id as_ =
  Debug.(log "il.parse_gram"
    (fun _ -> fmt "%s(%s) @ %s" (il_id id) (il_args as_) (il_text (rest str)))
    il_results
  ) @@ fun _ ->
  (* TODO(4, rossberg): rethink evaluation to enforce this better *)
  let as' = List.map (Eval.reduce_arg env) as_ in
  if
    List.exists (fun a ->
      match a.it with
      | ExpA e -> not (Eval.is_normal_exp e)
      | _ -> false
    ) as'
  then
    failure tr str "indeterminate argument values"
  else
    let _ps, _t, prods = Env.find_gram env id in
    trace_parse (enter tr id as' Print.string_of_exp) str @@ fun tr' ->
      parse_prods env tr' str id as' 0 prods


let rec parse_all = function
  | Failure _ as r -> r
  | Success (_, str, _, _, _) as r when eof str -> r
  | Success (tr, str, _, _, tl) ->
    let r = failure (alt tr None) str "end of input expected" in
    trace_result r;
    parse_all (Lazy.force tl) ||| lazy r

exception Grammar_unknown

let parse script name src =
  let env = Env.env_of_script script in
  let id = name $ no_region in
  if not (Env.mem_gram env id) then raise Grammar_unknown else
  match parse_all (parse_gram env empty_trace (stream src) id []) with
  | Failure (_, str, msg) -> Error (pos str, msg)
  | Success (_, _, _, e, _) when not !check_ambiguity -> Ok e
  | Success (_, _, _, e, tl) ->
    match Lazy.force tl with
    | Failure _ -> Ok e
    | Success _ -> Error (0, "ambiguous parse")
