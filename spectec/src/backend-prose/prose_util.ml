open Util.Source

let extract_desc_hint = List.find_map (function
  | El.Ast.{ hintid = id; hintexp = { it = TextE desc; _ } }
    when id.it = "desc" -> Some desc
  | _ -> None)
let rec extract_desc typ = match typ.it with
  | Il.Ast.IterT (typ, _) -> extract_desc typ ^ " sequence"
  | _ ->
    let name = Il.Print.string_of_typ typ in
    match !Langs.el |> List.find_map (fun def ->
      match def.it with
      | El.Ast.TypD (id, subid, _, _, hints)
      | El.Ast.HintD {it = TypH (id, subid, hints); _}
        when id.it = name && (List.mem subid.it [""; "syn"]) ->
        extract_desc_hint hints
      | _ -> None)
    with
    | Some desc -> desc
    | None -> name