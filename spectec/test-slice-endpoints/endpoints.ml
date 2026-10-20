open Util.Source
open Il.Ast
let at = no_region
let nat = NumT `NatT $ at
let ns = IterT (nat, List) $ at
let n i = NumE (`Nat (Z.of_int i)) $$ at % nat
let xs l = ListE (List.map n l) $$ at % ns
let run e = Il.Eval.reduce_exp Il.Env.empty e
let check tag e expected =
  match run e, expected with
  | Ok r, Some values when Il.Eq.eq_exp r (xs values) -> ()
  | Error _, None -> ()
  | _ -> failwith tag
let () =
  List.iter (fun (i,w,expected) ->
    check "slice" (SliceE (xs [1;2;3;4], n i, n w) $$ at % ns) expected)
    [1,2,Some [2;3]; 3,1,Some [4]; 0,4,Some [1;2;3;4];
     4,0,Some []; 4,1,None; 5,0,None; 3,2,None];
  List.iter (fun (i,w,r,expected) ->
    let p = SliceP (RootP $$ at % ns, n i, n w) $$ at % ns in
    check "update" (UpdE (xs [1;2;3;4], p, xs r) $$ at % ns) expected)
    [1,1,[9],Some [1;9;3;4]; 3,1,[9],Some [1;2;3;9];
     0,4,[9;8;7;6],Some [9;8;7;6]; 4,0,[],Some [1;2;3;4];
     4,1,[9],None; 5,0,[],None; 3,2,[9;8],None];
  print_endline "SLICE-ENDPOINTS-OK 14"
