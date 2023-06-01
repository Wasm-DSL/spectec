type ('acc, 't) fold_map = 't -> 'acc -> 't * 'acc

val fold_map :
  ?exp:('acc, Il.Ast.exp) fold_map ->
  ?rule:('acc, Il.Ast.rule) fold_map ->
  ?def:('acc, Il.Ast.def) fold_map ->
  ('acc, Il.Ast.script) fold_map

type 't map = 't -> 't

val map :
  ?exp:Il.Ast.exp map ->
  ?rule:Il.Ast.rule map ->
  ?def:Il.Ast.def map ->
  Il.Ast.script map

type ('acc, 't) fold = 't -> 'acc -> 'acc

val fold :
  ?exp:('acc, Il.Ast.exp) fold ->
  ?rule:('acc, Il.Ast.rule) fold ->
  ?def:('acc, Il.Ast.def) fold ->
  ('acc, Il.Ast.script) fold

type ('env, 't) reader = 'env -> 't -> 't

val reader :
  ?exp:('env, Il.Ast.exp) reader ->
  ?rule:('env, Il.Ast.rule) reader ->
  ?def:('env, Il.Ast.def) reader ->
  ('env, Il.Ast.script) reader
