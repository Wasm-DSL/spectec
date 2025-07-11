open Value
open Instance

exception Link of Source.region * string
exception Trap of Source.region * string
exception Exception of Source.region * string
exception Crash of Source.region * string
exception Exhaustion of Source.region * string

val init : Ast.module_ -> extern list -> moduleinst (* raises Link, Trap *)
val invoke : funcinst -> value list -> value list (* raises Trap *)
