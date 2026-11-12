import «wasm2.0»
def mkFunctype (tf1 tf2 : List valtype) : functype :=
    functype.mk_functype (list.mk_list tf1) (list.mk_list tf2)

def resulttypeSub (t1s t2s : List valtype) : Prop :=
    Resulttype_sub (list.mk_list t1s) (list.mk_list t2s)

infix:67 "f->" => mkFunctype
infix:50 "sub<" => Valtype_sub
infix:40 "subs<" => resulttypeSub
infix:30 "ftsub<" => Functype_sub

def prepend_label (C : context) (t : resulttype) : context :=
    { C with LABELS := t :: C.LABELS }
