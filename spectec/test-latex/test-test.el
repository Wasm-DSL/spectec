== Parsing...
var XYZ : nat
def $test_sub_ATOM_22(nat : nat) : nat
def $test_sub_ATOM_22(n_1_xyz_y) = 0
def $test_sub_ATOM_22(n_2_XYZ_y) = 0
def $test_sub_ATOM_22(n_3_ATOM_y) = 0
def $curried_(nat : nat, nat : nat) : nat
def $curried_(n_1, n_2) = n_1 + n_2
syntax testfuse = | {AB_ nat nat nat} | {CD nat nat nat} | {EF nat nat nat} | {GH nat nat nat} | {IJ nat nat nat} | {KL nat nat nat} | {MN nat nat nat} | {OP nat nat nat} | {QR nat nat nat}



syntax InfixArrow = | nat* ->_ {(nat*) nat*}
syntax InfixArrow2 = | nat* =>_ {(nat*) nat*}
syntax AtomArrow = {nat? ->_ (nat*) nat*}
syntax AtomArrow2 = {nat? =>_ (nat*) nat*}
def $InfixArrow(InfixArrow : InfixArrow) : nat
def $InfixArrow(a ->_ c) = 0
def $InfixArrow(a ->_ {c b}) = 0
def $InfixArrow(a ->_ {(c*) b}) = 0
def $InfixArrow(a ->_ {c b_1 b_2}) = 0
def $InfixArrow(a ->_ {(c*) b_1 b_2}) = 0
def $InfixArrow(a ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $InfixArrow({} ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $InfixArrow2(InfixArrow2 : InfixArrow2) : nat
def $InfixArrow2(a =>_ c) = 0
def $InfixArrow2(a =>_ {c b}) = 0
def $InfixArrow2(a =>_ {(c*) b}) = 0
def $InfixArrow2(a =>_ {c b_1 b_2}) = 0
def $InfixArrow2(a =>_ {(c*) b_1 b_2}) = 0
def $InfixArrow2(a =>_ {({c_1 c_2}) b_1 b_2}) = 0
def $InfixArrow2({} =>_ {({c_1 c_2}) b_1 b_2}) = 0
def $AtomArrow(AtomArrow : AtomArrow) : nat
def $AtomArrow({a ->_ c}) = 0
def $AtomArrow({a ->_ c b}) = 0
def $AtomArrow({a ->_ (c*) b}) = 0
def $AtomArrow({a ->_ c b_1 b_2}) = 0
def $AtomArrow({a ->_ (c*) b_1 b_2}) = 0
def $AtomArrow({a ->_ ({c_1 c_2}) b_1 b_2}) = 0
def $AtomArrow({->_ ({c_1 c_2}) b_1 b_2}) = 0
def $AtomArrow2(AtomArrow2 : AtomArrow2) : nat
def $AtomArrow2({a =>_ c}) = 0
def $AtomArrow2({a =>_ c b}) = 0
def $AtomArrow2({a =>_ (c*) b}) = 0
def $AtomArrow2({a =>_ c b_1 b_2}) = 0
def $AtomArrow2({a =>_ (c*) b_1 b_2}) = 0
def $AtomArrow2({a =>_ ({c_1 c_2}) b_1 b_2}) = 0
def $AtomArrow2({=>_ ({c_1 c_2}) b_1 b_2}) = 0
syntax MacroInfixArrow = | nat* ->_ {nat* nat*}
syntax MacroAtomArrow = | nat* ->_ {nat* nat*}
def $MacroInfixArrow(MacroInfixArrow : MacroInfixArrow) : nat
def $MacroInfixArrow(a ->_ c) = 0
def $MacroInfixArrow(a ->_ {c b}) = 0
def $MacroInfixArrow(a ->_ {(c*) b}) = 0
def $MacroInfixArrow(a ->_ {c b_1 b_2}) = 0
def $MacroInfixArrow(a ->_ {(c*) b_1 b_2}) = 0
def $MacroInfixArrow(a ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $MacroInfixArrow({} ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $MacroAtomArrow(MacroAtomArrow : MacroAtomArrow) : nat
def $MacroAtomArrow(a ->_ c) = 0
def $MacroAtomArrow(a ->_ {c b}) = 0
def $MacroAtomArrow(a ->_ {(c*) b}) = 0
def $MacroAtomArrow(a ->_ {c b_1 b_2}) = 0
def $MacroAtomArrow(a ->_ {(c*) b_1 b_2}) = 0
def $MacroAtomArrow(a ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $MacroAtomArrow({} ->_ {({c_1 c_2}) b_1 b_2}) = 0
syntax ShowInfixArrow = | nat* ->_ {nat* nat*}
syntax ShowAtomArrow = | nat* ->_ {nat* nat*}
def $ShowInfixArrow(ShowInfixArrow : ShowInfixArrow) : nat
def $ShowInfixArrow(a ->_ c) = 0
def $ShowInfixArrow(a ->_ {c b}) = 0
def $ShowInfixArrow(a ->_ {(c*) b}) = 0
def $ShowInfixArrow(a ->_ {c b_1 b_2}) = 0
def $ShowInfixArrow(a ->_ {(c*) b_1 b_2}) = 0
def $ShowInfixArrow(a ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $ShowInfixArrow({} ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $ShowAtomArrow(ShowAtomArrow : ShowAtomArrow) : nat
def $ShowAtomArrow(a ->_ c) = 0
def $ShowAtomArrow(a ->_ {c b}) = 0
def $ShowAtomArrow(a ->_ {(c*) b}) = 0
def $ShowAtomArrow(a ->_ {c b_1 b_2}) = 0
def $ShowAtomArrow(a ->_ {(c*) b_1 b_2}) = 0
def $ShowAtomArrow(a ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $ShowAtomArrow({} ->_ {({c_1 c_2}) b_1 b_2}) = 0
syntax ShowMacroInfixArrow = | nat* ->_ {nat* nat*}
syntax ShowMacroAtomArrow = | nat* ->_ {nat* nat*}
def $ShowMacroInfixArrow(ShowMacroInfixArrow : ShowMacroInfixArrow) : nat
def $ShowMacroInfixArrow(a ->_ c) = 0
def $ShowMacroInfixArrow(a ->_ {c b}) = 0
def $ShowMacroInfixArrow(a ->_ {(c*) b}) = 0
def $ShowMacroInfixArrow(a ->_ {c b_1 b_2}) = 0
def $ShowMacroInfixArrow(a ->_ {(c*) b_1 b_2}) = 0
def $ShowMacroInfixArrow(a ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $ShowMacroInfixArrow({} ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $ShowMacroAtomArrow(ShowMacroAtomArrow : ShowMacroAtomArrow) : nat
def $ShowMacroAtomArrow(a ->_ c) = 0
def $ShowMacroAtomArrow(a ->_ {c b}) = 0
def $ShowMacroAtomArrow(a ->_ {(c*) b}) = 0
def $ShowMacroAtomArrow(a ->_ {c b_1 b_2}) = 0
def $ShowMacroAtomArrow(a ->_ {(c*) b_1 b_2}) = 0
def $ShowMacroAtomArrow(a ->_ {({c_1 c_2}) b_1 b_2}) = 0
def $ShowMacroAtomArrow({} ->_ {({c_1 c_2}) b_1 b_2}) = 0






syntax xfoo = | XFOONULL | {XFOOUN0 nat} | {XFOOUN1N nat} | {XFOOUN11 nat} | {XFOOUNREST nat} | {XFOOBIN0 nat nat} | {XFOOBIN1N nat nat} | {XFOOBIN11 nat nat} | {XFOOBIN1N2N nat nat} | {XFOOBIN1N22 nat nat} | {XFOOBIN112N nat nat} | {XFOOBIN1122 nat nat} | {XFOOBIN22 nat nat} | {XFOOBIN2211 nat nat} | {XFOOBINREST nat nat} | {XFOOBIN1NREST nat nat} | {XFOOBIN11REST nat nat} | {XFOOBIN22REST nat nat} | {XFOOBIN1N2NREST nat nat} | {XFOOBIN1122REST nat nat} | {XFOOBIN2211REST nat nat} | {XFOONAME1N2NREST nat nat} | {XFOONAME1122REST nat nat} | {XFOONAME2211REST nat nat}
syntax xxfoo = {xfoo nat}
syntax xxxfoo = {nat xfoo nat}
def $xfoo(xfoo : xfoo) : nat
def $xfoo(XFOONULL) = 0
def $xfoo({XFOOUN0 2}) = 0
def $xfoo({XFOOUN1N 2}) = 0
def $xfoo({XFOOUN11 2}) = 0
def $xfoo({XFOOUNREST 2}) = 0
def $xfoo({XFOOBIN0 2 3}) = 0
def $xfoo({XFOOBIN1N 2 3}) = 0
def $xfoo({XFOOBIN11 2 3}) = 0
def $xfoo({XFOOBIN1N2N 2 3}) = 0
def $xfoo({XFOOBIN1N22 2 3}) = 0
def $xfoo({XFOOBIN112N 2 3}) = 0
def $xfoo({XFOOBIN1122 2 3}) = 0
def $xfoo({XFOOBIN22 2 3}) = 0
def $xfoo({XFOOBIN2211 2 3}) = 0
def $xfoo({XFOOBINREST 2 3}) = 0
def $xfoo({XFOOBIN1NREST 2 3}) = 0
def $xfoo({XFOOBIN11REST 2 3}) = 0
def $xfoo({XFOOBIN22REST 2 3}) = 0
def $xfoo({XFOOBIN1N2NREST 2 3}) = 0
def $xfoo({XFOOBIN1122REST 2 3}) = 0
def $xfoo({XFOOBIN2211REST 2 3}) = 0
def $xfoo({XFOONAME1N2NREST 2 3}) = 0
def $xfoo({XFOONAME1122REST 2 3}) = 0
def $xfoo({XFOONAME2211REST 2 3}) = 0
def $xxfoo(xxfoo : xxfoo) : nat
def $xxfoo({XFOONULL 9}) = 0
def $xxxfoo(xxxfoo : xxxfoo) : nat
def $xxxfoo({1 XFOONULL 9}) = 0






syntax fii = | FII
syntax faa = | FAA
syntax foo = | FOO
syntax fuu = | FUU
syntax bar = | BAR
syntax boo = | BOO
syntax baz = | BAZ
syntax boi = | BOI
def $macros1 : nat
def $macros1 = 0
  -- if fii = FII
  -- if faa = FAA
  -- if foo = FOO
  -- if fuu = FUU
  -- if bar = BAR
  -- if boo = BOO
  -- if baz = BAZ
  -- if boi = BOI
syntax ufii_(nat_1, nat_2) = | UFII
syntax ufaa_(nat_1, nat_2) = | UFAA
syntax ufoo_(nat_1, nat_2) = | UFOO
syntax ufuu_(nat_1, nat_2) = | UFUU
syntax ubar_(nat_1, nat_2) = | UBAR
syntax uboo_(nat_1, nat_2) = | UBOO
syntax ubaz_(nat_1, nat_2) = | UBAZ
syntax uboi_(nat_1, nat_2) = | UBOI
def $macros2 : nat
def $macros2 = 0
  -- var ufii: ufii_(0, 0)
  -- if ufii = UFII
  -- var ufaa: ufaa_(0, 0)
  -- if ufaa = UFAA
  -- var ufoo: ufoo_(0, 0)
  -- if ufoo = UFOO
  -- var ufuu: ufuu_(0, 0)
  -- if ufuu = UFUU
  -- var ubar: ubar_(0, 0)
  -- if ubar = UBAR
  -- var uboo: uboo_(0, 0)
  -- if uboo = UBOO
  -- var ubaz: ubaz_(0, 0)
  -- if ubaz = UBAZ
  -- var uboi: uboi_(0, 0)
  -- if uboi = UBOI



def $fii : nat
def $fii = 0
def $faa : nat
def $faa = 0
def $foo : nat
def $foo = 0
def $fuu : nat
def $fuu = 0
def $bar : nat
def $bar = 0
def $boo : nat
def $boo = 0
def $baz : nat
def $baz = 0
def $boi : nat
def $boi = 0
def $ufii_(nat_1 : nat, nat_2 : nat) : nat
def $ufii_(x, y) = 0
def $ufaa_(nat_1 : nat, nat_2 : nat) : nat
def $ufaa_(x, y) = 0
def $ufoo_(nat_1 : nat, nat_2 : nat) : nat
def $ufoo_(x, y) = 0
def $ufuu_(nat_1 : nat, nat_2 : nat) : nat
def $ufuu_(x, y) = 0
def $ubar_(nat_1 : nat, nat_2 : nat) : nat
def $ubar_(x, y) = 0
def $uboo_(nat_1 : nat, nat_2 : nat) : nat
def $uboo_(x, y) = 0
def $ubaz_(nat_1 : nat, nat_2 : nat) : nat
def $ubaz_(x, y) = 0
def $uboi_(nat_1 : nat, nat_2 : nat) : nat
def $uboi_(x, y) = 0
def $foo__bar : nat
def $foo__bar = 0
def $foo_boo : nat
def $foo_boo = 0
def $ufoo__bar_(nat_1 : nat, nat_2 : nat) : nat
def $ufoo__bar_(x, y) = 0
def $ufoo_boo_(nat_1 : nat, nat_2 : nat) : nat
def $ufoo_boo_(x, y) = 0



syntax parent = | AA | AAX | AAY | AAZ | BB | BBX | BBY | BBZ | {CC nat CCCC} | {CCX nat CCXX} | {CCY nat CCYY} | {CCZ nat CCZZ} | {DD nat} | {DDX nat} | {DDY nat} | {DDZ nat} | {EE nat} | {EEX nat} | {EEY nat} | {EEZ nat}
def $parent(parent : parent) : nat
def $parent(AA) = 0
def $parent(AAX) = 0
def $parent(AAY) = 0
def $parent(AAZ) = 0
def $parent(BB) = 0
def $parent(BBX) = 0
def $parent(BBY) = 0
def $parent(BBZ) = 0
def $parent({CC n CCCC}) = 0
def $parent({CCX n CCXX}) = 0
def $parent({CCY n CCYY}) = 0
def $parent({CCZ n CCZZ}) = 0
def $parent({DD n}) = 0
def $parent({DDX n}) = 0
def $parent({DDY n}) = 0
def $parent({DDZ n}) = 0
def $parent({EE n}) = 0
def $parent({EEX n}) = 0
def $parent({EEY n}) = 0
def $parent({EEZ n}) = 0
syntax parentimplicit(syntax t) = | PP | PPX | PPY | PPZ | QQ | QQX | QQY | QQZ | {RR t} | {RRX t} | {RRY t} | {RRZ t}
def $parentimpl(parentimplicit : parentimplicit(text)) : nat
def $parentimpl(PP) = 0
def $parentimpl(PPX) = 0
def $parentimpl(PPY) = 0
def $parentimpl(PPZ) = 0
def $parentimpl(QQ) = 0
def $parentimpl(QQX) = 0
def $parentimpl(QQY) = 0
def $parentimpl(QQZ) = 0
def $parentimpl({RR n}) = 0
def $parentimpl({RRX n}) = 0
def $parentimpl({RRY n}) = 0
def $parentimpl({RRZ n}) = 0
syntax indirect = parentimplicit(nat)
def $indirect(indirect : indirect) : nat
def $indirect(PP) = 0
def $indirect(PPX) = 0
def $indirect(PPY) = 0
def $indirect(PPZ) = 0
def $indirect(QQ) = 0
def $indirect(QQX) = 0
def $indirect(QQY) = 0
def $indirect(QQZ) = 0
def $indirect({RR n}) = 0
def $indirect({RRX n}) = 0
def $indirect({RRY n}) = 0
def $indirect({RRZ n}) = 0
syntax family(nat : nat)
syntax family(0) = | FF
syntax family(1) = | GG
syntax family(2) = | HH
def $family(nat : nat, family : family(nat)) : nat
def $family(0, FF) = 0
def $family(1, GG) = 0
def $family(2, HH) = 0
syntax child = | parent | family(0) | indirect | ZZZ
def $child(child : child) : nat
def $child(AA) = 0
def $child(AAX) = 0
def $child(AAY) = 0
def $child(AAZ) = 0
def $child(BB) = 0
def $child(BBX) = 0
def $child(BBY) = 0
def $child(BBZ) = 0
def $child({CC n CCCC}) = 0
def $child({CCX n CCXX}) = 0
def $child({CCY n CCYY}) = 0
def $child({CCZ n CCZZ}) = 0
def $child({DD n}) = 0
def $child({DDX n}) = 0
def $child({DDY n}) = 0
def $child({DDZ n}) = 0
def $child({EE n}) = 0
def $child({EEX n}) = 0
def $child({EEY n}) = 0
def $child({EEZ n}) = 0
def $child(FF) = 0
def $child(PP) = 0
def $child(PPX) = 0
def $child(PPY) = 0
def $child(PPZ) = 0
def $child(QQ) = 0
def $child(QQX) = 0
def $child(QQY) = 0
def $child(QQZ) = 0
def $child({RR n}) = 0
def $child({RRX n}) = 0
def $child({RRY n}) = 0
def $child({RRZ n}) = 0
def $child(ZZZ) = 0
syntax grandchild = | child | ZZZZ
def $grandchild(grandchild : grandchild) : nat
def $grandchild(AA) = 0
def $grandchild(AAX) = 0
def $grandchild(AAY) = 0
def $grandchild(AAZ) = 0
def $grandchild(BB) = 0
def $grandchild(BBX) = 0
def $grandchild(BBY) = 0
def $grandchild(BBZ) = 0
def $grandchild({CC n CCCC}) = 0
def $grandchild({CCX n CCXX}) = 0
def $grandchild({CCY n CCYY}) = 0
def $grandchild({CCZ n CCZZ}) = 0
def $grandchild({DD n}) = 0
def $grandchild({DDX n}) = 0
def $grandchild({DDY n}) = 0
def $grandchild({DDZ n}) = 0
def $grandchild({EE n}) = 0
def $grandchild({EEX n}) = 0
def $grandchild({EEY n}) = 0
def $grandchild({EEZ n}) = 0
def $grandchild(FF) = 0
def $grandchild(PP) = 0
def $grandchild(PPX) = 0
def $grandchild(PPY) = 0
def $grandchild(PPZ) = 0
def $grandchild(QQ) = 0
def $grandchild(QQX) = 0
def $grandchild(QQY) = 0
def $grandchild(QQZ) = 0
def $grandchild({RR n}) = 0
def $grandchild({RRX n}) = 0
def $grandchild({RRY n}) = 0
def $grandchild({RRZ n}) = 0
def $grandchild(ZZZ) = 0
def $grandchild(ZZZZ) = 0



syntax rec = {FA nat*, FB nat*, FC nat*, FD nat*, FE nat*, FF nat*, FG nat*, FH nat*}
def $proj(rec : rec, nat : nat) : nat*
def $proj(r, 0) = r.FA
def $proj(r, 1) = r.FB
def $proj(r, 2) = r.FC
def $proj(r, 3) = r.FD
def $proj(r, 4) = r.FE
def $proj(r, 5) = r.FF
def $proj(r, 6) = r.FG
def $proj(r, 7) = r.FH
def $upd(rec : rec, nat : nat) : rec
def $upd(r, 0) = r[FA = 0]
def $upd(r, 1) = r[FB = 0]
def $upd(r, 2) = r[FC = 0]
def $upd(r, 3) = r[FD = 0]
def $upd(r, 4) = r[FE = 0]
def $upd(r, 5) = r[FF = 0]
def $upd(r, 6) = r[FG = 0]
def $upd(r, 7) = r[FH = 0]
def $ext(rec : rec, nat : nat) : rec
def $ext(r, 0) = r[FA =++ 0]
def $ext(r, 1) = r[FB =++ 0]
def $ext(r, 2) = r[FC =++ 0]
def $ext(r, 3) = r[FD =++ 0]
def $ext(r, 4) = r[FE =++ 0]
def $ext(r, 5) = r[FF =++ 0]
def $ext(r, 6) = r[FG =++ 0]
def $ext(r, 7) = r[FH =++ 0]
syntax recimpl = {FIA nat*, FIB nat*, FIC nat*, FID nat*, FIE nat*, FIF nat*, FIG nat*, FIH nat*}
def $rproj(recimpl : recimpl, nat : nat) : nat*
def $rproj(r, 0) = r.FIA
def $rproj(r, 1) = r.FIB
def $rproj(r, 2) = r.FIC
def $rproj(r, 3) = r.FID
def $rproj(r, 4) = r.FIE
def $rproj(r, 5) = r.FIF
def $rproj(r, 6) = r.FIG
def $rproj(r, 7) = r.FIH



syntax cona = {nat COA nat}
syntax conb = {nat COB nat}
syntax conc = {nat COC nat}
syntax cond = {nat COD nat}
syntax cone = {nat COE nat}
syntax conf = {nat COF nat}
syntax cong = {nat COG nat}
syntax conh = {nat COH nat}



syntax C = {}
relation Rok: C |- parent : OK
relation Rsub: C |- parent <: parent
relation Reval: parent ; child ~> parent ; child
rule Rok:
  C |- AA : OK
rule Rsub:
  C |- parent <: AA
rule Reval:
  parent ; child ~> AA ; BB
relation Rok_macro: C |- parent : OK
relation Rsub_macro: C |- parent <: parent
relation Reval_macro: parent ; child ~> parent ; child
rule Rok_macro:
  C |- AA : OK
rule Rsub_macro:
  C |- parent <: AA
rule Reval_macro:
  parent ; child ~> AA ; BB
relation Rok_nomacro: C |- parent : OK
relation Rsub_nomacro: C |- parent <: parent
relation Reval_nomacro: parent ; child ~> parent ; child
rule Rok_nomacro:
  C |- AA : OK
rule Rsub_nomacro:
  C |- parent <: AA
rule Reval_nomacro:
  parent ; child ~> AA ; BB






syntax argh = | ARGH
syntax borg = | BORG
syntax curb = | CURB
syntax dork = | DORK
syntax eerk = | EERK



syntax dotstypex/1 = | argh | DX1 | ...
syntax dotstypey/1 = | argh | DY1 | ...
syntax dotstypex/2 = | ... | borg | DX2 | ...
syntax dotstypesep = borg
syntax dotstypex/3 = | ... | curb | DX3 | DX4 | DX5 | DX6 | ...
syntax dotstypey/2 = | ... | borg | DY2 | DY3 | DY4 | ...
syntax dotstypex/4 = | ... | dork | DX7
syntax dotstypey/3 = | ... | dork | DY5



syntax casetype = | {LA nat argh}
  -- if nat = 0
  -- if argh =/= ARGH | {LB borg curb} | {LC dork_1 dork_2}
  -- if dork_1 =/= dork_2 | {LD argh nat}
  -- if nat > 0
  -- if argh =/= ARGH | {LE nat_1 nat_2}
  -- if nat_1 <= nat_2 | {LFA borg} | {LFB borg} | {LFC borg} | {LH borg argh eerk} | {LI borg argh eerk}
  -- if 0 < 1
  -- if 1 > 0 | {LJ borg}
  -- if 0 < 1
  -- if 1 > 0 | {LK borg argh eerk}
  -- if 0 < 1
  -- if 1 > 0



grammar gram : nat* = 
  | {"GA" "GB"} => 0
    -- if 0 < 1
  (; \n ;)
  | {"GB" "GC" "GD"} => 0
  (; \n ;)
  | {"GC" "GD"} => 0
    -- if 0 < 1
  (; \n ;)
  | {"GD" "GE"} => 0
    -- if 0 < 1
    -- if 1 > 0
  (; \n ;)
  | {"GE" "GF"} => 0
    -- if 0 < 1
  (; \n ;)
  | {"GFA" "GF"} => 0
  | {"GFB" "GF"} => 1
  | "GFC" => 2
  (; \n ;)
  | "GG" => 0
    -- if 1 > 0
  (; \n ;)
  | "GH" => 0
    -- if 1 > 0
  (; \n ;)
  | "GI" => {0 1 2}
    -- if 0 < 1
    -- if 1 > 0
  (; \n ;)
  | {"GJ" "GJ" "G" "J"} => 0
  (; \n ;)
  | {"GK" "GJ" "G" "J"} => 0
    -- if 0 < 1
    -- if 1 > 0
  (; \n ;)
  | "GI" => {0 1 2}
    ----
    -- if 0 < 1
    -- if 1 > 0
  (; \n ;)
  | "GI" => {0 1 2}
    ----
    -- if 0 < 1
    -- if 1 > 0



def $func(nat : nat, nat : nat) : nat*
def $func(n, m) = 0
def $func(n, m) = 0
  -- if n < m
def $func(n, m) = 0
  -- if n > m
  -- if m < n
def $func(n, m) = {0 1}
  -- if n < m
  -- if m > n
def $func(n, m) = {0 1}
  -- if n < m
  -- if m > n
def $func(n, m) = {0 1 2}
  -- if n < m
  -- if m > n
def $func(n, m) = {0 1 2}
  -- if n < m
  -- if m > n
def $func(n, m) = {0 1 2}
  -- if n < m
  -- if m > n



relation Rel: {argh borg} -> {curb dork}
rule Rel/A:
  {argh borg} -> {curb dork}
rule Rel/B:
  {argh borg} -> {curb dork}
  -- if 0 < 1
rule Rel/C:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0
rule Rel/D:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0
rule Rel/E:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0
rule Rel/F:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0
rule Rel/G:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0
rule Rel/DD:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0
rule Rel/EE:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0
rule Rel/FF:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0
rule Rel/GG:
  {argh borg} -> {curb dork}
  -- if 0 < 1
  -- if 1 > 0

== Elaboration...
== IL Validation...
== Latex Generation...
== Complete.
