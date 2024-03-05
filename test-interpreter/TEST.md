# Preview

```sh
$ (cd ../spec && dune exec ../src/exe-watsup/main.exe -- *.watsup -v -l --sideconditions --animate --interpreter --test-interpreter "multi-memory" --root "..") 2>/dev/null
watsup 0.4 generator
== Parsing...
== Elaboration...
== IL Validation...
== Running pass sideconditions...
== IL Validation after pass sideconditions...
== Running pass animate...
Animation failed (binding inference).
if (|ct'*{ct'}| = |y*{y}|)
if (|ct'*{ct'}| = |y'*{y'}*{y'}|)
(if (y < |C.TYPE_context|))*{ct' y y'}
if (|y*{y}| <= 1)
(if (y < x))*{y}
(if ($unrolldt(C.TYPE_context[y]) = SUB_subtype(`FINAL%?`(?()), y'*{y'}, ct')))*{ct' y y'}
Comptype_ok: `%|-%:OK`(C, ct)
(Comptype_sub: `%|-%<:%`(C, ct, ct'))*{ct'}
...Animation failed (reorder)
if (|ct'*{ct'}| = |y*{y}|)
if (|ct'*{ct'}| = |y'*{y'}*{y'}|)
(if (y < |C.TYPE_context|))*{ct' y y'}
if (|y*{y}| <= 1)
(if (y < x))*{y}
(if ($unrolldt(C.TYPE_context[y]) = SUB_subtype(`FINAL%?`(?()), y'*{y'}, ct')))*{ct' y y'}
Comptype_ok: `%|-%:OK`(C, ct)
(Comptype_sub: `%|-%<:%`(C, ct, ct'))*{ct'}
Animation failed (binding inference).
if (|ct'*{ct'}| = |ht*{ht}|)
if (|ct'*{ct'}| = |ht'*{ht'}*{ht'}|)
if (|ht*{ht}| <= 1)
(if $before(ht, x, i))*{ht}
(if ($unrollht(C, ht) = SUBD_subtype(`FINAL%?`(?()), ht'*{ht'}, ct')))*{ct' ht ht'}
Comptype_ok: `%|-%:OK`(C, ct)
(Comptype_sub: `%|-%<:%`(C, ct, ct'))*{ct'}
...Animation failed (reorder)
if (|ct'*{ct'}| = |ht*{ht}|)
if (|ct'*{ct'}| = |ht'*{ht'}*{ht'}|)
if (|ht*{ht}| <= 1)
(if $before(ht, x, i))*{ht}
(if ($unrollht(C, ht) = SUBD_subtype(`FINAL%?`(?()), ht'*{ht'}, ct')))*{ct' ht ht'}
Comptype_ok: `%|-%:OK`(C, ct)
(Comptype_sub: `%|-%<:%`(C, ct, ct'))*{ct'}
Animation failed (binding inference).
if ((n_1 <= n_2) /\ (n_2 <= k))
...Animation failed (reorder)
if (n_1 <= n_2)
if (n_2 <= k)
Animation failed (binding inference).
Valtype_sub: `%|-%<:%`(C, t, t')
if ((t' = (numtype <: valtype)) \/ (t' = (vectype <: valtype)))
...Animation failed (reorder)
Valtype_sub: `%|-%<:%`(C, t, t')
if ((t' = (numtype <: valtype)) \/ (t' = (vectype <: valtype)))
Animation failed (binding inference).
Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*{t_1}, t_2*{t_2}))
Instrs_ok: `%|-%*:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*{t_2}], RETURN ?()}, instr_1*{instr_1}, `%->%*%`(t_1*{t_1}, x_1*{x_1}, t_2*{t_2}))
Instrs_ok: `%|-%*:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*{t_2}], RETURN ?()}, instr_2*{instr_2}, `%->%*%`(t_1*{t_1}, x_2*{x_2}, t_2*{t_2}))
...Animation failed (reorder)
Instrs_ok: `%|-%*:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*{t_2}], RETURN ?()}, instr_1*{instr_1}, `%->%*%`(t_1*{t_1}, x_1*{x_1}, t_2*{t_2}))
Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*{t_1}, t_2*{t_2}))
Instrs_ok: `%|-%*:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*{t_2}], RETURN ?()}, instr_2*{instr_2}, `%->%*%`(t_1*{t_1}, x_2*{x_2}, t_2*{t_2}))
Animation failed (binding inference).
(if (l < |C.LABEL_context|))*{l}
if (l' < |C.LABEL_context|)
(Resulttype_sub: `%|-%*<:%*`(C, t*{t}, C.LABEL_context[l]))*{l}
Resulttype_sub: `%|-%*<:%*`(C, t*{t}, C.LABEL_context[l'])
...Animation failed (reorder)
(if (l < |C.LABEL_context|))*{l}
if (l' < |C.LABEL_context|)
(Resulttype_sub: `%|-%*<:%*`(C, t*{t}, C.LABEL_context[l]))*{l}
Resulttype_sub: `%|-%*<:%*`(C, t*{t}, C.LABEL_context[l'])
Animation failed (binding inference).
if (x < |C.TYPE_context|)
if (y < |C.DATA_context|)
Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(mut, (t <: storagetype))))
if ((t = (numtype <: valtype)) \/ (t = (vectype <: valtype)))
if (C.DATA_context[y] = OK)
...Animation failed (reorder)
if (x < |C.TYPE_context|)
if (y < |C.DATA_context|)
if ($expanddt(C.TYPE_context[x]) = ARRAY_comptype(`%%`(mut, (t <: storagetype))))
if ((t = (numtype <: valtype)) \/ (t = (vectype <: valtype)))
if (C.DATA_context[y] = OK)
Animation failed (binding inference).
if (x < |C.TYPE_context|)
Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(`MUT%?`(?(())), zt)))
...Animation failed (reorder)
where $expanddt(C.TYPE_context[x]) = ARRAY_comptype(`%%`(`MUT%?`(?(())), zt))
if (x < |C.TYPE_context|)
Animation failed (binding inference).
if (x < |C.TYPE_context|)
if (y < |C.DATA_context|)
Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(`MUT%?`(?(())), zt)))
if ((t = (numtype <: valtype)) \/ (t = (vectype <: valtype)))
if (C.DATA_context[y] = OK)
...Animation failed (reorder)
if (x < |C.TYPE_context|)
if (y < |C.DATA_context|)
if ($expanddt(C.TYPE_context[x]) = ARRAY_comptype(`%%`(`MUT%?`(?(())), zt)))
if ((t = (numtype <: valtype)) \/ (t = (vectype <: valtype)))
if (C.DATA_context[y] = OK)
Animation failed (binding inference).
if (x < |C.MEM_context|)
if ((n?{n} = ?()) <=> (sx?{sx} = ?()))
if (C.MEM_context[x] = mt)
if ((2 ^ n_A) <= ($size(nt <: valtype) / 8))
(if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(nt <: valtype) / 8))))?{n}
if ((n?{n} = ?()) \/ (nt = (inn <: numtype)))
...Animation failed (reorder)
if (x < |C.MEM_context|)
if ((n?{n} = ?()) <=> (sx?{sx} = ?()))
if (C.MEM_context[x] = mt)
if ((2 ^ n_A) <= ($size(nt <: valtype) / 8))
(if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(nt <: valtype) / 8))))?{n}
if ((n?{n} = ?()) \/ (nt = (inn <: numtype)))
Animation failed (binding inference).
if (x < |C.MEM_context|)
if (C.MEM_context[x] = mt)
if ((2 ^ n_A) <= ($size(nt <: valtype) / 8))
(if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(nt <: valtype) / 8))))?{n}
if ((n?{n} = ?()) \/ (nt = (inn <: numtype)))
...Animation failed (reorder)
if (x < |C.MEM_context|)
if (C.MEM_context[x] = mt)
if ((2 ^ n_A) <= ($size(nt <: valtype) / 8))
(if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(nt <: valtype) / 8))))?{n}
if ((n?{n} = ?()) \/ (nt = (inn <: numtype)))
== IL Validation after pass animate...
== Translating to AL...
...Animation failed (reorder)
if (a < |$funcinst(z)|)
where fi = $funcinst(z)[a]
where FUNC_comptype(`%->%`(t_1^n{t_1}, t_2^m{t_2})) = $expanddt(fi.TYPE_funcinst)
where `FUNC%%*%`(x', LOCAL(t)*{t}, instr*{instr}) = fi.CODE_funcinst
where f = {LOCAL ?(val)^n{val} :: $default(t)*{t}, MODULE fi.MODULE_funcinst}
where (val <: admininstr)^n{val} :: [REF.FUNC_ADDR_admininstr(a) CALL_REF_admininstr(x?{x})] = u_0*{u_0}
...Animation failed (reorder)
if (a < |$funcinst(z)|)
where FUNC_comptype(`%->%`(t_1^n{t_1}, t_2^m{t_2})) = $expanddt($funcinst(z)[a].TYPE_funcinst)
where FRAME__admininstr(k, f, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [REF.FUNC_ADDR_admininstr(a)] :: [RETURN_CALL_REF_admininstr(x?{x})] :: (instr <: admininstr)*{instr}) = u_2
== Initializing AL interprter with generated AL...
== Interpreting AL...
===== memory_size1.wast =====
- 14/14 (100.00%)

===== memory_size0.wast =====
- 7/7 (100.00%)

===== memory-multi.wast =====
- 4/4 (100.00%)

===== imports1.wast =====
- 4/4 (100.00%)

===== linking0.wast =====
- 3/3 (100.00%)

===== memory_copy0.wast =====
- 28/28 (100.00%)

===== address0.wast =====
- 91/91 (100.00%)

===== align0.wast =====
- 4/4 (100.00%)

===== memory_init0.wast =====
- 12/12 (100.00%)

===== load2.wast =====
- 37/37 (100.00%)

===== float_exprs0.wast =====
- 13/13 (100.00%)

===== float_exprs1.wast =====
- 2/2 (100.00%)

===== data1.wast =====
- 14/14 (100.00%)

===== memory_copy1.wast =====
- 13/13 (100.00%)

===== address1.wast =====
- 126/126 (100.00%)

===== linking1.wast =====
- 9/9 (100.00%)

===== linking2.wast =====
- 8/8 (100.00%)

===== float_memory0.wast =====
- 28/28 (100.00%)

===== start0.wast =====
- 8/8 (100.00%)

===== load0.wast =====
- 2/2 (100.00%)

===== memory_trap0.wast =====
- 13/13 (100.00%)

===== imports4.wast =====
- 8/8 (100.00%)

===== memory_trap1.wast =====
- 167/167 (100.00%)

===== load1.wast =====
- 15/15 (100.00%)

===== memory_fill0.wast =====
- 15/15 (100.00%)

===== linking3.wast =====
- 9/9 (100.00%)

===== data_drop0.wast =====
- 10/10 (100.00%)

===== store0.wast =====
- 4/4 (100.00%)

===== imports2.wast =====
- 8/8 (100.00%)

===== traps0.wast =====
- 14/14 (100.00%)

===== memory_size2.wast =====
- 20/20 (100.00%)

===== store1.wast =====
- 8/8 (100.00%)

Total [718/718] (100.00%; Normalized 100.00%)
== Complete.
```
