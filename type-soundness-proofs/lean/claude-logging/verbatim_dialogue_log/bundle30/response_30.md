# Response 30 (verbatim)

---

The `≠ none` premises come from the Sideconditions pass, and the pass never looks at one place: the source expression of an iteration (the `e` in `…*{x <- e}`). In the float ops, TypeFamilyRemoval puts the `!` exactly there. In the integer ops it sits in the iteration body, which the pass does visit. Pass order has nothing to do with it; OLD has the same gap.

**What creates the premises**
- The `!` isn't in the spec; TypeFamilyRemoval (pass 03) adds it. `lane_` is a type family, so each lane is projected to the `iN`/`fN` the operator takes, using `!($proj_lane__0(Jnn, lane_1))`. The result is wrapped back with `mk_lane__0_lane_`. The Lean backend prints IL `!e` as `Option.get! e`.
- Sideconditions adds `e =/= ?()` for every `!e` it visits ([sideconditions.ml:60-61](spectec/src/middlend/sideconditions.ml#L60-L61)). If the `!e` is inside an iteration, the premise is iterated too ([lines 64-73](spectec/src/middlend/sideconditions.ml#L64-L73)). In Lean that becomes `Forall (fun l => (proj_lane__0 l) ≠ none) lane_1_lst` ([wasm2.0.lean:5968](spectec/src/test-lean-claude/wasm2.0.lean#L5968)). The length premises beside it come from the same pass (`iter_side_conditions`, lines 39-46).

**Why the integer ops have it and the float ops don't**
1. The spec gives them different result types:
   - `$iabs_ : iN(N)` returns one value ([3-numerics.spectec:132](specification/wasm-2.0/3-numerics.spectec#L132)).
   - `$fabs_ : fN(N)*` returns the set of allowed results, because NaN results are nondeterministic ([:224](specification/wasm-2.0/3-numerics.spectec#L224)). That's why the float clauses use `$setproduct_` and return `v128*`.
2. So TypeFamilyRemoval builds two shapes ([wasm2.0_03-typefamily-removal.il](spectec/test-lean-backend/il_dump/wasm2.0_03-typefamily-removal.il)):
   - integer: `mk_lane__0_lane_(Jnn, $iabs_(…, !($proj_lane__0(Jnn, lane_1))))*{lane_1 <- lane_1*}`. The `!` is in the iteration body.
   - float: `mk_lane__1_lane_(Fnn, iter_0)*{iter_0 <- $fabs_(…, !($proj_lane__1(Fnn, lane_1)))}*{lane_1 <- lane_1*}`. To wrap each element of the result list, it adds an inner iteration over `$fabs_(…)`, and the `!` ends up in that iteration's source.
3. Sideconditions never visits iteration sources.
   - Its `IterE` case collects only from the body and the `ListN` bound (`collect_iter collector1 iter`, [line 72](spectec/src/middlend/sideconditions.ml#L72)).
   - It then returns `false`, so the generic walker doesn't visit the body again without the iteration around it. But that also stops the walker from visiting the sources, and nothing else does ([walk.ml:293-299](spectec/src/il/walk.ml#L293-L299)).
   - The `IterPr` case ([line 84](spectec/src/middlend/sideconditions.ml#L84)) has the same gap, so the float `wf_lane_` premise gets no guard either.
   - In Lean, the unvisited source is the list argument of the inner `Map`/`Forall`, `(fabs_ var_0 (Option.get! (proj_lane__1 lane_1_38_elem)))` ([wasm2.0.lean:6105](spectec/src/test-lean-claude/wasm2.0.lean#L6105), [6108](spectec/src/test-lean-claude/wasm2.0.lean#L6108)).
4. Later passes don't change this.
   - DefToRel turns `$iabs_` into the relation `fun_iabs_`, so the integer call becomes the premise `Forall₂ (… fun_iabs_ …)`. The `!` is still in an iteration body, so the second Sideconditions run sees it too.
   - `$fabs_` is `hint(builtin)`, so it stays a function (`opaque fabs_`) and its `!` stays in the source.
   - Scalar float ops have the same inner iteration but no `!`: `$unop_` takes its operand apart in the clause pattern `mk_num__1_num_(Fnn, fN)`. So among the numeric ops, only the vector float ones are hit.

**How I checked**
- The dumps just before and after Sideconditions (`wasm2.0_11-sub.il` → `wasm2.0_12-sideconditions.il`, from your 2026-11-02 run with one Sideconditions pass) show:
  - the integer clause gains `(if ($proj_lane__0(lane_1#2) =/= ?()))*{lane_1#2 <- lane_1*}`;
  - the float clause comes out unchanged.
- A script over the model's generated relations finds 1,314 `get!`s:
  - All 1,128 outside iteration sources have a guard. I checked 17 of them by hand, where my matcher missed the guard's form.
  - None of the 186 inside iteration sources has one:
    - 184 are in `fun_vunop_`/`fun_vbinop_`, including the `_before_` relations that repeat their clauses;
    - 2 are in the `wf_instr` premises of `fun_instantiate`.
- `OLD_wasm2.0.lean` has exactly the same 186. The gap also predates the January 2026 rewrite of the pass: before `41dd386e9` it had `t_iterexp env (iter, _) = t_iter env iter`, which also drops the sources.
- So far only `!` is affected: none of the 138 `xs[i]!` in the relations sits in an iteration source.

**Likely fix (not tried).** DefToRel's collectors already handle this: they call `collect_iterexp c1 iterexp`, which visits the sources with the outer collector ([deftorel.ml:96](spectec/src/middlend/deftorel.ml#L96), [:104](spectec/src/middlend/deftorel.ml#L104)). The same change in Sideconditions would be:

```diff
-  | IterE (e1, ((iter, _) as iterexp))
+  | IterE (e1, iterexp)
 …
-    collect_iter collector1 iter @
+    collect_iterexp collector1 iterexp @
 …
-  | IterPr (prem', ((iter, _) as iterexp))
+  | IterPr (prem', iterexp)
 …
-    collect_iter collector1 iter @
+    collect_iterexp collector1 iterexp @
```

The source's condition is then produced outside the inner iteration, and the outer iteration wraps it. For the float lanes that should give `Forall (fun l => (proj_lane__1 l) ≠ none) lane_1_lst`.

I haven't built or run it. I can try it in a scratch copy of spectec and regenerate the model, without touching the repo. The constructors would gain premises, so a few proofs that destructure `fun_vunop_`/`fun_vbinop_` might need small updates.

This exchange is logged in `claude-logging/verbatim_dialogue_log/bundle30/`, with the scripts and their outputs in `evidence/`. Safety checks before and after writing the logs found no change outside them (`claude-logging/safety-checks/check-*-bundle30-*.txt`).
