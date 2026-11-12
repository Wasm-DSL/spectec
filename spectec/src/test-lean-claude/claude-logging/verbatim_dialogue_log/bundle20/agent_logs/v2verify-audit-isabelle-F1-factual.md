# v2verify-audit-isabelle-F1-factual — adversarial FACTUAL verification of audit-isabelle F1

## Task

I am the adversarial verifier (factual lens) for finding F1 of auditor `audit-isabelle`, part of the
bundle20 preservation audit. F1 says the following. The generated `Moduleinst_ok` in Lean, Rocq and
Isabelle has a premise `List.length (GLOBAL-addrs ++ MEM-addrs ++ TABLE-addrs ++ FUNC-addrs) > 0`
that the spec rule (B-soundness.spectec:230) lacks. Since `$invoke` builds its frame with the empty
module instance, `Moduleinst_ok`/`Frame_ok`/`State_ok`/`Config_ok` can never hold for `$invoke`
configurations, so `t_preservation` and any progress theorem never apply to them. F1 rates this
major, new and undocumented. My job was to open every cited file and line, re-derive each claim,
and try to refute it. The task was read-only apart from this log file. Lean was not run and no
agents were spawned.

## Prior log

None existed at this path; this is a fresh run (v2 brief read in full first).

## What I read (files and line ranges)

- Brief: `scratchpad/briefs/audit_brief_v2.md` (all).
- `wasm2.0.lean`: 26-28 (`Map` = `List.map`); 15448-15490 (`fun_invoke`); 15671-15776 (`Moduleinst_ok`
  and the head of `Frame_ok`); 16315-16333 (`State_ok`, `Config_ok`).
- `TypePreservation.lean`: 2699-2704 (`t_preservation` signature); 536-540 (`reduce_inst_unchanged`).
- `specification/wasm-2.0/B-soundness.spectec`: 196-240 (rule `Moduleinst_ok`).
- `specification/wasm-2.0/9-module.spectec`: 194-200 (`$invoke`).
- `spectec/test-rocq/theories/wasm.v`: 17155-17183 (`Moduleinst_ok`; line 17174); 17000-17002
  (`fun_invoke_case_0`).
- Isabelle `scratchpad/isabelle/isabelle_reference_output_wasm2.thy`: 13615-13643 (`Moduleinst_ok`;
  premise at 13634); 13470-13472 (`fun_invoke_case_0`). `Progress.thy`: 1116-1117.
- SpecTec sources (root cause): `spectec/src/middlend/sideconditions.ml` 1-140; `spectec/src/il/ast.ml`
  16-20 (`iter` constructor order); `spectec/src/exe-spectec/main.ml` 305-335 (passes enabled per target).
- claude-logging: grep over all `*.md` for `Moduleinst_ok|fun_invoke|$invoke|non-empty|empty module|hoist|> 0`,
  then read `bundle18/user_requested_documents/insights_for_next_turn.md` 276-282 and
  `for-claude/digest_wasm_v.md` 403-410.

## Method

For each claim in F1 I opened the cited source myself, using `grep -n`/`sed -n` ranges. I tried to
refute three things: (1) that the empty module really fails the premise; (2) that no other
constructor or route reaches `Config_ok`; (3) that the issue was really undocumented. I also traced
which SpecTec pass emits the premise.

## Claim-by-claim results

| # | Claim | Result | Evidence |
|---|-------|--------|----------|
| 1 | Lean `Moduleinst_ok` has the `> 0` premise | TRUE | `wasm2.0.lean:15690` `(List.length ((Map (… externaddr.GLOBAL …) globaladdr_lst) ++ (… MEM … ++ (… TABLE … ++ … FUNC …)))) > 0 →`, followed at 15691 by `Forall (fun v_exportinst_elem => List.contains (…) (v_exportinst_elem.ADDR)) exportinst_lst →` |
| 2 | Rocq has it | TRUE | `wasm.v:17174` `… funcaddr_lst))))\|) >? 0%N)%BN ->` |
| 3 | Isabelle has it | TRUE | `isabelle_reference_output_wasm2.thy:13634` `((length ((map … externaddr_GLOBAL …) @ (… MEM … @ (… TABLE … @ … FUNC …)))) > 0) \<Longrightarrow>` (inside `mk_Moduleinst_ok`, 13616) |
| 4 | The spec rule has no `> 0`, only per-export membership | TRUE | `B-soundness.spectec:230` `-- (if exportinst.ADDR <- (GLOBAL globaladdr)* (MEM memaddr)* (TABLE tableaddr)* (FUNC funcaddr)*)*`. The `(…)*` ranges over `exportinst*`, so it is vacuous with no exports. |
| 5 | `fun_invoke` uses the empty module instance | TRUE | Lean 15454-15465 `f = ({ LOCALS := [] MODULE := { TYPES := [] FUNCS := [] GLOBALS := [] TABLES := [] MEMS := [] ELEMS := [] DATAS := [] EXPORTS := [] … } })`. Spec 9-module.spectec:198 `-- if f = { MODULE {} }`. Rocq wasm.v:17001 and Isabelle .thy:13471 are the same. The config is `config.mk_config (state.mk_state s f) (vals ++ [CALL_ADDR fa])`. |
| 6 | `Moduleinst_ok s {} C` cannot hold | TRUE | Single constructor; its conclusion is the record `{TYPES := functype_lst, FUNCS := funcaddr_lst, GLOBALS := globaladdr_lst, …}`. Inverting on the empty record forces those four lists to `[]`. `Map` = `List.map` (l.26-27), so the premise reduces to `0 > 0`, which is False. |
| 7 | Hence `Frame_ok`, `State_ok`, `Config_ok` fail for invoke configs | TRUE | Each has a single constructor. `mk_Frame_ok` needs `Moduleinst_ok s v_moduleinst C` for frame `{LOCALS := val_lst, MODULE := v_moduleinst}` (15745, 15766-15768). `mk_State_ok` needs `Frame_ok s f C` (16318). `mk_Config_ok` needs `State_ok (state.mk_state s f) C` (16327). |
| 8 | `t_preservation` (and progress) never apply to them | TRUE | `TypePreservation.lean:2700` `Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts`. Isabelle `Progress.thy:1117` `assumes "Config_ok (mk_config s es) ts"`. |
| 9 | Not a Lean porting deviation | TRUE | Rocq and Isabelle are identical (items 2 and 3). |
| 10 | Preservation is not false or vacuous | TRUE (reasoned) | The premise is satisfiable whenever the frame's module has at least one global, mem, table or func address, e.g. any real function's module (it contains its own funcaddr). |
| 11 | Undocumented in claude-logging | TRUE | Nothing outside bundle20 mentions the `> 0` premise or the invoke consequence. The bundle18 "premise order" note lists premises 1-16 then `…`. `digest_wasm_v.md:403-407` paraphrases the rule without the `> 0`. Only bundle20 audit logs (this audit) mention it. |
| 12 | Mechanism: "hoisted out of the per-export iteration by the shared IL/backend rendering of `<-`" (hedged "appears") | TRUE, located more precisely | It is the shared middlend IL pass `Sideconditions`, enabled for `Rocq \| Lean` (main.ml:318). See below. |

### Root cause (traced; F1 did not trace it)

`spectec/src/middlend/sideconditions.ml`:

```ocaml
  | MemE (_exp, exp) ->
    ([IfPr (CmpE (`GtOp, `NatT, LenE exp …, NumE (`Nat Z.zero) …) …) $ e.at], true)
```

So every `e1 <- e2` gets the side condition `|e2| > 0`. For the iterated premise, `t_prem` wraps
each collected side condition with the smart constructor:

```ocaml
let iterPr (pr, (iter, vars)) =
  … let vars' = List.filter (fun (id, _) -> Set.mem id.it frees.varid) vars in
  if iter <= List1 && vars' = [] then pr.it else IterPr (pr, (iter, vars'))
```

`|(GLOBAL globaladdr)* … (FUNC funcaddr)*| > 0` does not mention the iterated `exportinst`, so
`vars' = []`. The `iter` order is `Opt | List | List1 | ListN` (il/ast.ml:16-20), so `List <= List1`
holds and the condition is emitted unconditionally, outside the iteration. Dropping the iteration
is only sound for `List1`; for `List` (and `Opt`) it strengthens the rule when the iterated list is
empty. The Isabelle output has the same premise, so its pipeline evidently ran the same pass.

### Extra observation (strengthens F1's impact, not part of its claim)

`TypePreservation.lean:536-539`: `reduce_inst_unchanged … : Step (… (state.mk_state s f) ais) (… (state.mk_state s' f') ais') → f.MODULE = f'.MODULE`.
By induction along a `Step` sequence, the outer frame of every configuration reachable from an
`$invoke` configuration keeps the empty module. So `Config_ok` fails not only for the initial
`$invoke` configuration but for every configuration in an execution started by `$invoke`. Configs
from `fun_instantiate`, whose frame holds the new module instance, are fine whenever that module
has at least one address.

### Minor citation nits (not errors in substance)

- `fun_invoke` spans 15452-15484 (F1 says 15452-15485; 15485 is blank).
- The Isabelle premise is at line 13634 (F1 says "after l.13615"; correct but imprecise).

## Verdict

**CONFIRMED, severity major (unchanged).** Every factual claim holds against the sources, and my
attempts to refute it failed: the empty module fails `0 > 0`, every inductive in the chain has a
single constructor, and nothing was documented before this audit. Severity stays major, not
critical: preservation remains true and non-vacuous, and the issue is not a Lean port deviation.
It is still an undocumented restriction on what the soundness theorems cover, and a reviewer must
know about it, since no execution started by `$invoke` is ever `Config_ok`. The fix belongs in
SpecTec's `sideconditions.ml`: `iterPr` should not drop a `List`/`Opt` iteration (or the `MemE` side
condition should stay inside it). Alternatively, document the exclusion.

## Uncertainties

- I did not open the Isabelle backend's driver. I infer it runs the same `Sideconditions` pass
  because its generated premise is identical.
- The non-vacuity in item 10 and the reachability argument are reasoned, not machine-checked
  (Lean was not run, per the brief).

## Safety check — START (verbatim)

```
safety check [v2verify-audit-isabelle-F1-factual] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T111855.110329633Z-v2verify-audit-isabelle-F1-factual-1416131.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Safety check — END (verbatim)

```
safety check [v2verify-audit-isabelle-F1-factual] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112353.007210008Z-v2verify-audit-isabelle-F1-factual-1419011.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```
