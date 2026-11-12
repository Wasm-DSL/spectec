# Significant issue: `store_extension_reduce` and `t_preservation` are false in the Lean model

Written for: the user (decision needed) and any future Claude session (do not try
to prove the affected cases until this is resolved).

Found: bundle17, during the gap analysis for `store_extension_reduce`, before any
proof work was attempted. Per the standing instruction ("if any issues arise that
are significant, immediately stop and report back"), work stopped here.

## Claim

In the Lean model as generated (`spectec/src/test-lean-claude/wasm2.0.lean`), the
four store "val" reduction rules can fire **out of bounds**, and when they do they
**change the length of the memory's byte list**. That breaks `Meminst_ok`, so the
post-state is not `Store_ok`. Consequently, as stated in Lean:

- `TLC.store_extension_reduce` is **false** (its `Store_ok s'` conjunct fails), and
- `TLC.t_preservation` is **false** (`Config_ok c2` needs `State_ok`, which needs
  `Store_ok`).

The current Lean "proof" of `t_preservation` (bundle16) goes through only because
`store_extension_reduce` is `sorry`.

Rocq does **not** have this problem. The difference is in how the two backends render
the same spec function.

## Where the divergence comes from

Spec (`specification/wasm-2.0/5-runtime-aux.spectec:108`):

```
def $with_mem((s; f), x, i, j, b*) = s[.MEMS[f.MODULE.MEMS[x]].BYTES[i : j] = b*]; f
```

Spec store rules (`8-reduction.spectec:546-552`, and likewise `store-pack`, `vstore`,
`vstore_lane` at 554-576): the `-trap` rule has the bounds check; the `-val` rule has
**no** bounds premise, only `b* = $nbytes_(nt, c)`. In the spec's intended reading the
slice update is only meaningful in bounds.

| Backend | Rendering of `BYTES[i : j] = b*` | Out-of-bounds behaviour |
|---|---|---|
| Rocq (`backend-rocq/print.ml:467`, prelude `list_slice_update` at `print.ml:919` / `wasm.v:66-74`) | `list_slice_update BYTES i j b*` (recursive, stops at the end of the list) | **length-preserving** for all arguments; writes what fits, drops the rest |
| Lean (`backend-lean/backend.ml:795-834`, `SliceSeg` case) | `(BYTES.take i ++ b*) ++ BYTES.drop (i + j)` | **not** length-preserving: if `i ≥ |BYTES|` the result is `BYTES ++ b*`; if `i < |BYTES| < i + j` it is `take i BYTES ++ b*` |

Generated Lean (`wasm2.0.lean`, `def with_mem`):
```lean
MEMS := List.modify (s.MEMS) ((f.MODULE.MEMS)[proj_uN_0 v_memidx]!) (fun elem_1 => {
  elem_1 with
  BYTES := ((elem_1.BYTES.take nat) ++ var_0_lst) ++ (elem_1.BYTES.drop (nat + nat_0))
})
```

Generated Lean `Step.store_num_val` (no bounds premise; same for `store_pack_val`,
`vstore_val`, `vstore_lane_val`):
```lean
| store_num_val (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) (b_lst : List byte) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    b_lst = (nbytes_ nt c) →
    Step (config.mk_config z [CONST I32 i, CONST nt c, STORE nt none ao])
         (config.mk_config (with_mem z (uN.mk_uN 0) (i + ao.OFFSET) (size nt / 8) b_lst) [])
```

`Meminst_ok` (generated) requires `List.length b_lst = v_n * (64 * Ki)`, where `v_n` is
the min limit in the instance's **own** `TYPE` field (the conclusion is
`Meminst_ok s {TYPE := PAGE (limits v_n ..), BYTES := b_lst} ..`). A store does not
change `TYPE`, so after the step the byte count must still be exactly `v_n * 65536`.

## Counterexample (informal, every step checked against the generated definitions)

1. Store with one memory `m0 = {TYPE := PAGE (limits 0 none), BYTES := []}` (zero
   pages). It is valid: `Memtype_ok` needs `Limits_ok _ (2^16)`, i.e. `0 ≤ 2^16`;
   `Meminst_ok` needs `|[]| = 0 * 64Ki`.
2. Module instance with `MEMS := [0]`, context with `MEMS := [PAGE (limits 0 none)]`.
3. `[CONST I32 0, CONST I32 c, STORE I32 none ao]` with `ao.ALIGN = 0` is well typed
   at `[] -> []`: `Instr_ok.store_val` only needs `0 < |C.MEMS|` and
   `2^ALIGN ≤ size(I32)/8` (no constraint on the memory's size).
4. `Step.store_num_val` applies (its three premises hold for any `i`, `c`).
5. Resulting `BYTES = take 0 [] ++ nbytes_ I32 c ++ drop 4 [] = nbytes_ I32 c`, of
   length `4` by the project's axiom `HelperLemmas.nbytes_len` (ported from Rocq
   `axioms.v`).
6. `Meminst_ok` for the new memory would need `4 = 0 * 64Ki`. False, and no other
   choice of the store's memtype list helps (see above). So `¬ Store_ok s2`, hence
   `¬ Config_ok c2`, while `Config_ok c1` holds.

A one-page memory and an address within 4 bytes of the end gives the same failure
(partial overlap grows the list to `i + 4`), so this is not a zero-page corner case.

I have not built this as a formal Lean term (constructing `Config_ok c1` from scratch
is a few hundred lines and would have been "spinning"). I can do so if you want a
machine-checked refutation.

## Scope: what is and is not affected

- **Affected**: exactly the four `Step` rules `store_num_val`, `store_pack_val`,
  `vstore_val`, `vstore_lane_val`, and only in the out-of-bounds situation where the
  matching `_trap`/`_oob` rule also applies. Lemmas affected:
  `store_extension_reduce` (those 4 cases) and `t_preservation`, which consumes its
  `Store_ok s'` conjunct. `step_moduleinst`'s *statement* is still true (it only needs
  the `Extend_store` half, and `Extend_meminst` only asks the byte list to *grow*,
  which it does), but its current *proof* takes `.1` of the false
  `store_extension_reduce`, so it would need re-routing once that lemma is split or
  weakened.
- **Not affected**: loads. `Step_read.load_num_val` requires
  `nbytes_ nt c = take n (drop off BYTES)`; out of bounds the right side is shorter than
  `n` while `nbytes_len` pins the left side to length `n`, so the rule cannot fire.
  (Same for the other load rules via `ibytes_len`/`vbytes_len'`.)
- **Not affected**: `t_pure_preservation`, `t_read_preservation`,
  `t_preservation_type` (its store cases end in `[]`, typed by `ais_empty_typing`
  given `wf_store s'`), all `Step_pure__*` lemmas, all vector lemmas, and every other
  `Step` rule (`table_set_val` has a `<` premise; `List.modify`, `with_meminst`,
  `with_tableinst`, `with_elem`, `with_data` are all length-safe or handled by the
  existing `construct_*_grow` lemmas).

## Options (your call)

1. **Fix the Lean backend (recommended).** Render `SliceSeg` updates with a
   length-preserving function, e.g. emit a prelude `list_slice_update` mirroring the
   Rocq backend's (the project already has exactly that recursive definition in
   `HelperLemmas.lean:159`, re-derived from `wasm.v:66-74` in bundle14), or
   `take i l ++ (b*.take (|l| - i)) ++ drop (i + j) l` restricted appropriately.
   Then regenerate `wasm2.0.lean`. `store_extension_reduce` becomes provable by
   following Rocq, and the existing `store_none_mem_extension`/`construct_meminsts`
   (already stated with `list_slice_update`) plug in directly.
2. **Fix the spec.** Add the bounds premise to the four `-val` rules
   (`-- if $(i + ao.OFFSET + n) <= |$mem(z, 0).BYTES|`). Affects both backends; makes the
   `-val`/`-trap` pairs disjoint, which is arguably what the spec means anyway.
3. **Weaken the Lean theorem.** Add a hypothesis to `store_extension_reduce` /
   `t_preservation` excluding out-of-bounds store-val steps. Deviates from the Rocq
   signature and from what "preservation" means; not recommended.
4. **Leave the 4 cases `sorry`**, documented as false-in-the-Lean-model, and finish
   everything else. Compatible with 1 or 2 later.

If you pick 1 or 2, note `Step_is_wf`/`Step_read_is_wf` in the generated file would
change too (see `is_wf_theorems.md`).

## Related observation (not a blocker, recorded for completeness)

Upstream `wasm.v` has hand-edited `Step_read_is_wf` and `Step_is_wf` to take an extra
`Store_ok (fun_store z)` premise ("the store bounds are needed for table.size,
memory.size and the bulk rules"), and `Step_read_is_wf` is `Admitted` with the
author's note that 3 cases (4 goals: memory.fill-succ, memory.copy-le,
memory.init-succ) are **not derivable even under `Store_ok`**: they push
`CONST I32 (i + 1)` where `i = 2^32 - 1` is allowed, and `2^32` is not a `u32`. The
generated Lean versions (`wasm2.0.lean`) lack the `Store_ok` premise and are `sorry`.
`t_preservation` already depends on `Step_is_wf`; `t_pure_preservation` will depend
on `Step_pure_is_wf` (which is `Qed` upstream). Logged in
`claude-logging/for-claude/is_wf_theorems.md`.
