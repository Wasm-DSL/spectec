/- ═══════════════════════════════════════════════════════════════════════
   FORALL/FORALL₂ MATHLIB-REDIRECT POSTMORTEM
   ═══════════════════════════════════════════════════════════════════════

   ┌─────────────────────────────────────────────────────────────────────┐
   │ SHORT REPORT (for humans) -- read this section, skip the rest       │
   │ unless you're picking this work back up.                            │
   └─────────────────────────────────────────────────────────────────────┘

   GOAL: the Lean backend (spectec/src/backend-lean/) self-generates its own
   `Forall`/`Forall₂`/`Forall₃` helper predicates instead of using Mathlib's
   real `List.Forall`/`List.Forall₂`. We wanted either (a) redirect codegen
   to emit Mathlib's versions when safe, giving downstream proofs access to
   Mathlib's much richer lemma library, or, failing that, (b) at least bake
   a length-equality condition into our own custom Forall₂/Forall₃, since
   Mathlib's real version enforces equal-length lists and ours (zip-based)
   doesn't -- to at least match Mathlib's *semantics* even without using it.

   WHAT HAPPENED, IN ORDER:

   1. Investigated *why* the custom, non-inductive Forall/Forall₂ exists at
      all (backend.ml has a comment citing "PR #192" and
      "leanprover/lean4#1964"). Traced both sources directly (via `gh`) and
      via extensive hands-on Lean experimentation (~20 small repros,
      compiled for real, not just reasoned about) worked out a precise
      characterization of the underlying Lean kernel restriction --
      "nested inductive datatypes cannot have indices." See the LONG
      section below, and spectec/test-lean/sandbox_11.lean, for the full,
      verified detail -- that file is unaffected by this postmortem and
      still stands as a correct, runnable reference.

   2. Implemented a full redirect: arity-1/2 Forall/Forall₂ calls would
      emit Mathlib's List.Forall/List.Forall₂ when the enclosing relation
      wasn't part of a genuine multi-member `mutual` group (detected via a
      new whole-script analysis, gather_mutual_group_member_ids), falling
      back to the existing custom defs otherwise. Also added the
      length-equality condition to whatever custom Forall₂/Forall₃ still
      got generated. Full design in the LONG section below.

   3. Verified via the project's golden-file test (`dune build
      @test-lean-backend/runtest`, which diffs generated *text* against a
      committed fixture) -- it passed. This felt like enough at the time.
      IT WASN'T.

   4. While answering an unrelated question (about why opening the golden
      fixture file directly in an editor couldn't find Mathlib), we went a
      step further than the golden-file test ever does: generated the
      Lean output for the *actual, complete* WASM 2.0 spec (not the
      `test.spectec` dune fixture) and ran it through `lake env lean`
      against real Mathlib. This is the first time in the whole
      investigation the real Lean kernel actually saw the real, full
      output. It found two genuine kernel errors:
        (kernel) arg #4 of 'wf_instr.instr_case_4' contains a non valid
          occurrence of the datatypes being declared
        (kernel) arg #5 of 'wf_admininstr.admininstr_case_71' contains a
          non valid occurrence of the datatypes being declared
      Root cause: both `wf_instr` and `wf_admininstr` are relations that
      reference *themselves* (e.g. "every instruction in this BLOCK is
      well-formed" is `wf_instr` calling `wf_instr`) -- and a single
      self-recursive `inductive` declaration is "still being elaborated
      with itself" the moment its own constructor mentions it, with **no
      `mutual` keyword required at all**. gather_mutual_group_member_ids
      only ever looked at explicit ≥2-member `mutual` groups, so it
      structurally could not see this at all -- a real gap, not a fine-
      tuning issue.

   5. Started drafting a fix (a second analysis,
      gather_self_referencing_relation_ids, unioned into the same gating
      set) -- see the LONG section for the drafted-but-never-applied code.

   6. User decided the redirect was too risky/complex relative to its
      benefit and asked to revert it entirely, keeping *only* the
      length-condition addition to the custom Forall₂/Forall₃ (no Mathlib
      involved at all -- seemingly much lower risk, since no new inductive
      types or imports are involved).

   7. Reverted the full redirect (`git checkout HEAD --
      spectec/src/backend-lean/ spectec/src/exe-spectec/main.ml`),
      re-applied just the length-condition change to make_forall_def,
      verified via the golden-file test (passed) -- and, having learned
      the lesson from step 4, *also* re-ran the real full-spec Mathlib
      check before declaring victory. Good thing: it found a THIRD real
      kernel error, in yet another self-referencing relation (`fun_utf8`,
      via its `fun_utf8_case_4` rule).

      Root cause, and the important new realization: baking the length
      condition in means wrapping the existing (always-safe) `∀ t ∈ …, P t`
      body in `∧` -- i.e. `length_eq ∧ (∀ t ∈ …, P t)`. But `∧` *is*
      `And`, Lean's own ordinary, pre-existing, single-constructor
      inductive type. So the moment a length condition was added, any
      relation that calls itself (or a mutual sibling) through
      Forall/Forall₂ was back to exactly the same "self/mutual-referencing
      type nested inside a pre-existing inductive container" shape that
      broke the Mathlib redirect -- just with `And` playing the role
      `List.Forall₂`/`Prod`/`Box` played earlier in the investigation. The
      problem was never really "which specific type is Mathlib's" -- it's
      that *any* pre-existing inductive container wrapping a self/mutual-
      referencing relation with real indices triggers this, and `∧` is
      such a container too. This was not anticipated going in.

   8. Realized, on reflection, that this whole exercise may not even be
      that valuable: `src/middlend/sideconditions.ml` (a shared,
      backend-agnostic middlend pass, unrelated to any of these changes)
      *already* emits a separate `List.length xs₁ = List.length xs₂`
      premise at every Forall₂/Forall₃ call site, unconditionally, for
      every backend -- confirmed 505 such premises already present in the
      untouched, reverted output. So the length information a downstream
      proof would want is already available at every call site today, just
      not folded into Forall₂'s own definition body. The length-condition
      idea was solving a real but fairly minor ergonomic gap, not a
      capability gap -- worth knowing before deciding it's worth the
      complexity of gating it correctly.

   9. Fully reverted everything in `spectec/src/backend-lean/` and
      `spectec/src/exe-spectec/main.ml` back to HEAD (confirmed
      byte-identical via `git diff --stat`, empty). **No functional change
      to the Lean backend survives this investigation.** The golden-file
      fixture (`test-lean-backend/test_spectec_output.lean`) was
      regenerated and re-promoted to match the fully-reverted generator, so
      it's back to (an up-to-date version of) its original content too.
      `sandbox_11.lean` (a separate, correct, still-useful worked reference
      on the underlying kernel restriction) was NOT touched and remains.

   BIGGEST LESSON: the project's golden-file test (`dune runtest`) only
   ever diffs generated *text* against a fixture -- it never invokes the
   Lean kernel at all. It is structurally incapable of catching this whole
   class of bug (anything about whether the generated Lean actually
   typechecks). Every real problem found in this investigation was found
   by manually running the *complete, real* spec's output through
   `lake env lean` against actual Mathlib -- not by the golden-file test,
   and not by small repros alone (the repros were essential for
   understanding *why*, but the real spec was needed to find *whether it
   actually happens in practice*, since it depends on the specific shapes
   of real relations like `wf_instr`/`wf_admininstr`/`fun_utf8` that no
   hand-built repro was designed to match). **Any future attempt at this
   MUST budget for that full real-spec check as a required step, not an
   afterthought** -- see the invocation recipe in the LONG section.

   ═══════════════════════════════════════════════════════════════════════
-/


/- ┌─────────────────────────────────────────────────────────────────────┐
   │ LONG TECHNICAL GUIDE (for a future Claude session)                   │
   └─────────────────────────────────────────────────────────────────────┘

   ───────────────────────────────────────────────────────────────────────
   1. THE UNDERLYING LEAN KERNEL RESTRICTION
   ───────────────────────────────────────────────────────────────────────

   Full, exhaustively-verified detail lives in spectec/test-lean/
   sandbox_11.lean -- read that file first, it's a working, compiled
   reference with one minimal example per case. Summary of what it
   establishes:

   Lean's kernel supports "nested inductive types" (e.g. `inductive Tree |
   node : List Tree → Tree`, `Tree` "nested" inside the pre-existing `List`)
   via an automatic compilation trick: it builds a specialized, Tree-aware
   copy of `List`'s own recursive structure. This trick can fail --
   "(kernel) invalid nested inductive datatype '<Container>', nested
   inductive datatypes parameters cannot contain local variables" -- under
   a specific combination of conditions. What actually matters (established
   via ~20 compiled repros, not just theorized):

   * NECESSARY PRECONDITION for either failure mode below: the nested type
     must be "still being elaborated" at the point of nesting. Two
     completely different ways this can be true:
       (a) It's part of an explicit ≥2-member `mutual ... end` block.
       (b) It's a SINGLE, ordinary `inductive` declaration that mentions
           itself directly in one of its own constructors -- no `mutual`
           keyword needed at all; self-reference is automatically "still
           in progress." THIS IS THE CASE THE IMPLEMENTATION MISSED (see
           wf_instr/wf_admininstr/fun_utf8 above).
     If the nested type is instead already fully, separately compiled
     before the referencing type exists, nesting it is always safe,
     regardless of anything else (confirmed: `repro G`-style test, moving a
     genuinely-indexed sibling with a captured-local-using nesting OUTSIDE
     any mutual/self-recursive relationship made it compile fine).

   * Given precondition (a) or (b) holds, TWO DIFFERENT safety rules apply
     depending on the shape of the "container":
       - Forall/List-style (walks a variable-length collection): safe iff
         the predicate passed in uses ONLY the collection's own walked
         element(s) -- any expression built purely from them (even
         transformed, e.g. `n + 1`) is fine; anything else ("captured" from
         an enclosing scope) breaks it. Never cares what the enclosing
         declaration's own conclusion looks like.
       - Prod/Box-style (a fixed, small, statically-known number of direct
         slots, no looping -- e.g. `Foo a b × Foo c d`, or a one-field
         wrapper `Box (Foo a b)`): safe iff EVERY nested occurrence
         reproduces the enclosing constructor's own conclusion EXACTLY,
         order included -- confirmed a single occurrence disagreeing with
         the conclusion is already fatal, with no second occurrence needed
         to "disagree with."
     (These are genuinely different rules, not the same rule described
     two ways -- confirmed both directions experimentally in sandbox_11.lean.)

   * A DIRECT (unwrapped) recursive/mutual reference -- e.g. two plain
     hypotheses `B 0 c → B 1 c → A`, no container at all -- is ALWAYS safe,
     no matter how many times, how varied the indices, or whether it
     captures an outer local. This is ordinary recursion (the same shape
     `Nat.succ`/transitivity-style rules already rely on) and never touches
     the "nested inductive compilation" machinery at all, because there's
     no separately-elaborated container type (`List`/`Prod`/`And`/...)
     being applied with the recursive type substituted into one of its own
     argument slots. The restriction is *specifically* about being wrapped
     inside such a container -- see next point.

   * THE KEY GENERALIZATION THAT BIT US TWICE: "container" means *any*
     pre-existing, already-elaborated inductive type being applied with the
     self/mutual-referencing type substituted into one of its own argument
     slots -- not specifically Mathlib's types. `List`, `Prod`, a trivial
     one-field `Box`, and **`And` (i.e. Lean's own `∧`)** all equally
     qualify. This is *why* the length-condition idea (wrapping the
     existing safe `∀ t ∈ …, P t` body in `length_eq ∧ (…)`) reintroduced
     the exact same failure for self-referencing relations: `∧` is just as
     much a "pre-existing inductive container" as `List.Forall₂` was.
     (This specific case -- `∧`/`And` as the offending container -- is NOT
     covered in sandbox_11.lean, since it was discovered afterward, in the
     length-condition-only attempt. If picking this back up, consider
     adding an `Row_And`-style cell there for completeness, mirroring the
     existing `Box`-based cells but substituting `And` conjunction for
     `Box` wrapping.)

   * A plain arrow/Pi-type (`X → T`) is exempt from all of this regardless
     of anything else -- `→` is a primitive kernel construct, not an
     application of any separately-elaborated inductive type, so ordinary
     strict positivity (T not in the domain, may be in the codomain) is all
     that's ever checked. This is also why a `def`'s ordinary BODY (as
     opposed to a fresh `inductive`/`structure` declaration) is always safe
     regardless of mutual-block status: using List.Forall₂ inside a plain
     `def`'s value, even one referencing a mutual-block inductive sibling
     with a captured local, is just ordinary term elaboration -- confirmed
     directly by compiling exactly that shape.

   ───────────────────────────────────────────────────────────────────────
   2. THE REAL-SPEC VERIFICATION RECIPE (do this, every time, before
      trusting any change here)
   ───────────────────────────────────────────────────────────────────────

   The golden-file test (`dune build @test-lean-backend/runtest`, from
   spectec/) only diffs generated text against a fixture -- it never runs
   the Lean kernel and will NOT catch anything in section 1. Use this
   instead, on the actual complete spec, not just the `test.spectec` dune
   fixture:

   ```sh
   cd spectec
   eval $(opam env)                              # this project's local
                                                   # opam switch; if `dune
                                                   # build` fails with
                                                   # zarith/ppxlib "not a
                                                   # compiled interface"
                                                   # errors, the shell env
                                                   # just isn't synced to
                                                   # it yet -- this fixes it
   dune build src/exe-spectec/main.exe
   ./_build/default/src/exe-spectec/main.exe \
     ../specification/wasm-2.0/*.spectec --lean > /tmp/wasm2.0_check.lean
   cd test-lean                                   # the ONE directory here
                                                   # that's an actual Lake
                                                   # project with Mathlib
                                                   # pinned (v4.32.0) --
                                                   # test-lean-backend/ is
                                                   # NOT a Lake project at
                                                   # all, just dune text
                                                   # fixtures; its Mathlib
                                                   # is not resolvable and
                                                   # never will be without
                                                   # setting up a second,
                                                   # separate Lake project
                                                   # there (possible, but
                                                   # a real, deliberate
                                                   # decision -- it would
                                                   # need its own Mathlib
                                                   # fetch+build unless you
                                                   # symlink test-lean/
                                                   # .lake into it to reuse
                                                   # the already-built copy)
   lake env lean /tmp/wasm2.0_check.lean 2>&1 | grep -i error
   ```
   Mathlib is already fully built in test-lean/.lake/packages/mathlib, so
   this is fast (no fresh download/build) -- confirmed throughout this
   session. Grep the output for "error"; "(kernel) ... non valid
   occurrence" or "(kernel) invalid nested inductive datatype ..." are the
   specific signatures of the restriction in section 1.

   ───────────────────────────────────────────────────────────────────────
   3. THE FULL REDIRECT DESIGN, AS IMPLEMENTED (then reverted)
   ───────────────────────────────────────────────────────────────────────

   This is reconstructed from the working session, not copied from any
   file still on disk -- everything below was reverted via `git checkout
   HEAD -- spectec/src/backend-lean/ spectec/src/exe-spectec/main.ml` and
   no longer exists in the tree. Treat this as a detailed starting design,
   not a patch to reapply verbatim -- it has the known gap from step 4/5 of
   the short report (self-referencing single relations weren't gated) and
   was never fixed or re-verified.

   ── 3a. lean_ast.ml: a `_program` type, not an `Import` command variant ──

   Considered adding `Import of string` to the existing `command` variant,
   but checked against the real Lean 4 source
   (Lean/Parser/Module.lean's `parseHeader`, Lean/Elab/Frontend.lean's
   `processCommands`) and confirmed Lean has NO single AST node combining a
   module header with its commands at all -- it's two structurally separate
   phases, header parsed-and-processed once, then commands parsed and
   elaborated one at a time in a loop. `import` is not a `command` in
   Lean's own grammar. So:

   ```ocaml
   (* in lean_ast.ml, after `command`'s definition *)
   type _program = {
     imports : string list;  (* e.g. ["Mathlib.Data.List.Forall2"] *)
     commands : command list;
   }
   [@@deriving show]
   ```

   ── 3b. render.ml: render__program replaces render_script_to_string ──

   ```ocaml
   (* NOTE: like render__script, _program isn't a Lean AST construct. *)
   let render__program (prog : _program) : string =
     let doc = match prog.imports with
       | [] -> render__script prog.commands
       | _  ->
         let imports_str = separate hardline (List.map (fun m -> string "import " ^^ string m) prog.imports) in
         imports_str ^^ hardline ^^ hardline ^^ render__script prog.commands
     in
     let buf = Buffer.create 4096 in
     PPrint.ToBuffer.pretty 1.0 80 buf doc;
     Buffer.contents buf
     |> strip_trailing_whitespace_per_line
     |> normalize_trailing_newline
   ```
   `main.ml`'s one call site: `Backend_lean.Render.render_script_to_string
   lean_ast` → `Backend_lean.Render.render__program lean_ast`.

   ── 3c. whole_file_analyses.ml: the two gating analyses ──

   ```ocaml
   (* Every VariantT/StructT/RelD id that is a member of a genuine
      multi-member (>=2, after stripping HintD) mutual-recursion group --
      mirrors create_mutual_construct's own is_inductive/
      all_inductive_or_structure classification. Reuses shape_of_def, which
      already excludes wf-lemma RelD's (rendered as `theorem ... := sorry`,
      never inductive) via its own hint-based guard.
      KNOWN GAP: this alone is NOT sufficient -- see
      gather_self_referencing_relation_ids below, which was needed to catch
      wf_instr/wf_admininstr/fun_utf8 and was never actually wired in
      before the whole thing was reverted. *)
   let gather_mutual_group_member_ids (il : script) (hints : Hint_index.t) : string list =
     List.concat_map (fun (def : Il.Ast.def) -> match def.it with
       | RecD defs ->
         let defs = List.filter (fun (d : Il.Ast.def) -> match d.it with HintD _ -> false | _ -> true) defs in
         let shapes = List.filter_map (shape_of_def hints) defs in
         if List.length shapes = List.length defs && List.length defs > 1 then
           List.filter_map (fun (id, _, shape) -> match shape with
             | ShapeVariant _ | ShapeStruct _ | ShapeRelation -> Some id
             | ShapeAlias _ -> None
           ) shapes
         else []
       | _ -> []
     ) il

   (* DRAFTED BUT NEVER APPLIED/TESTED -- this is the fix for the gap
      above, written after finding wf_instr/wf_admininstr broken, but the
      user asked to stop and revert before it was wired into backend.ml or
      verified. Catches: a single RelD (no `mutual` keyword, no RecD
      grouping) whose own rules reference itself, directly or via an
      IterPr (Forall/Forall₂-shaped) wrapper -- exactly wf_instr's
      instr_case_4 calling `List.Forall (fun x => wf_instr x) instr_lst`
      inside wf_instr's own constructor. *)
   let rec prem_references_id (target_id : string) (p : Il.Ast.prem) : bool =
     match p.it with
     | RulePr (id, _, _, _) -> id.it = target_id
     | IfPr _ | LetPr _ | ElsePr -> false
     | IterPr (inner, _) -> prem_references_id target_id inner
     | NegPr inner -> prem_references_id target_id inner

   let gather_self_referencing_relation_ids (il : script) : string list =
     List.filter_map (fun (def : Il.Ast.def) -> match def.it with
       | RelD (id, _, _, _, rules) ->
         let self_referencing = List.exists (fun (rule : Il.Ast.rule) -> match rule.it with
           | RuleD (_, _, _, _, prems) -> List.exists (prem_references_id id.it) prems
         ) rules in
         if self_referencing then Some id.it else None
       | _ -> None
     ) (flatten_defs il)
   ```
   Both would feed a `mutual_group_member_ids : string list` field on
   `whole_script_analysis` (populated as the UNION of both functions'
   results, not just the first one -- this union was never actually
   implemented), consulted via `!analysis` the same way existing fields
   like `defs_needing_catchall` already are.

   ── 3d. backend.ml: threading rel_id, and the arity dispatch ──

   Deliberately NOT a global mutable ref for control flow (explicitly
   requested during the session, in favor of consistency with how the rest
   of this file already looks facts up in `!analysis` at the point of use).
   `create_prem`/`create_iter_prem`/`append_prems_to_prop` each gained a
   leading `rel_id : Il.Ast.id option` parameter -- `Some id` when actually
   building an inductive relation's own constructor signature
   (create_relations_inductive_case already had the real id in scope as
   `rel_id`, so threading it into `append_prems_to_prop` needed zero
   further plumbing there), `None` everywhere else (wf-lemma theorem
   statements, def-clause bodies -- confirmed empirically safe
   unconditionally, since neither is a fresh inductive/structure
   declaration; see section 1's last paragraph).

   ```ocaml
   (* create_iter_prem, inside the existing arity-dispatch match: *)
   let in_mutual = match rel_id with
     | None -> false   (* not inside an inductive/structure declaration at
                           all -- unconditionally safe, confirmed
                           empirically, not assumed *)
     | Some id -> List.mem id.it (!analysis).mutual_group_member_ids
   in
   match entries with
   | [] -> body
   | [(name, coll_term, typ)] ->
       let lambda = Lambda { params = ...; body } in
       if not in_mutual then begin
         used_mathlib_forall := true;
         FunApp (Ident "List.Forall", [Term lambda; Term coll_term])
       end else begin
         used_prem_arities := 1 :: !used_prem_arities;
         FunApp (Ident (forall_with_arity 1), [Term lambda; Term coll_term])
       end
   | [(name1, coll1, typ1); (name2, coll2, typ2)] when not in_mutual ->
       used_mathlib_forall2 := true;
       let lambda = Lambda { params = [...]; body } in
       FunApp (Ident "List.Forall₂", [Term lambda; Term coll1; Term coll2])
   | _ ->
       (* unchanged existing generic arity>=2 fallback -- also where
          every in_mutual=true arity-2 site ends up, since the guarded arm
          above didn't match *)
       ...
   ```
   `create_script` resets `used_mathlib_forall`/`used_mathlib_forall2 :=
   false` alongside the existing `used_prem_arities := []` etc., and
   computes `imports` from them afterward (only emitting
   `Mathlib.Data.List.Forall2` -- which transitively covers
   `Mathlib.Data.List.Defs`, hence `List.Forall` too -- if
   `used_mathlib_forall2` fired; the narrower `Mathlib.Data.List.Defs`
   alone otherwise; nothing if neither fired), building a `_program`
   instead of a bare `command list`.

   ── 3e. The length-condition addition to make_forall_def ──

   This part is NOT gated by any of the above in what was actually tried
   -- and per the short report, that's exactly what made it break too. If
   re-attempting, this needs the SAME in_mutual/self-reference gating as
   the redirect, applied per-call-site rather than baked unconditionally
   into the shared def:

   ```ocaml
   (* inside make_forall_def, n >= 2 branch -- DO NOT ship this
      unconditionally; it broke fun_utf8's self-reference the same way the
      redirect broke wf_instr's, because `∧` is `And`, itself an ordinary
      pre-existing inductive type, and this bakes it into the SHARED
      Forall₂/Forall₃ def used by every call site, safe or not. *)
   let bounded_forall = BoundedForall { var = tuple_var; collection = zipped; body = FunApp (Ident "P", proj_args) } in
   let length_of i = FunApp (DotProj (Ident "List", Ident "length"), [Term (Ident (coll_var i))]) in
   let length_eqs = List.map (fun i -> BinaryInfixFunApp (Term (length_of 0), Ident "=", Term (length_of i))) (List.tl indices) in
   List.fold_right (fun eq acc -> BinaryInfixFunApp (Term eq, Ident "∧", Term acc)) length_eqs bounded_forall
   ```
   Since `Forall₂`/`Forall₃` are ONE SHARED definition used by every call
   site across the whole file, gating this per-call-site the way the
   redirect does doesn't work the same way -- there's no way to have "two
   versions" of the shared def selected per site without either (a)
   generating differently-named variants (e.g. a safe `Forall₂` and an
   unsafe-context `Forall₂_plain`, chosen per call site the same way the
   Mathlib redirect chooses `List.Forall₂` vs the fallback), or (b) not
   baking it into the definition at all and instead relying on the
   already-existing, always-safe, separately-emitted middlend length
   premise (see short report point 8) -- which is probably the better
   answer, and worth strongly considering before attempting (a).

   ───────────────────────────────────────────────────────────────────────
   4. IDEAS FOR NEXT TIME, IN ROUGH ORDER OF HOW PROMISING THEY SEEM
   ───────────────────────────────────────────────────────────────────────

   1. Don't bake length into Forall₂/Forall₃'s definition at all. The
      information is already available at every call site via
      sideconditions.ml's separately-emitted premise (confirmed: 505
      instances in the current, untouched output). If a downstream proof
      wants "Forall₂ unfolds to give you both facts together," that's a
      genuinely different, more invasive ask than what was attempted here.

   2. If still pursuing the Mathlib redirect: implement the union of
      gather_mutual_group_member_ids AND gather_self_referencing_relation_ids
      (section 3c) properly, wire it into backend.ml, and -- critically --
      run the FULL real-spec verification recipe (section 2) before
      declaring success, not just the golden-file text diff. Also
      specifically hunt for any OTHER self-referencing relations beyond
      wf_instr/wf_admininstr/fun_utf8 by grepping the real generated output
      for `Forall(₂|₃)? \(fun [^=]*=> <same-relation-name>` patterns, or by
      running gather_self_referencing_relation_ids standalone and checking
      its output against every actual mutual/self-nested relation in the
      real wasm 2.0 (and ideally 3.0) spec, not just the two/three found by
      accident this round.

   3. If still pursuing the length-condition idea despite (1): it would
      need the exact same per-relation-site gating as the redirect, likely
      via generating a second, unsafe-context variant of Forall₂/Forall₃
      (plain, un-lengthened body) selected the same way the Mathlib
      redirect chooses between List.Forall₂ and the custom fallback -- more
      total code paths than either the pure-redirect or pure-revert
      options, for a smaller ergonomic win. Probably not worth it given
      (1).

   4. A more exotic option, not seriously explored: express `A ∧ B` via a
      Church-encoded (∀-only, no inductive `And`) conjunction instead of
      Lean's native `∧`, which actually would sidestep the whole class of
      restriction (plain Pi-types are always safe, confirmed throughout
      section 1) -- but makes the generated defs meaningfully less
      ergonomic for anyone writing proofs against them (no `.1`/`.2`
      projections, `And.intro`, etc.). Mentioned for completeness; probably
      not worth the ergonomics cost relative to option (1).
-/
