;; ============================================================================
;; Companion to specification/wasm-2.0/B-soundness.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs. This is the cleanest
;; case in the directory -- 100% proof machinery, zero WASM-observable
;; content, by design.
;;
;; This file exists to state (this repo does not include the proof itself,
;; just the statement) type *soundness*: roughly, "a well-typed module
;; (Module_ok, 6-typing.spectec) never gets stuck in a bad way when run
;; (Step, 8-reduction.spectec) -- it either keeps stepping, finishes with
;; values matching its declared type, or explicitly traps". To even state
;; that, it needs runtime counterparts of typing judgments that quietly
;; assumed a "nice" static world:
;;
;;   Context_ok, Ref_ok, Val_ok, Result_ok
;;     -- lift 6-typing.spectec's static context/value-type judgments to
;;        talk about *runtime* refs and values (which carry resolved
;;        addresses, not source indices -- see 4-runtime.spectec).
;;
;;   Instr_ok2 / Instrs_ok2 / Expr_ok2
;;     -- like 6-typing.spectec's Instr_ok, but typing *administrative*
;;        instructions too (LABEL_, FRAME_, CALL_ADDR, TRAP -- the ones
;;        with no WAT syntax at all, from 4-runtime.spectec's admininstr).
;;        You need this because after even one execution step, your
;;        configuration contains administrative instructions that plain
;;        Instr_ok was never designed to classify.
;;
;;   Globalinst_ok, Meminst_ok, Tableinst_ok, Funcinst_ok, Datainst_ok,
;;   Eleminst_ok, Exportinst_ok, Moduleinst_ok, Store_ok
;;     -- runtime well-formedness for every instance record in
;;        4-runtime.spectec: e.g. Meminst_ok checks a meminst's byte
;;        length actually matches its declared page count.
;;
;;   Extend_globalinst, ..., Extend_store
;;     -- the store only ever *grows* as execution proceeds (new instances
;;        get appended, existing ones only change in specific allowed ways
;;        -- e.g. a global's value may change only if it's mutable). This
;;        "extension" ordering is the technical device the soundness proof
;;        uses to reason about a store that keeps changing underneath it.
;;
;;   Frame_ok, State_ok, Config_ok
;;     -- well-formedness of a whole running configuration, tying store +
;;        frame + in-flight administrative instructions together.
;;
;; None of this is meant to be authored, executed, or observed -- it's the
;; scaffolding that lets someone *prove*, once and for all, that every
;; file in this directory which validates (6-typing.wat) behaves
;; predictably when run (8-reduction.wat). A WAT author benefits from this
;; file having been written without ever needing to read it.

(module)
