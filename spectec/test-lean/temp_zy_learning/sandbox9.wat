;; ============================================================================
;; sandbox9.wat -- `return` exits the WHOLE function immediately, no matter
;; how many blocks/loops deep it's nested in. Contrast with `br $label`,
;; which only unwinds as far as the named label.
;;
;; Stack-state comments below show the operand stack just before the next
;; instruction runs (top of stack on the right). They're annotated for the
;; concrete call find_index(ptr=0, len=5, target=9) against the array
;; [5,3,9,7,2] in memory -- 9 lives at index 2, so the loop runs i=0,1,2
;; and fires `return` on the i=2 iteration.
;;
;; Also annotated: how the `return` line here instantiates each part of
;;   ∃ t1s ts t2s : List valtype, v_ft = mkFunctype (t1s ++ ts) t2s ∧
;;     v_C.RETURN = some (list.mk_list ts) ∧
;;     Instr_ok v_C instr.RETURN (mkFunctype (t1s ++ ts) t2s)
;; from `ai_principal_typing`'s RETURN case in TypingLemmas.lean.
;; ============================================================================

(module
  (memory (export "mem") 1)
  ;; array of 5 i32s: [5, 3, 9, 7, 2]
  (data (i32.const 0) "\05\00\00\00\03\00\00\00\09\00\00\00\07\00\00\00\02\00\00\00")

  ;; Linear-scan `ptr[0..len)` for `target`. The moment a match is found,
  ;; `return` jumps straight out of the `if`, the `loop`, and the `block`
  ;; in one step -- it doesn't just exit the innermost construct the way
  ;; `br $scan` or `br $not_found` would.
  (func $find_index (export "find_index")
      (param $ptr i32) (param $len i32) (param $target i32) (result i32)
    ;; This function's (result i32) is exactly what makes
    ;;   v_C.RETURN = some [i32]
    ;; throughout this whole body -- `v_C.RETURN` would instead be `none`
    ;; while typing a bare instruction sequence outside any function body
    ;; (where `return` isn't even legal). Every `return` below is only
    ;; well-typed because this field is `some [i32]`, not `none`.
    (local $i i32)
    (local.set $i (i32.const 0))
    ;; stack: [ ]   ($i := 0)
    (block $not_found
      (loop $scan
        ;; stack: [ ]        (i = 0, then 1, then 2 across iterations)
        (br_if $not_found (i32.ge_u (local.get $i) (local.get $len)))
        ;; stack: [ ]        (br_if consumed the i32 condition; i < len,
        ;;                    so the branch is NOT taken -- loop continues)
        (if (i32.eq
              (i32.load (i32.add (local.get $ptr) (i32.mul (local.get $i) (i32.const 4))))
              (local.get $target))
          ;; stack: [ ]        (if's own i32 condition already consumed;
          ;;                    this `if` has no (result ...), so BOTH
          ;;                    branches are required to be [] -> [])
          (then
            ;; entered only on the i=2 iteration: ptr[2] = 9 = target
            ;; stack: [ ]
            ;;
            ;; (return (local.get $i)) mapped onto the typing rule:
            ;;   `local.get $i`  pushes the index -> stack becomes [i32].
            ;;                   This [i32] IS `ts`: the value(s) actually
            ;;                   handed back to the caller (concretely: 2).
            ;;   `return`        fires with stack = [i32]:
            ;;     t1s = []      nothing sits below that i32 here, so the
            ;;                   rule's "ignorable polymorphic prefix" is
            ;;                   empty at this occurrence -- it exists in
            ;;                   general to cover call sites where `return`
            ;;                   fires with extra junk still stacked below
            ;;                   the returned values; not the case here.
            ;;     ts  = [i32]   matches v_C.RETURN = some [i32] exactly --
            ;;                   this equality IS the conjunct
            ;;                   `v_C.RETURN = some (list.mk_list ts)`.
            ;;     t2s = []      the (never-reached) rest of this `then`
            ;;                   branch would need type [] to match the
            ;;                   if's declared [] -> [], but the rule lets
            ;;                   t2s be ANY type list, since control never
            ;;                   actually falls through to find out.
            ;;   mkFunctype (t1s ++ ts) t2s = mkFunctype [i32] [] :
            ;;     "`return`, as an instruction, consumes one i32 and
            ;;     produces nothing further" -- this functype is `v_ft`,
            ;;     and it's also what gets fed into
            ;;     `Instr_ok v_C instr.RETURN (mkFunctype (t1s ++ ts) t2s)`,
            ;;     which additionally certifies `wf_context v_C` and
            ;;     `wf_instr instr.RETURN` hold (not visible in the WAT
            ;;     source -- those are facts about the surrounding
            ;;     validation context, satisfied here because this module
            ;;     and function are themselves well-formed).
            (return (local.get $i))))
        ;; stack: [ ]        (only reached when ptr[i] != target)
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $scan)))
    ;; stack: [ ]        (only reached if `br_if $not_found` fired: i >= len)
    ;; This -1 satisfies the SAME v_C.RETURN = some [i32] result type, but
    ;; through the ordinary end-of-body typing rule (the function's own
    ;; declared result type), not through `return`'s own typing rule above.
    (i32.const -1))
)
