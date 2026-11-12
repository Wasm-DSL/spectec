;; ============================================================================
;; sandbox10.wat -- demonstrates `table.set`, the operation whose semantic
;; soundness `construct_tableinsts` (ExtensionLemmas.lean) establishes:
;; writing a validated reference into one table slot keeps the WHOLE table
;; list well-typed against the SAME declared type list `ts` -- table.set
;; changes a table's CONTENTS, never its declared TYPE.
;;
;; construct_tableinsts's signature (ExtensionLemmas.lean):
;;   (s : store) (ts : List tabletype) (t : reftype) (tba : Nat)
;;   (lim : limits) (tbr : List ref) (i : Nat) (ref_lst : ref) :
;;     Forall₂ Tableinst_ok s.TABLES ts ->          -- store's tables all ok
;;     Ref_ok s ref_lst t ->                        -- new value is a valid t
;;     lookup_total s.TABLES tba = {TYPE:=(lim,t), REFS:=tbr} ->  -- which table
;;     Forall₂ Tableinst_ok (<tba's REFS[i] := ref_lst>) ts       -- still ok
;; ============================================================================

(module
  ;; `ts` / `lim` / `t`: this table's declared type is (min=3, no max) x
  ;; funcref -- `lim` = {min: 3, max: none}, `t` = funcref. At the store
  ;; level this becomes the one entry of `ts : List tabletype` that matters
  ;; here (a real store would have other modules' tables in `ts` too).
  (table $tbl 3 funcref)

  (func $double (param i32) (result i32)
    (i32.mul (local.get 0) (i32.const 2)))
  (func $triple (param i32) (result i32)
    (i32.mul (local.get 0) (i32.const 3)))
  ;; both must be declared to be legal `ref.func` targets
  (elem declare func $double $triple)

  (type $unop_t (func (param i32) (result i32)))

  ;; `tbr`: the table's contents BEFORE any table.set call. This active elem
  ;; segment populates slot 0 with $double at instantiation time; slots 1
  ;; and 2 start as (ref.null func).
  (elem (i32.const 0) func $double)

  ;; `tba`: this module declares only table 0, so `$tbl` always resolves to
  ;; store address 0 -- the one tableinst construct_tableinsts mutates below.
  (func (export "install_triple") (param $slot i32)
    ;; `i`: the index operand -- which slot is being written.
    (local.get $slot)
    ;; `ref_lst`: the NEW reference being written. `Ref_ok s ref_lst t`
    ;; is exactly table.set's own typing rule firing here -- `ref.func
    ;; $triple` must (and does) produce a valid `funcref`, matching this
    ;; table's declared element type `t = funcref`.
    (ref.func $triple)
    ;; the mutation itself: construct_tableinsts's conclusion says the
    ;; WHOLE table list is STILL well-typed against the SAME `ts` after
    ;; this -- only slot `i`'s contents changed, nothing about the type.
    table.set $tbl)

  ;; Exercise the table afterward to confirm the written reference is a
  ;; genuinely callable, correctly-typed function -- the real payoff of
  ;; `Ref_ok s ref_lst t` holding at table.set time.
  (func (export "call_slot") (param $slot i32) (param $x i32) (result i32)
    (local.get $x)
    (local.get $slot)
    (call_indirect $tbl (type $unop_t)))
)
