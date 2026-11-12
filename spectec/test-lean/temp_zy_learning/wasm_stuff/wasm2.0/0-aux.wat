;; ============================================================================
;; Companion to specification/wasm-2.0/0-aux.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: this source file has NO category-A constructs.
;; Every top-level construct is category B (spec-convenience machinery).
;; There is nothing for a WAT file to "make use of" here, so this file is a
;; minimal valid module plus documentation of why.
;;
;; Top-level constructs in 0-aux.spectec, and why each is category B:
;;
;;   syntax N = nat, syntax M = nat, syntax n = nat, syntax m = nat
;;     -- literally commented "hack" in the source. These are just short
;;        aliases so later files can write "N" instead of "nat" in a few
;;        places. Not a WASM concept at all; `nat` (mathematical natural
;;        number) is the meta-language's own number type used to *talk
;;        about* sizes, indices, counts, etc. You never write a bare "nat"
;;        in a .wat file -- concrete WASM integers are i32/i64 (see
;;        1-syntax.spectec, category A) or fixed-width encoded quantities.
;;
;;   def $Ki = 1024
;;     -- a numeric constant (1 KiB) used later to convert page counts to
;;        byte counts (memory pages are 64 * $Ki = 65536 bytes). You can't
;;        "invoke" this constant from a .wat file; it only appears inside
;;        other definitions' math.
;;
;;   def $min, def $sum
;;     -- generic integer helpers (minimum of two nats, sum of a sequence)
;;        used to state side conditions in later typing/runtime rules
;;        (e.g. limits checking). Ordinary math lemmas, not WASM syntax.
;;
;;   def $opt_, def $list_, def $concat_, def $inv_concat_,
;;   def $setproduct_, def $disjoint_
;;     -- generic, type-parametric sequence/option combinators (think:
;;        the spec's own tiny standard library for lists and optionals --
;;        concat a list of lists, take a cartesian-ish set product, check
;;        pairwise disjointness). These get reused throughout the *other*
;;        spectec files whenever they need to manipulate sequences
;;        generically (e.g. concatenating byte sequences during encoding,
;;        or checking export names are pairwise distinct in
;;        6-typing.spectec's Module_ok rule). None of them correspond to
;;        anything you write in WASM source text or observe in a running
;;        module -- they are the plumbing the *other* definitions are
;;        built out of.
;;
;; In short: this file is where the spec authors keep their generic
;; "prelude" (numbers, lists, options) so the WASM-specific files that
;; follow don't have to redefine it. See 1-syntax.wat in this directory
;; for where the actual WASM constructs begin.

(module)
