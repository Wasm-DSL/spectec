;; ============================================================================
;; Companion to specification/wasm-2.0/A-binary.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs -- but this file is the
;; closest thing to a genuine borderline case in the whole directory, worth
;; explaining rather than just asserting.
;;
;; Every top-level construct here is `grammar B... : sometype = ...`: a
;; byte-level encoding/decoding rule. E.g.
;;
;;   grammar Bnumtype : numtype =
;;     | 0x7F => I32
;;     | 0x7E => I64 | 0x7D => F32 | 0x7C => F64
;;
;; says the single byte 0x7F *is* the encoding of the type I32. These
;; grammar rules cover every value type, every instruction opcode
;; (Binstr/control, Binstr/numeric-*, Binstr/vector-*, ...), and every
;; module section (Btypesec, Bimportsec, Bcodesec, Bdatasec, ...), right
;; up to `grammar Bmodule : module` -- the whole binary format, byte for
;; byte.
;;
;; Why category B rather than A: this whole directory's exercise is WAT
;; (*text* format) files, and a .wat file never contains these bytes
;; directly -- `wat2wasm` (or wasmdebug, which shells out to it) is the
;; thing that applies these grammar rules, converting your text into the
;; bytes A-binary.spectec describes. You cannot "write" grammar
;; Bnumtype in a .wat file any more than you can write a CPU's opcode
;; table into a C source file -- it's what the compiler consults, once,
;; on your behalf.
;;
;; That said, the *bytes themselves* are arguably the single most literal
;; "manifestation in WASM" of anything in this whole directory -- they are
;; the actual contents of the .wasm file wasmdebug serves to Chrome. If
;; you want to see this file's output directly rather than take that on
;; faith, from a shell:
;;
;;   wat2wasm 1-syntax.wat -o /tmp/out.wasm --enable-all --debug-names
;;   wasm2wat /tmp/out.wasm | less        # Bmodule's grammar, inverted
;;   xxd /tmp/out.wasm | less             # the raw bytes Bmodule describes
;;
;; and note e.g. that every `i32.add` in the text shows up as the single
;; byte 0x6a in the hexdump -- that's grammar Binstr/numeric-bin-i32's
;; `0x6A => ADD` clause, applied.
;;
;; grammar Blist, BuN/BsN/BiN/BfN (LEB128 integer/float encoding), and the
;; def $utf8 clauses reused from 1-syntax.spectec round out the file --
;; all auxiliary encoding machinery in the same vein.

(module)
