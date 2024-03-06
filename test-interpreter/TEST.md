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
== IL Validation after pass animate...
== Translating to AL...
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
