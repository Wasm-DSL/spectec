# Artifact For "Bringing the WebAssembly Standard up to Speed with SpecTec"
This artifact is for PLDI 2024 paper: "Bringing the WebAssembly Standard up to Speed with SpecTec" and includes SpecTec, a domain-specific language (DSL) and toolchain that facilitates both developing the Wasm specification and the generation of artifacts necessary to standardize new features.


## Getting Started
We support two ways to use SpecTec:

* Using a Docker container

* Building from source

### Using a docker container
We provide a Docker container with SpecTec and its dependencies. You can install the docker by following the instruction in https://docs.docker.com/get-started/ and download our docker image with the following command:
> WARNING: The docker image is 6GB large. Thus, be patient when you download it, and please assign more than 6GB of memory for the docker engine.
```
$ docker pull pldi24spectec/artifact
$ docker run --name artifact -it --rm pldi24spectec/artifact
```

### Building from source

* You will need `ocaml` installed with `dune`, `menhir`, and `mdx`.

* Have `python3` version 3.7 or higher with `pip3` installed.

* Install `sphinx` version 7.1.2 and `six` version 1.16.0 via `pip3` (default versions).
  ```
  $ pip3 install sphinx six
  ```

* Install `texlive-full` via your package manager.
  ```
  $ apt-get install texlive-full
  ```

* Then, you should be able to build the binary using the `make` command.
  ```
  $ (cd spectec; make)
  ```
  
* Check if the build was successful.
  ```
  $ ./spectec/watsup --help
  Usage: watsup [option] [file ...] [-p file ...] [-o file ...]
  -v                Show version
  -p                Patch files
  -o                Output files
  -l                Log execution steps
  -w                Warn about unused or multiply used splices
  --check           Check only
  --latex           Generate Latex (default)
  --splice-latex    Splice Sphinx
  --splice-sphinx   Splice Sphinx
  --prose           Generate prose
  --interpreter     Generate interpreter
  --print-il        Print il (after elaboration)
  --print-final-il  Print final il
  --print-all-il    Print il after each step
  --print-al        Print al
  -help             Display this list of options
  --help            Display this list of options
  --sub  Synthesize explicit subtype coercions
  --totalize  Run function totalization
  --the-elimination  Eliminate the ! operator in relations
  --wildcards  Eliminate wildcards and equivalent expressions
  --sideconditions  Infer side conditions
  --animate  Animate equality conditions
  --all-passes  Run all passes
  --root  Set the root of watsup. Defaults to current directory
  --test-interpreter  The name of .wast test file for interpreter
  ```

## Step-by-Step Instructions

We provide instructions to reproduce the results in the Evaluation section of the paper.

### 1) Correctness

In this section, we demonstrate the SpecTec's ability to correctly generate formal and prose specification, and execute the official test suite using the meta-level interpreter.

#### Formal and Prose Specification
SpecTec can generate the specification document in both formal and prose notation from the spec files given by the user.

We have made a script for generating the pdf document from the input files located in the `spectec/spec` directory.

The specification document is generated using the command below.
```
$ (cd spectec/test-prose; make pdf)
```
The generated pdf document is located at `spectec/test-prose/WebAssembly.pdf`.

You can check that this document with formal and prose notations is very close to the respective parts of the [hand-written specification](https://webassembly.github.io/spec/core/).


#### Interpreter
SpecTec can can generate the meta-level interpreter for Wasm, which can run any wasm file.

We have made a script for executing the [official test-suite](https://github.com/WebAssembly/spec/tree/main/test/core), located in the `spectec/test-interpreter/spec-test` directory.

By running the `interpreter.sh`, you can see total 23,751 tests are passed. (This make take a few minutes)
```
$ (cd spectec; ./interpreter.sh)
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== nop.wast =====
- 83/83 (100.00%)

Total [23751/23751] (100.00%; Normalized 100.00%)
```

### 2) Bug prevention

In this section, we demonstrate the SpecTec's ability to prevent the real-world spec bugs.

In the paper, we have identified the bugs that could have been prevented using SpecTec, and classified the bugs into four categories:
1. Type Erros
2. Prose Errors
3. Semantics Errors
4. Editorial Fixes

Among the four categories, prose errors and editorial fixes were confirmed by looking at the generated document, and checking the absence of such errors.

For rest of the two categories, we show that SpecTec can detect these errors during its type-checking phase and interpreter phase.

The patch files that injects each bugs into the spec files are located in the directory `spectec/spec-bugs`.

We made a script that injects each bugs into spec files by applying those patch files, and executes SpecTec with the injected spec:
```
$ (cd spectec; ./bug-prevention.sh)
```

Below are the expected results.

For type errors, you can see that SpecTec raises type error, with the error message indicating the location of the bug and the explanation for the bug.

```
===== spec-bugs/type-1/4-runtime.watsup =====
Injecting error to spec-bugs/type-1/4-runtime.watsup ...
Running watsup on spec-bugs/type-1 ...
spec-bugs/type-1/4-runtime.watsup:164.61-164.63: type error: iteration does not match expected type `eleminst`


===== spec-bugs/type-2/7-module.watsup =====
Injecting error to spec-bugs/type-2/7-module.watsup ...
Running watsup on spec-bugs/type-2 ...
spec-bugs/type-2/7-module.watsup:142.39-142.51: type error: omitted sequence tail does not match expected type `elemidx`


===== spec-bugs/type-3/3-typing.watsup =====
Injecting error to spec-bugs/type-3/3-typing.watsup ...
Running watsup on spec-bugs/type-3 ...
spec-bugs/type-3/3-typing.watsup:296.22-296.24: type error: variable's type `reftype` does not match expected type `tabletype`
```

For semantics errors, you can see that SpecTec raises error during the execution of official test suite.

```
===== spec-bugs/semantics-1/6-reduction.watsup =====
Injecting error to spec-bugs/semantics-1/6-reduction.watsup ...
Running watsup on spec-bugs/semantics-1 ...
./watsup: uncaught exception Failure("Could not get kind_of_context[CONST_admininstr(I32_numtype, n) TABLE.GROW_admininstr(x)]")
Raised at Stdlib.failwith in file "stdlib.ml", line 29, characters 17-33
Called from Backend_interpreter__Translate.reduction_group2algo.(fun) in file "src/backend-interpreter/translate.ml", line 737, characters 21-40
Called from Stdlib__List.fold_right2 in file "list.ml", line 167, characters 32-58
Called from Backend_interpreter__Translate.reduction_group2algo in file "src/backend-interpreter/translate.ml", line 735, characters 6-298
Called from Stdlib__List.map in file "list.ml", line 86, characters 15-19
Called from Stdlib__List.map in file "list.ml", line 88, characters 14-21
Called from Backend_interpreter__Translate.translate in file "src/backend-interpreter/translate.ml", line 891, characters 37-55
Called from Dune__exe__Main in file "src/exe-watsup/main.ml", line 205, characters 8-30


===== spec-bugs/semantics-2/6-reduction.watsup =====
Injecting error to spec-bugs/semantics-2/6-reduction.watsup ...
Running watsup on spec-bugs/semantics-2 ...
===========================

test-interpreter/spec-test/test-semantics.wast

[Instantiating module...]
[Uncaught exception] Module Instantiation failed due to Failed Array.get during ReplaceE, test-semantics.wast took 1.878000 ms.
Took 1.878000 ms.


===== spec-bugs/semantics-3/6-reduction.watsup =====
Injecting error to spec-bugs/semantics-3/6-reduction.watsup ...
Running watsup on spec-bugs/semantics-3 ...
===========================

test-interpreter/spec-test/test-semantics.wast

[Instantiating module...]
[Invoking data []...]
 Fail!
 Expected: [(I32.CONST 0x1)]
 Actual  : Invalid pop: Popall val^n

test-semantics.wast took 1.835000 ms.
Took 1.835000 ms.
```

### 3) Forward compatibility

In this section, we demonstrate the SpecTec's ability to handle Wasm's five proposals:
1. Typed Function References
2. Garbage Collection
3. Tail Calls
4. Multiple Memories
5. Extended Constant Expression

#### Formal and Prose Specification
We have extended the spec files with the proposals, and the extended spec files are available at the `spectec-forward` directory:

```
$ (cd spectec-forward; make)
```

Same as before, the specification document is generated using the command below.
```
$ (cd spectec-forward/test-prose; make pdf)
```

The generated pdf document is located at `spectec-forward/test-prose/WebAssembly.pdf`.

#### Interpreter
As we explained in the paper, we borrowed reference interpreter for parsing the Wasm test suite.
We need different parser to parse the test suite corresponding to each proposal,
so we need to change the reference interpreter for each proposal accordingly.
Each implementation of SpecTec with different version of reference interpreter is located in the `spectec-gc`, `spectec-mm`, and `spectec-const` directroy.
Same as before, we have made a script for executing the official test-suite corresponding to each proposals.

##### a. function references, tail calls proposal, and garbage collection
The reference interpreter for gc proposal can also parse the test for function references and tail calls proposals, so we can run tests for all three of these proposals at once under `spectec-gc` directory.

For function references, total 78 tests are passed. (This make take a few minutes)
```
$ (cd spectec-gc; ./interpreter.sh function-references)
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== return_call_ref.wast =====
- 35/35 (100.00%)

Total [78/78] (100.00%; Normalized 100.00%)
```

For tail call, total 78 tests are passed. (This make take a few minutes)
```
$ (cd spectec-gc; ./interpreter.sh tail-call)
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== return_call.wast =====
- 31/31 (100.00%)

Total [78/78] (100.00%; Normalized 100.00%)
```

For gc, total 449 tests are passed.
```
$ (cd spectec-gc; ./interpreter.sh gc)
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== ref_test.wast =====
- 69/69 (100.00%)

Total [449/449] (100.00%; Normalized 100.00%)
```

##### b. multiple memories proposal
For multiple memories, total 718 tests are passed.
```
$ (cd spectec-mm; ./interpreter.sh multi-memory)
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== store1.wast =====
- 8/8 (100.00%)

Total [718/718] (100.00%; Normalized 100.00%)
```

##### c. extended constant expressions proposal
For extended constant expressions, total 8 tests are passed.
```
$ git checkout const
$ (cd spectec-const; ./interpreter.sh extended-const)
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== data.wast =====
- 4/4 (100.00%)

===== global.wast =====
- 4/4 (100.00%)

Total [8/8] (100.00%; Normalized 100.00%)
```

In total, 1,331 tests in the five proposals are passed.
