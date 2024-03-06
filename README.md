# Artifact For "Bringing the WebAssembly Standard up to Speed with SpecTec"
This artifact is for PLDI 2024 paper: "Bringing the WebAssembly Standard up to Speed with SpecTec" and includes SpecTec, a domain-specific language (DSL) and toolchain that facilitates both the Wasm specification and the generation of artifacts necessary to standardize new features.


## Getting Started
We support two ways to use SpecTec:

* Using a Docker container

* Building from source

### Using a docker container
We provide a Docker container with SpecTec and its dependencies. You can install the docker by following the instruction in https://docs.docker.com/get-started/ and download our docker image with the following command:
> WARNING: The docker image is 6GB large. Thus, be patient when you download it, and please assign more than 6GB of memory for the docker engine.
```
$ docker pull spectec/spectec
$ docker run --name spectec -it --rm spectec/spectec
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

## Step-by-Step Instructions

We provide instructions to reproduce the results mentioned in Evaluation section of the paper.

### 1) Correctness

#### Formal and Prose Specification
The specification document is generated using the command below.
```
$ make
$ cd test-prose
$ make all
```

#### Interpreter
By running the interpreter.sh, you can see total 24,751 tests are passed in a few minutes.
```
$ ./interpreter.sh
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== nop.wast =====
- 83/83 (100.00%)

Total [23751/23751] (100.00%; Normalized 100.00%)
```

### 2) Bug prevention
Among the four categories that we classified, prose errors and editorial fixes are ???. However, if you see the generated document, our tool doesn't generate such fixes.

For type bugs and semantics bugs, we inject DSL bug and run spectec
```
$ ./bug-prevention.sh
[Building watsup binary ...]
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup
```

For type bugs, you can see SpecTec raises type error.

```
[Injecting error to spec-bugs/type-1/4-runtime.watsup ...]
patching file spec-bugs/type-1/4-runtime.watsup

[Running watsup on spec-bugs/type-1 ...]
spec-bugs/type-1/4-runtime.watsup:164.61-164.63: type error: iteration does not match expected type `eleminst`

[Injecting error to spec-bugs/type-2/7-module.watsup ...]
patching file spec-bugs/type-2/7-module.watsup

[Running watsup on spec-bugs/type-2 ...]
spec-bugs/type-2/7-module.watsup:142.39-142.51: type error: omitted sequence tail does not match expected type `elemidx`

[Injecting error to spec-bugs/type-3/3-typing.watsup ...]
patching file spec-bugs/type-3/3-typing.watsup

[Running watsup on spec-bugs/type-3 ...]
spec-bugs/type-3/3-typing.watsup:296.22-296.24: type error: variable's type `reftype` does not match expected type `tabletype`
```

For semantics bugs, you can see SpecTec raises error during the execution.

```
[Injecting error to spec-bugs/semantics-1/6-reduction.watsup ...]
patching file spec-bugs/semantics-1/6-reduction.watsup

[Running watsup on spec-bugs/semantics-1 ...]
./watsup: uncaught exception Failure("Could not get kind_of_context[CONST_admininstr(I32_numtype, n) TABLE.GROW_admininstr(x)]")
Raised at Stdlib.failwith in file "stdlib.ml", line 29, characters 17-33
Called from Backend_interpreter__Translate.reduction_group2algo.(fun) in file "src/backend-interpreter/translate.ml", line 738, characters 21-40
Called from Stdlib__List.fold_right2 in file "list.ml", line 167, characters 32-58
Called from Backend_interpreter__Translate.reduction_group2algo in file "src/backend-interpreter/translate.ml", line 736, characters 6-298
Called from Stdlib__List.map in file "list.ml", line 86, characters 15-19
Called from Stdlib__List.map in file "list.ml", line 88, characters 14-21
Called from Backend_interpreter__Translate.translate in file "src/backend-interpreter/translate.ml", line 892, characters 37-55
Called from Dune__exe__Main in file "src/exe-watsup/main.ml", line 205, characters 8-30

[Injecting error to spec-bugs/semantics-2/6-reduction.watsup ...]
patching file spec-bugs/semantics-2/6-reduction.watsup

[Running watsup on spec-bugs/semantics-2 ...]
===========================

test-interpreter/spec-test/test-semantics.wast

[Instantiating module...]
[Uncaught exception] Module Instantiation failed due to Failed Array.get during ReplaceE, test-semantics.wast took 2.182000 ms.
Took 2.182000 ms.

[Injecting error to spec-bugs/semantics-3/6-reduction.watsup ...]
patching file spec-bugs/semantics-3/6-reduction.watsup

[Running watsup on spec-bugs/semantics-3 ...]
===========================

test-interpreter/spec-test/test-semantics.wast

[Instantiating module...]
[Invoking foo []...]
 Fail!
 Expected: [(I32.CONST 0x2A)]
 Actual  : Invalid pop: Popall val^n

test-semantics.wast took 2.244000 ms.
Took 2.244000 ms.
```

### 3) Forward competibility

#### Formal and Prose Specification
Also for the proposals, the specification document is generated using the command below.
```
$ git checkout artifact-forward
$ cd test-prose
$ make all
```

#### Interpreter
As we said in the paper, we use reference interpreter for parsing.
Different proposal needs different parser, so we need to change the reference interpreter for each proposal accordingly.
##### a. function references, tail calls proposal, and garbage collection
There is a reference interpreter that includes gc, function references, and tail calls, so we can run it together in artifact-gc branch
```
$ git checkout artifact-gc
```

For function references, total 78 tests are passed in a few minutes.
```
$ ./interpreter.sh function-references
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== return_call_ref.wast =====
- 35/35 (100.00%)

Total [78/78] (100.00%; Normalized 100.00%)
```

For tail call, total 78 tests are passed in a few minutes.
```
$ ./interpreter.sh tail-call
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== return_call.wast =====
- 31/31 (100.00%)

Total [78/78] (100.00%; Normalized 100.00%)
```

For gc, total 449 tests are passed in a few minutes.
```
$ ./interpreter.sh gc
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== ref_test.wast =====
- 69/69 (100.00%)

Total [449/449] (100.00%; Normalized 100.00%)
```

##### b. multiple memories proposal
For multiple memories, total 718 tests are passed in a few minutes.
```
$ git checkout artifact-mm
$ ./interpreter.sh multi-memory
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== store1.wast =====
- 8/8 (100.00%)

Total [718/718] (100.00%; Normalized 100.00%)
```
You can see all the test are passed.

##### c. extended constant expressions proposal
To run all the test in the proposal,
```
$ git checkout artifact-const
$ ./interpreter.sh extended-const
dune build src/exe-watsup/main.exe
ln -f _build/default/src/exe-watsup/main.exe ./watsup

...

===== data.wast =====
- 4/4 (100.00%)

===== global.wast =====
- 4/4 (100.00%)

Total [8/8] (100.00%; Normalized 100.00%)
```

Total 1,331 tests in the five proposals are passed.
