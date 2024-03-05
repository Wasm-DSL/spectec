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

## Running Latex Backend

The tool can splice Latex formulas generated from, or expressed in terms of, the DSL into files. For example, invoking
```
watsup <source-files ...> -p <patch-files ...>
```
where `source-files` are the DSL files, and `patch-files` is a set of files to process (Latex, Sphinx, or other text formats), will splice Latex formulas or displaystyle definitions into the latter files.

Consider a Latex file like the following:
```
[...]
\subsection*{Syntax}

@@@{syntax: numtype vectype reftype valtype resulttype}

@@@{syntax: instr expr}


\subsection*{Typing @@{relation: Instr_ok}}

An instruction sequence @@{:instr*} is well-typed with an instruction type @@{:t_1* -> t_2*} according to the following rules:

@@@{rule: InstrSeq_ok/empty InstrSeq_ok/seq}

@@@{rule: InstrSeq_ok/weak InstrSeq_ok/frame}
[...]
```
The places to splice in formulas are indicated by _anchors_. For Latex, the two possible anchors are currently `@@` or `@@@`, which expand to `$...$` and `$$...$$`, respectively (for Sphinx, replace the anchor tokens with `$` and `$$`).

There are two forms of splices:

1. _expression splice_ (`@@{: exp }`): simply renders a DSL expression,
2. _definition splice_ (`@@{sort: id id ...}`): inserts the named definitions or rules of the indicated sort `sort` as defined in the DSL sources.

See the [documentation](doc/Latex.md) for more details.


## Running Sphinx Backend

The full pdf/html document generation via Sphinx.

To build both pdf and html specification document,
```
$ make
$ cd test-prose
$ make all
```

It splices Latex formulas and typesetted prose into the template `rst` document at `test-prose/doc`.
Then, Sphinx builds the `rst` files into desired formats such as pdf or html.


## Step-by-Step Instructions

We provide instructions to reproduce the results mentioned in Evaluation section.

### 1) Correctness
To run all the official test,
> WARNING: Note that it may take 10 minutes.
```
$ ./correctness.sh
```


### 2) Bug prevention
To inject bugs in the spec and run the spectec,
```
$ ./bug-prevention.sh
```

### 3) Forward competibility

#### a. function references, tail calls proposal, and garbage collection
To run all the test in the proposal,
> WARNING: Note that it may take 10 minutes.
```
$ git checkout artifact-gc
$ ./correctness.sh
```

#### b. multiple memories proposal
To run all the test in the proposal,
> WARNING: Note that it may take 10 minutes.
```
$ git checkout artifact-mm
$ ./correctness.sh
```

#### c. extended constant expressions proposal
To run all the test in the proposal,
> WARNING: Note that it may take 10 minutes.
```
$ git checkout artifact-const
$ ./correctness.sh
```
