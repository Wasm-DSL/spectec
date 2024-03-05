# Artifact For "Bringing the WebAssembly Standard up to Speed with SpecTec"


## Getting Started

### Using a docker container
```
$ docker build -t spectec .
$ docker run --rm -it spectec
```

### Building from source

* You will need `ocaml` installed with `dune`, `menhir`, and `mdx`.

* To run tests, you will also need `pdflatex` and `sphinx-build`.

* Invoke `make` to build the executable.

## Step-by-Step Instructions

### 1) Correctness
```
$ make
$ ./watsup spec/*.watsup --animate --sideconditions --interpreter
```

### 2) Bug prevention
```
$ ./reproduce-2.sh
```

### 3) Forward competibility

#### a. function references, garbage collection, and extended constant expressions proposal
```
$ git checkout artifact-gc
$ make
$ ./watsup spec/*.watsup --animate --sideconditions --interpreter
```

#### a. tail calls proposal
```
$ git checkout artifact-tc
$ make
$ ./watsup spec/*.watsup --animate --sideconditions --interpreter
```

#### a. multiple memories proposal
```
$ git checkout artifact-mm
$ make
$ ./watsup spec/*.watsup --animate --sideconditions --interpreter
```
