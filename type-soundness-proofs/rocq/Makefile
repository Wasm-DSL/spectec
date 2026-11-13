default:
	rm -f *.opam
	opam repo add rocq-released https://rocq-prover.org/opam/released
	opam install dune.3.23.1 rocq-runtime.9.1.1 rocq-core.9.1.1 rocq-mathcomp-ssreflect.2.4.0 rocq-stdlib.9.0.0 coq-record-update.0.3.6 coq-flocq.4.2.2 coq-compcert.3.18 coq-ext-lib.0.13.1 coq-parseque.0.2.2 coq-wasm.2.2.0
	dune build

clean:
	dune clean

test:
	dune clean
