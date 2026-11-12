default:
	rm -f *.opam
	dune build @opam
	opam repo add rocq-released https://rocq-prover.org/opam/released
	opam install .

clean:
	dune clean

test:
	dune clean
