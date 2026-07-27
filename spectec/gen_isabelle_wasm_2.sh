#!/bin/bash

./spectec -l -ll ../specification/wasm-2.0/* isabelle/wasm-2.0/C-mech-aux.spectec  --isabelle -o isabelle_reference_output_wasm2.thy && \
mv isabelle_reference_output_wasm2.thy isabelle_type_safety_proof/.
