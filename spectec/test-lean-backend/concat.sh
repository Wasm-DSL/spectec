#!/bin/bash

separator=";; ──────────────────────────────────────────────────────────────────────────────"

# Erase the file's contents and start anew
: > "./test-lean-backend/test.spectec"

specVersion="$1"

if [ -z "$specVersion" ]; then
    specVersion=3
    echo "Warning: no spec version given, defaulting to $specVersion" >&2
fi



find "../specification/wasm-$specVersion.0" -name "*.spectec" | sort |
while IFS= read -r file; do
    echo "Processing $file"
    cat "$file" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
done