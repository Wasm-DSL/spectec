IL_DUMP_DIR="./test-lean-backend/il_dump"

if [ -n "$(ls -A "$IL_DUMP_DIR" 2>/dev/null)" ]; then
    read -p "$IL_DUMP_DIR is not empty. Delete its contents? [y/N] " confirm
    if [ "$confirm" = "y" ] || [ "$confirm" = "Y" ]; then
        rm -rf "${IL_DUMP_DIR:?}"/*
    else
        echo "Aborting."
        exit 1
    fi
fi

make

for i in 1 2 3; do

    ./spectec ../specification/wasm-${i}.0/* \
        --print-all-il-to "./test-lean-backend/il_dump/wasm${i}.0_%s.il" \
        --ite \
        --let-intro-mech \
        --typefamily-removal \
        --remove-indexed-types \
        --totalize \
        --else \
        --else-simplification \
        --uncase-removal \
        --sub-expansion \
        --pattern-simp \
        --sub \
        --definition-to-relation \
        --sideconditions \
        --alias-demut \
        --improve-ids \
        --single-pattern-match
done


for i in 1 2 3; do

    ./spectec ../specification/wasm-${i}.0/* \
        --print-il-as-ast \
        --print-all-il-to "./test-lean-backend/il_dump/wasm${i}.0_ast_%s.il" \
        --ite \
        --let-intro-mech \
        --typefamily-removal \
        --remove-indexed-types \
        --totalize \
        --else \
        --else-simplification \
        --uncase-removal \
        --sub-expansion \
        --pattern-simp \
        --sub \
        --definition-to-relation \
        --sideconditions \
        --alias-demut \
        --improve-ids \
        --single-pattern-match
done
