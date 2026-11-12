`ai_principal_typing` was defined in `spectec/test-lean/typing_lemmas.lean`, which you are allowed to copy from, though you should check that it is correct first. Scan `spectec/test-lean/typing_lemmas.lean` and `spectec/test-lean/typing_lemmas.lean` for anything you could use directly.

Also, note that when `spectec/test-lean/typing_lemmas.lean` and `spectec/test-lean/typing_lemmas.lean` were written, `derive_deceq` was not yet available, so watch out for anything using BEq that should really be using `DecidableEq`.

I will need to take a look at the `Vals_ok_non_bot` gap in detail more later, and consider how to fix it, so leave that be for now. If you have any comments or suggestions on this, create a document in your new bundle covering it.

Considering these facts, continue your work.

[Accompanying IDE selection: lines 1433 of /home/zhengyew/spectec/spectec/test-lean/typing_lemmas.lean, reading "Val_ok_non_bot" — the user's note said this "may or may not be related."]
