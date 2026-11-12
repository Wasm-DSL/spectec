Read every document in `spectec/src/test-lean-claude/claude-logging`. You are a new Claude session taking over from the one that wrote `claude-logging`. In particular, the verbatim dialogue between me and the previous session is documented in `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log`, where every bundle refers to a prompt + response. Follow the chain of thought within `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log`, and understand what `spectec/src/test-lean-claude` is and what all the documents are within it / why they exist.

You should not only understand the documents in `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log`, but also *BEHAVE* as if you are that claude session -- I gave a series of standing / long-term instructions in previous prompts to that claude session that you must continue to follow. In particular, I want you to follow the safety constraints I previously stated, as well as the logging obligations for every prompt and response -- even mid-process promts + responses.

Once you are done, understand the rest of my instructions:

___

I've manually re-synced to upstread HEAD (i.e. merged in rocq-backend-proof). Do the following:

1. Check if I did it correctly. If not, stop here and report.
2. I don't understand why the local `spectec/test-rocq/theories` not being up to date would affect you -- you should be looking at the git repository I gave you, is that not up to date? Either way, check that you are well-positioned to get the latest Rocq proof in order to resume porting. If you find you have to mutate anything outside of `spectec/src/test-lean-claude`, stop and let me know. To clarify, your safety bounds still allow you to *read* outside of `spectec/src/test-lean-claude`, just not mutate / write / post outside of `spectec/src/test-lean-claude`. To clarify, you should be reading the live online Github Rocq proof, not the local one.
3. Once you're done, go back to `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle1` and `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle2` and re-do anything that needs to be updated based on the live Github Rocq proof, if you were previously working using the local one. *Don't* touch previous bundles! Just add them to your new `bundle3`.
4. Finally, report to me the current status.

You might run out of usage time  or be interrupted halfway through -- just be prepared for that.
