# Local kernel replay and regression gate

Tracker: #462, A4/A5. This prepares local verification; it is not the deployed Eigen judge.

`python3 scripts/challenge/gate.py --source-only` rejects the explicit `skipKernelTC` option in project Lean sources before compilation. The check deliberately also rejects that spelling in comments and quoted identifiers. It is conservative text policy, not a Lean parser and not a proof that arbitrary elaborator code cannot manipulate the environment.

After building, `python3 scripts/challenge/gate.py --replay ShorECDLP.Challenge` launches the pinned toolchain's `leanchecker` in a separate process. It replays every compiled module under that prefix with the Lean kernel. Submitted source commands and options do not control this replay. This uses the same kernel implementation, with imported dependencies as its base; it is not an independent kernel implementation or a fresh replay of Mathlib. Existing exact and exhaustive axiom audits remain mandatory: replay alone permits declared axioms.

The checked prefix is an organizer argument. The current CI integration checks the protected Challenge modules. A release judge must also replay every allowed submission/proof module and its untrusted import closure; a submission cannot choose that list. The current call does not certify the entire old Submission tree by kernel replay.

## Regressions

`python3 scripts/challenge/regressions.py` uses its own benign fixtures in a temporary directory. It accepts and replays a valid fixed entry and a fixed 512-bit coordinate-copy/measurement program, and checks rejection of:

- an entrant-supplied resource counter;
- a decoder callback receiving Q;
- a generator callback receiving Q;
- a coordinate-copy/measurement program paired with an entrant-supplied history-decoder callback (the final callback is rejected even with a harmless body);
- measurement branch subtrees;
- future record references;
- a namespace-local imitation of a protected entry type;
- a false zero-T cost claim.

A second fixture deliberately disables the compiler's kernel check and injects a theorem of False with the proof of True. The source policy rejects it. The test then intentionally bypasses that text policy, compiles the known fixture, and requires a kernel error when replaying its actual .olean. Thus the replay test cannot pass merely because compilation failed or a text pattern was found.

These are interface and kernel regressions. The positive case has no 99% ECDLP success certificate. It is not a claim that a complete competition submission was accepted, nor that the current Eigen benchmark rejected these attacks.

## Release obligations

The actual Eigen judge package and its editable-path contract are still missing. The organizer must pin and protect the toolchain, dependencies, checker scripts, resource functions, decoder, contract and policy limits. Compile untrusted Lean only in a disposable sandbox without credentials or write access to the trusted checkout. Supply the replay module set from the trusted build manifest. Check the exported certificate against the exact protected proposition and the same submitted data, rather than trusting a similarly named declaration or an entrant-generated wrapper. Arbitrary elaborator macros and initialization code make source-level name checks insufficient as a final admission check.

Candidate-check limits count candidates, not every machine instruction. Quantum gate slots, record count, coefficient-table size, candidate limits and external worker time/memory limits remain separate controls. Neither budget48 nor budget55 is selected by these scripts.
