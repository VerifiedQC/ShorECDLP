# Local kernel replay and regression gate

Tracker: #462, A4/A5. This prepares local verification; it is not the deployed Eigen judge.

`python3 scripts/challenge/gate.py --source-only` rejects the explicit `skipKernelTC` option in project Lean sources before compilation. The check deliberately also rejects that spelling in comments and quoted identifiers. It is conservative text policy, not a Lean parser and not a proof that arbitrary elaborator code cannot manipulate the environment.

After building, `python3 scripts/challenge/gate.py --replay ShorECDLP.Challenge` launches the pinned toolchain's `leanchecker` in a separate process. It replays every compiled module under that prefix with the Lean kernel, prints leanchecker’s actual module list, and reports its size. A successful command with no reported modules is rejected. Submitted source commands and options do not control this replay. This uses the same kernel implementation, with imported dependencies as its base; it is not an independent kernel implementation or a fresh replay of Mathlib. Existing exact and exhaustive axiom audits remain mandatory: replay alone permits declared axioms.

The checked prefix is an organizer argument. The current CI integration checks the protected Challenge modules. A release judge must also replay every allowed submission/proof module and its untrusted import closure; a submission cannot choose that list. The current call does not certify the entire old Submission tree by kernel replay.

## Sealed artifact root

Use the protected `scripts/challenge/stage-entrant.py` command before supplying
`--artifact-path` to the replay gate or an argument to `judge.lean`. The path is a
**combined root**, not a sparse Entrant-only directory: Lean resolves a package
prefix from one root, so a sparse `ShorECDLP/Submission/Entrant` tree can hide
`ShorECDLP/Challenge` and other trusted imports (#552).

The organizer builds trusted dependencies from its pinned protected checkout.
After the isolated candidate worker stops, stage into a fresh organizer-owned
empty directory outside that worker:

```sh
python3 /trusted/scripts/challenge/stage-entrant.py \
  --candidate /stopped-candidate --overlay /sealed-root \
  --trusted-lib /trusted/.lake/build/lib/lean
python3 /trusted/scripts/challenge/gate.py --root /trusted \
  --replay ShorECDLP.Submission.Entrant --artifact-path /sealed-root
# Run from /trusted with its pinned Lake/toolchain environment:
lake env lean --run scripts/challenge/judge.lean /sealed-root
```

Staging copies trusted dependencies first, removes any pre-existing trusted
Entrant subtree, and copies only compiled artifacts for the candidate's Entrant
source modules. Worker artifacts for protected modules never replace trusted
ones; symlinked worker paths are rejected. `artifacts.py` supplies this same
staging operation to the benchmark CLI, organizer example adapter and judge
regressions. The caller must keep the worker stopped and the result inaccessible
to it throughout replay and judging; staging is not a sandbox or a defense
against concurrent filesystem mutation.

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

Each negative fixture asserts its specific Lean diagnostic, including the expected protected type or failed arithmetic claim. A syntax error or missing import alone cannot satisfy these assertions.

A second fixture deliberately disables the compiler's kernel check and injects a theorem of False with the proof of True. The source policy rejects it. The test then intentionally bypasses that text policy, compiles the known fixture, and requires a kernel error when replaying its actual .olean. Thus the replay test cannot pass merely because compilation failed or a text pattern was found.

These are interface and kernel regressions. The positive case has no 99% ECDLP success certificate. It is not a claim that a complete competition submission was accepted, nor that the current Eigen benchmark rejected these attacks.

The judge regressions additionally reproduce the missing protected import from a sparse
Entrant artifact root, then require independent replay to succeed after shared staging.
All six certificate/metric fixtures also use that staging path, including rejection
of forged certificates and macro-based type substitution.

## Release obligations

The actual Eigen judge package and its editable-path contract are still missing. The organizer must pin and protect the toolchain, dependencies, checker scripts, resource functions, decoder, contract and policy limits. Compile untrusted Lean only in a disposable sandbox without credentials or write access to the trusted checkout. Supply the replay module set from the trusted build manifest. Check the exported certificate against the exact protected proposition and the same submitted data, rather than trusting a similarly named declaration or an entrant-generated wrapper. Arbitrary elaborator macros and initialization code make source-level name checks insufficient as a final admission check.

Candidate-check limits count candidates, not every machine instruction. Quantum gate slots, record count, coefficient-table size, candidate limits and external worker time/memory limits remain separate controls. Neither budget48 nor budget55 is selected by these scripts.
