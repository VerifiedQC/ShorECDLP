# Protected challenge interface (initial A1–A2)

Tracker: #462. This is a migration API, not a release-ready judge.

Protected imports are Framework and Math only. Challenge modules must be locked
by the future evaluator. Entrants may not declare names in their namespaces or
supply compiled objects for them.

## Data and instantiation

- Entry.coefficients: a finite list of canonical scalar pairs (a,b), each < order.
- Entry.template: first-order data indexed by that list's length.
- TemplateGate.literal: a fixed primitive Gate.
- TemplateGate.whenBit: fixed gate, table index, field, bit index <256, Boolean polarity.
- Fields: x, y, infinity, negX, negY, tripleX. Infinity is 1 at bit zero only.
- Template: done, unitary block, X measurement/reset with two fixed continuations.
- Template.seq and instantiate_seq allow compositional migration.
- Entry.program supplies only the protected bit reader for a•G+b•Q.
- Template.WellFormed entails well-formed instantiated circuits for every Q.

Generic instantiate(read) is a proof/composition helper. The release judge must
use Entry.program, never accept a submitted read callback or arbitrary program Q.
The ingestion layer must check a fixed closed Entry and protected-name ownership;
Lean type signatures alone are not a hostile build sandbox.

## Counts

resources uses the protected AdaptiveCircuit representation. It computes distinct
wire labels, existing T-model count, worst-case measurements, CCX count, and
non-Clifford count (CCX plus P at precision k≥3). Main score is T-model count.
There is no submitted cost function. P costs one T-model unit regardless of
precision under the existing model. This is not physical rotation synthesis.

## Deliberate remaining scope

A3 is not implemented here: the release decoder must have a protected parser,
fixed candidate algorithm and bounded parameter menu. A function of history can
still invert Q if the circuit first copies Q to that history, so an editable
history-only decoder is not sufficient.

A4 ingestion/namespace/kernel/environment protection and A5 actual attack
rejection are pending. Smoke tests check count semantics and template proofs;
they do not claim the missing Eigen benchmark rejected a cheating submission.

The existing baseline has not yet been migrated. No overall success probability
or official new score is claimed by this increment.
