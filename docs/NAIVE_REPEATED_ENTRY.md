# Fixed 26-round Naive entry

`naiveRepeatedEntry` is a single protected `StraightEntry`. Its coefficient table,
program, reset wires, and record positions are fixed independently of Q.
Each round runs the compiled 512-bit observed trial and resets all 206624
fixed wires. The full entry has 5385536 measurement records.

`naiveRepeatedEntry_run` proves equality of the complete ordered instrument
with the existing `fixedRepeated Q`, assuming `order • Q = 0`.
`naiveRepeatedEntry_success` transfers the existing 99% success result for
nonzero Q = d • G. The secret d occurs only in the event specification.
The proof includes the reset outcomes and does not postulate independence.

Every submitted slot is well formed. `repeatedStaticBounds` bounds the entire
26-round program, including reset, for every Q. Its T bound is the static cost
of the entire entry, not the cost of one round. Qubit and T bounds remain
closed symbolic syntax expressions; no new numerical score is claimed.

`repeatedSampleStart` gives the absolute offset t * 207136. Its bound theorem
only establishes valid indices. It does not establish decoder correctness.

The success event here is `fixedRepeatedSuccess`, not yet the protected
`verifiedCandidate` event. Binding the fixed nearestPair decoder to these
records, concrete resource evaluation, and assembly of the final admission
Certificate remain open. This component is not a completed B2 submission.
