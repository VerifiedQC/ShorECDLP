# Streaming outer program

This component builds the actual protected straight-line outer program. Window
bodies remain parameters. It does not provide a complete Streaming certificate.

`OuterWindow n` contains a fixed measurement count and a compiler
`(start : Nat) → Straight n start (start + count)`. The producer supplies 16 left
windows (the first lookup followed by 15 additions) and 13 right windows. All
windows use the same coefficient table. A body must not include the outer
Hadamards or Fourier readout.

`standardOuterPlan` fixes the Fourier bank to wires 870 through 855. Every window
prepares that bank with Hadamards in the opposite order, runs its body, and
performs inverse semiclassical Fourier readout. The next bank receives the
newest Fourier bits first, followed by earlier bits on the same axis. The right
axis starts with an empty Fourier history. Each round toggles wire 836 before
and after the two axes, then runs the explicitly supplied reset list. The entry
repeats this round 56 times. Additional endpoint scratch wires must be covered by
the producer's reset/cleanliness proof; the old 854-wire count is not assumed.

The round measurement stride is the sum of the 29 body counts, 464 Fourier
measurements, and the reset-list length. `OuterPlan.layout` derives every
absolute decoder position from those counts, with 256 left bits and 208 right
bits per round. It does not reuse `legacyTrialStride`.

## Evidence

- `straight_append_branch` splits an actual branch into actual prefix and
  suffix branches. It preserves the composed Kraus map and chronological
  records. The history supplied to the suffix equals the old history followed
  by the actual prefix outcomes.
- `outerAxis_records`, `OuterPlan.round_records`, and
  `OuterPlan.repeat_records` carry that evidence through the entire program.
- `OuterPlan.entry_records` proves every selected position is an actual Fourier
  outcome bit. The Fourier branch is evaluated with a history equal to the
  full execution's prefix at that bank. Reset outcomes and window-internal
  measurements affect offsets but are not selected as Fourier bits.
- `OuterPlan.layout_trial` binds those positions to the submitted DecodeLayout.
  `OuterPlan.entry_reads` proves both protected `readWord` calls succeed on
  each actual execution branch.
- Window well-formedness implies well-formedness of the complete entry.
  `OuterPlan.entry_history_length` proves its exact record length.
- `OuterPlan.assembly` supplies the shape and physical-composition fields of
  the existing `StreamingAssembly` interface. Uniform resource inequalities
  and the 99% protected-decoder success statement remain explicit hypotheses.
  `OuterPlan.candidate_budget` reuses the fixed budget55 theorem.

## Remaining integration

Instantiate the window bodies and coefficient table, prove their physical
validity, bind their execution to the intended point arithmetic, justify reset
and scratch cleanliness, and prove actual resource bounds and success. Then
use `StreamingAssembly.certificate` with the actual syntactic gate-slot,
record, and table budgets. These obligations are not discharged by this file.
