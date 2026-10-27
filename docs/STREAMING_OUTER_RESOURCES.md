# Streaming outer resource bounds

The bounds apply to the actual `OuterPlan.entry` program from
`STREAMING_OUTER.md`. They remain parameterized by the producer's window
programs and reset list. They are not numerical claims about an unfinished
Streaming baseline.

Let every window have at most S syntactic gate slots, T abstract T cost, and M
measurements. There are 16 left windows, 13 right windows, and 56 rounds.

| Metric | Whole-entry upper bound |
| --- | --- |
| Gate slots | `56 * (29*S + 54634)` |
| Abstract T model | `56 * (29*T + 54168)` |
| Measurements | `56 * (29*M + 464 + reset.length)` |
| Physical qubits | `support.toFinset.card` |

The shared support must contain every window's actual wires for every public
point and incoming history, the Fourier bank, the reset list, and wire 836.
Repeated use of the same physical labels does not increase this bound. A
per-window qubit count without a common wire set is not sufficient to establish
this shared-support result.

The Fourier feedback contributes 32,640 slots on the 256-bit left axis and
21,528 on the 208-bit right axis. These total 54,168. Each feedback slot costs at
most one T in the protected abstract model; this is an upper bound, not an
exact realized T count or a rotation-synthesis estimate. Hadamards add 464 slots
per round and the two control-wire X gates add two more. They add no T cost.
Reset adds one measurement per listed wire, but no gate slots or T cost.
The actual measurement count remains exactly `56 * p.stride`.

`OuterBudget coefficients p` is the producer interface. Its fields supply S,
T, M, the shared support, and their uniform proofs. `OuterBudget.resources`
proves all three `Bounds` inequalities. `gateSlots` and `finalCursor` prove the
syntactic admission quantities. `OuterBudget.assembly` fills the resource
fields of `StreamingAssembly` from these local proofs.

Window physical validity and the protected decoder's 99% success statement
remain separate hypotheses. The budget does not prove point-addition
correctness, clean scratch/reset behavior, or an actual final numerical score.
After those proofs arrive, `StreamingAssembly.certificate` connects the entry
to the organizer's admission limits.
