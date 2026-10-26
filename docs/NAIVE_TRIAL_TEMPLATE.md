# Naive trial composition and static checks

The fixed trial template applies the original H gates, 256 controlled additions
using the G rows, 256 using the Q rows, and the original two inverse QFTs. Its
Straight observation suffix reads the same 512 bits in the same order. For
`order • Q = 0`, its complete ordered instrument equals `naiveObserved Q`.
No large gate list or coefficient table is expanded to prove this equality.

Static well-formedness covers every submitted slot, including inactive gates.
All non-X gates controlled by constants depend only on the infinity bit. Their
legality is checked using both finite-point and zero-point evaluations; X gates
are directly well formed. The actual fixed layout then supplies disjointness
for each point-add. QFT, H, and observation slots are checked separately.

The generic `straightWires` and `straightT` bounds inspect all submitted slots,
not an input-dependent active subset. Their soundness is proved for arbitrary
constant reads and histories, including both outcomes of each measurement.
`observedTrialProgram_resources` instantiates these bounds for every Q without
an order assumption. The single trial has exactly 512 measurements and exactly
`trialGates.length + 1024` submitted gate slots.

The qubit and T bounds in `observedStaticBounds` remain closed symbolic
expressions from the submitted syntax. This increment does not claim a new
concrete numerical qubit/T score or an organizer-selected admission limit.
The 26-trial reset/repetition template, absolute decoder indices, final
verified-candidate probability, and numerical resource certificate remain to
be connected before a complete B2 certificate can be claimed.
