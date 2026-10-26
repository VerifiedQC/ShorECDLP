# Naive controlled point-add template

This increment compiles `controlledPointAddOut` and the in-place
`controlledPointAdd` into fixed constant-bit gate lists and Straight programs.
For every input point, the instantiated gate list equals the original circuit;
the ordered quantum instrument therefore also agrees exactly.

The decomposition covers coordinate subtraction, generic affine arithmetic,
branch flags, the doubling branch, packed 513-bit point loading, selection,
cleanup, and the negative-point inverse used by the in-place operation.
The packed word uses the original finite flag followed by 256 x bits and 256 y
bits. Its bit correspondence is proved against `encode`, rather than inferred
from wire counts.

The zero constant point is included. Fixed gates of the finite branch are
individually enabled by the protected infinity bit being false. Coordinate
loads are already disabled at zero, because all coordinate fields are zero;
the finite tag is also disabled. The zero branch copies the input exactly as
the original implementation does. No conjunction of two constant controls and
no classical callback is introduced. The negative-point pass only swaps y and
negative-y field references; the protected evaluator still computes the fields.

`naivePowerTable` is fixed data with 512 rows: 256 powers of G and 256 powers of Q.
Each row contains canonical scalar residues. `naivePowerTable_get` binds the
list representation to its coefficient function. G row correctness uses the
proved generator order. Q row correctness explicitly requires `order • Q = 0`;
`dlogPoint_order` discharges that condition when Q is a multiple of G.
`gPowerProgram_run` and `qPowerProgram_run` connect these rows to the original
controlled point-add programs.

This is not a complete B2 certificate. Full trial/QFT composition, fixed
readout/decoder binding, static well-formedness and resource certificates, and
final admission through the protected evaluator remain to be completed.
