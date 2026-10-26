# Naive constant-subtraction template

This increment compiles the coordinate-constant subtraction block used by the
Naive point-add implementation. It does not compile a complete point-add or ECDLP
trial.

`fieldLoadGates` contains only fixed wire addresses and fixed constant-bit
references. The evaluator selects X gates from those bits. The submitted data
never receives Q. Bits above position 255 generate no gate: `fieldValue_lt`
proves that all protected field values fit in 256 bits, including transformed
coordinates and the infinity flag. Thus the original 257-bit arithmetic register
retains its zero high bit without querying an out-of-range reference.

`fieldSubConstGates_source` proves equality with the complete original
`fieldSubConst` gate list: input copy, constant load, modular subtraction,
output copy, reverse arithmetic, constant unload, and input cleanup. The fixed
modular-subtraction expression repeats the original private core definition;
the Lean equality checks that they agree. Any drift must still satisfy this
proof.

The concrete coefficient row `qCoefficient = (0,1)` denotes Q for every input
point. `qFieldSubProgram_run` proves exact equality of the ordered quantum
instrument for the fixed Straight program and the original coordinate
subtraction. The same table reference is used for load and unload. There are no
measurements or record controls in this block. Its start and end cursors coincide.
`constantGateProgram_slots` counts every submitted slot, including disabled
constant-bit gates.

Remaining B2 work includes the other constant-dependent arithmetic blocks,
complete point-add/trial compilation, static well-formedness and resource bounds
for the full submitted program, absolute decoder-position binding, and the final
protected-evaluator certificate. This increment does not discharge these tasks.
