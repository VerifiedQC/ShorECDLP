# Streaming static support (work in progress)

The shared candidate allocation is `batchedResetWires` in `WindowBody.lean`.
It contains 854 original wires, 2,565 endpoint-bank wires, and 512 flag/comparator
auxiliary wires: 3,931 list entries. The earlier 3,932 estimate used a conservative
855-wire original allocation. The one-wire difference is the unused wire 837,
not zero-based numbering. Wire 838 (the infinity flag) remains allocated.
Address/sign wires 839–854 are relocated to 855–870.

`BatchSupport.lean` proves that every static correction-block wire, after both
actual permutations, lies in this allocation. Disabled constant-controlled gates,
measurement targets, record-controlled gates, and both corrections are included.
The temporary sixth component word is moved onto actual accumulator ports.

`ArithmeticSupport.lean` proves support transfer for compiled adders, comparisons,
negation and the actual shared Y-negation stage. `ControlSupport.lean` additionally
proves removal of the comparator's virtual control, then covers modular addition
and the actual constant-field lookup stages.

`WindowSupport.lean` provides explicitly conditional composition lemmas. Its
`batchedOuter_qubits_le_of_coordinate` bounds the cardinality of the actual
program's deduplicated wire set for any repetition count, **assuming** concrete
coordinate-compiler support. It does not infer program support from reset-list
length and is not a completed Streaming resource certificate.

Remaining: discharge coordinate-compiler support, including division,
multiplication and square-subtraction, before claiming an unconditional whole
program bound. Success semantics and the final challenge certificate are separate
obligations. The frozen published challenge is unchanged.
