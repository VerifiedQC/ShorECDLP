# Fixed reset table for Naive

Tracker: #462, B2. Depends on the physical bridge in PR471.

`fixedResetWires` is the constant list 0 through 206623. `bitcoinECDLPTrial_fixed_support` exposes the existing dense-envelope argument as a wire-inclusion theorem, and `naiveObserved_fixed_support` includes the added readout operations. Both hold for every Q, without assuming Q is nonzero.

`fixedResetTrial` uses that same table for every key. Every branch starts the next trial in a scalar multiple of zero. Each trial has exactly 207136 records: 512 output bits and 206624 reset outcomes. Twenty-six trials therefore have exactly 5385536 records. `fixedRepeated_success` preserves the ≥99% guarantee for every valid nonzero key.

`resetWireProgram` compiles any fixed reset table into Straight measurement instructions, with no constant-bit queries, record-controlled gates or unitary gate slots. Its complete ordered instrument equals the reset suffix used in the probability proof. The fixed table is represented symbolically and is not expanded by a large kernel computation.

This closes the Q-dependent reset-table and transcript-width gap in PR471. It does not yet compile Naive's original arithmetic/constant loads, prove that each absolute output position returns its designated register bit, instantiate the protected DecodeLayout/verifiedCandidate, or provide the final resource Certificate. The output-index bound proves only that proposed indices are in range; it is not a semantic record-binding theorem.
