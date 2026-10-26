# Naive readout and physical repetition

Tracker: #462, B2. This component supplies an explicit adaptive measurement and reset bridge for the existing Naive unitary circuit. It does not yet compile that circuit's public-key constants into a protected StraightEntry.

`observeWires` uses a fixed wire list. Each bit is read by H followed by the existing X-measure/reset primitive, then restored with an X controlled by the newest fixed record index. Each actual branch is exactly a Z projection. `observeWires_jointProbability` equates the probability of the recorded register pair with the old `jointRegisterProbability`, for arbitrary (including entangled) states. Register values are little-endian. The probability event reads the newly produced local transcript; integrating these positions into the final absolute DecodeLayout remains separate work.

`resetTrial` appends X-measure/reset of every distinct wire used by the adaptive trial. The proof includes the frame outside this support. Every branch starting from zero therefore returns to a scalar multiple of the same zero state. All reset outcomes remain in the instrument, and reset preserves the original readout event mass.

`repeatFixed` is actual sequential AdaptiveCircuit composition. Its success event parses fixed-size trial transcripts and ignores each reset suffix. `resetTrial_twentySix` derives the formula 1−(1−p)^26 from these Kraus branches and their reset property; independence is a conclusion, not an external assumption.

`naiveRepeated_success` instantiates this construction with `bitcoinECDLPSubmission.program Q`. It obtains at least 99% success for each valid nonzero Q=d•G using the existing 41/250 lower bound and 26-trial numerical theorem. The secret appears only in the success specification, never in the program. The fixed canonical postprocessor is unchanged.

Remaining B2 work: replace `program Q.wires.dedup` with one fixed reset wire table and prove `program Q.wires ⊆ fixedResetWires` for every Q. The current reset set and per-trial record width `512 + (naiveObserved Q).wires.dedup.length` both depend on Q through its gate list; they cannot be submitted as the fixed template or fixed DecodeLayout. Derive one fixed transcript stride and absolute decoder positions from the replacement table. Then compile the original public-key-dependent constant loads and arithmetic into the protected straight-line template; connect the actual absolute record positions to DecodeLayout and verifiedCandidate; prove final resource bounds for that same submitted program and construct the protected Certificate. No completed challenge submission or deployment-level admission is claimed here.

The generic repetition proof follows the existing sequential-instrument proof in the 2607 submission, specialized here to fixed transcript lengths. It imports only shared Framework/Math modules and Naive modules, preserving submission isolation.
