# Actual absolute sample records

`repeatedTrialPositions` fixes the two 256-bit sample words of round t at
`t * 207136` and `t * 207136 + 256`. There is no Q-dependent address.

`readWord_range` proves that the protected reader returns exactly the
little-endian value of the corresponding history slice, provided the history
is long enough. `naiveRepeatedEntry_history_length` supplies that length for
every actual branch of the compiled entry under `order • Q = 0`.

`fixedRepeatedSuccess_actualWords` proves that every successful history has
one of the 26 fixed position pairs whose actual protected reads satisfy the
original canonical recovery predicate. This is a record-value correspondence,
not merely a bound on the indices.

`repeatedDecodeLayout` fixes the protected nearestPair tag and all 26 trials.
`repeated_success_candidate` and `repeated_success_verified` show that the
actual canonical recovery is present in the protected candidate list and
passes the final public group-relation check. There are at most 26 candidate
checks for any history.

`naiveRepeatedEntry_verified_success` transfers the ≥99% probability to the
actual protected verifiedCandidate event by monotonicity of filtered Born
mass. `naiveRepeatedEntry_certificate` assembles the full semantic Certificate
for organizer limits that cover the fixed gate slots, 5385536 measurements,
512 coefficient rows, and 26 candidate checks. Limits remain explicit inputs;
this theorem does not set organizer policy or presume admission.

The resource bounds cover all 26 rounds but remain symbolic. Concrete qubit
and total T evaluation is a separate publication obligation. The certificate
also does not assert that an actual Eigen deployment uses the local harness.
