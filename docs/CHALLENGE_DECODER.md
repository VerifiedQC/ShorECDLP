# Fixed decoding and certificate interface

Tracker: #462, A3. Depends on PR463/PR464; not a release runner.

No submitted decoder/parser function is accepted. DecodeLayout is data: a fixed
algorithm tag, two positive widths bounded by 512, and at most 56 trial position
vectors of those widths. Positions are absolute, zero-based, little-endian.
A missing position rejects that trial. Neither parsing nor candidate generation
receives Q. Only verifiedCandidate checks the public group relation afterward.

The protected candidate generator uses the upstream half-bin interval, optional
zero-endpoint wrap, and nearest-left-numerator inverse formulas. Its namespace
and imports are protected. It imports no editable Submission code.

The per-trial bound is 2*(order / 2^rightBits + 2); the protected list cap is
proved never to truncate. The total declared bound used for admission is
numberOfTrials * perTrialBound, not observed/unique candidates for one sample.
At 256/208 the bound is 2^49+2 per trial; at 256/256 it is 4. Explicit candidate
enumeration at the former scale is enormous: these are mathematical definitions,
not a claim of efficient practical classical execution.

Certificate binds a StraightEntry's interpreted circuit to:
- well-formed primitive gates;
- organizer-fixed gate-slot, measurement, coefficient-table and candidate budgets;
- qubit, T-model and measurement upper bounds for that SAME circuit;
- ≥99% decoded acceptance for every nonzero Q=d•G from zero state.
Protected group-order mathematics proves every accepted candidate equals d mod order.

Limits is organizer policy. The release judge must fix its values before importing
a submission and check a fully qualified Certificate at those exact values.
Accepting solver-selected Limits or a different proposition would re-open the
trust boundary. Numeric policy, ingestion/kernel isolation and baseline
equivalence/success proofs remain pending.

The baseline migration must prove absolute record-position extraction equals
its former parser, and the accepted candidate event equals its original event.
Those are not inferred from this API or from resource-count agreement.

The organizer configuration exposes budget48 = 2^48 and budget55 = 56 * (2^49 + 2), without a default. Certificate.candidateChecks_le bounds the entire candidate list for every history, using the actual trial count. The 56-trial 256/208 baseline does not satisfy budget48. Other admission limits remain explicit organizer parameters.
