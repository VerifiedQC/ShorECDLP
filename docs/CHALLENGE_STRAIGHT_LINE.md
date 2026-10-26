# Straight-line record controls

Tracker: #462, A4b. Supersedes arbitrary Template measurement branching for
the accepted submission language; the old Template module remains a proof/API
dependency but must not be accepted as an alternative by the final judge.

Straight n start finish is first-order data with four constructors:
done, gate, recordGate, measure. A record control contains Fin start, so a
future or nonexistent record cannot be named. Measure advances the cursor by
one; no constructor chooses different suffix programs. Protected interpretation
expands the SAME suffix with false/true appended to the record.

Straight.append composes compatible cursors. Measurement count is finish-start
on the worst-case counter, independently of Q/history. gateSlots includes every
optional constant/record gate, even when not triggered. allGateCount on the
interpreted AdaptiveCircuit is bounded by gateSlots. Literal H, X and CX all
occupy a slot. Constants, wires and references cannot be computed by a submitted
callback during interpretation.

The evaluator must require gateSlots and finalCursor under organizer-fixed
limits, and accept only StraightEntry. Numeric limits are not selected in this
increment. This is a precise resource contract; it is not a theorem of classical
ECDLP hardness. A quantum/classical hybrid attack is allowed or excluded by the
explicit published decoder and budget rules, not by Lean guessing its intent.

Parser, protected decoder, official policy limits, hostile environment isolation
and baseline migration remain unfinished. No whole-challenge acceptance claimed.
