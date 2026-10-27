# Protected constant-field menu

Every field is a fixed evaluator definition on **one** coefficient-table point
`C = a • G + b • Q`. Entrants supply only the row, field constructor and bit
index. They cannot supply field functions, change the formulas, inspect Q in a
program generator, or choose a gate address using a computed field value.
The ten new fields are organizer-approved fixed functions, not a general
precomputation callback. They do not add coefficient-table rows.

For a finite C write (x,y) for its field coordinates. Define
`E(z) = if z = 0 then 1 else z`. Define
`u = (s-y)/E(r-x)`, `w = r+2x-u²`, and `H(r,s) = (x-w, u E(w)-y)`.
The denominator goes through E **before inversion**. Replacing this with the
convention `0⁻¹=0` would change the coordinate permutation.
Let `(iD,d,e)` be the canonical encoding of `D=C+C`; if D is infinity then
`iD=true` and `d=e=0`. Doubling uses the group law, including its infinity branch.

| Constructor | Protected value |
|---|---|
| x | x |
| y | y |
| infinity | infinity flag |
| negX | −x |
| negY | −y |
| tripleX | 3x |
| exceptionalZeroX | first coordinate of H(0,0) |
| exceptionalZeroY | second coordinate of H(0,0) |
| negDoubleX | −2x |
| exceptionalNegX | first coordinate of H(x,−y), equal to 4y²−2x |
| exceptionalNegY | second coordinate of H(x,−y), equal to (−2y)E(3x−4y²)−y |
| exceptionalNegDoubleX | first coordinate of H(d,−e) |
| exceptionalNegDoubleY | second coordinate of H(d,−e) |
| doubleX | d |
| doubleY | e |
| doubleInfinity | iD |

All coordinate arithmetic is in Fp and returned as its canonical natural
representative. Flags return 0 or 1. For C=infinity all coordinate fields return
0 and both infinity flags return 1 (`fieldValue_zero`). In particular, the new
menu does not assert that exceptional images themselves lie on the curve.

The menu exposes no entrant-defined algorithm. The source boundary and trusted
artifact overlay still protect these definitions; the trusted judge still checks
the same certificate. Regressions accept a listed field and reject a custom
Point-to-Nat callback and an invented discrete-log field. This is an interface
restriction, not a general computational-hardness theorem.

Using these constants in a migrated circuit still requires proof of endpoint
binding, fixed-address selection, cleanup, and the complete program certificate.
Constant-bit-controlled X gates for a fixed row do not charge T, but selecting a
row with quantum address bits requires an address-selection network. Neither
that cost nor the costs of adjusted endpoint swaps are certified by this menu.

## Compatibility with the original menu

The original coordinate source remains computable by reading `baseFieldValue`
only at its fixed original constructors; those values are definitionally equal
to `fieldValue`. The general protected reader remains `fieldValue`.
The Naive negation/reindexing proof now requires `LegacyField` (the original six
constructors). A compositional proof establishes that its actual gate list only
reads those fields. No negation-invariance claim is made for new exceptional Y
fields, and no new field is silently substituted in the Naive circuit.
