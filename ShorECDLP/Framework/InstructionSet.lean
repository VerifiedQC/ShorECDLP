/-
# Instruction set (M0 skeleton)

The primitive gate set over which every ShorECDLP circuit is built. M0 seeds only
the basic gates; the controlled modular-arithmetic building blocks (modular
multiplication, Fermat inversion, elliptic-curve point addition) are layered on top
in M1–M2 as *derived* circuits over this set, never as new primitives — so the cost
model has a single, small trusted surface to count against.
-/

namespace ShorECDLP

/-- A qubit / wire index. -/
abbrev Wire := Nat

/-- The primitive gate set. Kept deliberately minimal: X, H, CNOT, Toffoli.
Higher-level arithmetic is expressed as `List Gate` circuits over these, so the
Toffoli-caliber cost model (see `CostModel`) counts exactly the constructed circuit. -/
inductive Gate where
  /-- Pauli-X (logical NOT) on `target`. -/
  | X    (target : Wire)
  /-- Hadamard on `target`. -/
  | H    (target : Wire)
  /-- Controlled-NOT: flips `target` when `control` is set. -/
  | CX   (control target : Wire)
  /-- Toffoli (CCX): flips `target` when both `c1` and `c2` are set. -/
  | CCX  (c1 c2 target : Wire)
  deriving Repr, DecidableEq

/-- A circuit is a straight-line list of primitive gates. -/
abbrev Circuit := List Gate

end ShorECDLP
