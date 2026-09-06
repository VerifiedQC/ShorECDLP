import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.OfFn

/-
# Classical doubling tables for elliptic-curve scalar multiplication (M2)

The ECDLP oracle adds the classical constants `[2^i]P` and `[2^i]Q` into a quantum point
accumulator.  This module supplies the circuit-independent table boundary: a fixed-length list,
its exact indexed value, and the recurrence checked between adjacent entries.  The construction is
generic over an additive monoid so the later secp256k1 point type can instantiate it directly.

There are deliberately no circuits, wires, register layouts, or point encodings here.  Those belong
to `PointAdd`; this file only verifies the classical constants that the eventual circuit indexes.
-/

namespace ShorECDLP
namespace Precompute

variable {G : Type*} [AddMonoid G]

/-- The `width` classical constants `[2^i]base`, in LSB-first order. -/
def doublingTable (width : Nat) (base : G) : List G :=
  List.ofFn fun i : Fin width => (2 ^ (i : Nat)) • base

/-- A doubling table has exactly the requested number of entries. -/
@[simp]
theorem doublingTable_length (width : Nat) (base : G) :
    (doublingTable width base).length = width := by
  simp [doublingTable]

/-- Reading an entry with a `Fin` index returns the corresponding power-of-two multiple. -/
@[simp]
theorem doublingTable_get (width : Nat) (base : G)
    (i : Fin (doublingTable width base).length) :
    (doublingTable width base).get i = (2 ^ (i : Nat)) • base := by
  simp [doublingTable]

/-- Natural-number indexing exposes the same `[2^i]base` specification. -/
@[simp]
theorem doublingTable_getElem (width : Nat) (base : G) {i : Nat} (hi : i < width) :
    (doublingTable width base)[i]'(by
      rw [doublingTable_length]
      exact hi) = (2 ^ i) • base := by
  simp [doublingTable]

/-- Each entry after the first is the group double of the preceding entry. -/
theorem doublingTable_adjacent (width : Nat) (base : G) {i : Nat} (hi : i + 1 < width) :
    (doublingTable width base)[i + 1]'(by
      rw [doublingTable_length]
      exact hi) =
      (doublingTable width base)[i]'(by
          rw [doublingTable_length]
          omega) +
        (doublingTable width base)[i]'(by
          rw [doublingTable_length]
          omega) := by
  rw [doublingTable_getElem width base hi]
  rw [doublingTable_getElem width base (by omega)]
  rw [Nat.pow_succ, Nat.mul_two, add_nsmul]

end Precompute
end ShorECDLP
