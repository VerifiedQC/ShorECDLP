import ShorECDLP.Submission.Arithmetic.Adder

/-
# Reversible n-bit ripple-carry adder (M1.2)

Chains `fullAdder` cells, threading the carry: column `i` takes carry-in from column `i-1`
and produces the carry-out consumed by column `i+1`. Built over `{X, CX, CCX}`, correctness
proved against the classical basis-state semantics.
-/

namespace ShorECDLP

open Classical

/-- `fullAdder` writes only to its two output wires `s` and `co`; every other wire is left
unchanged. This is what lets the ripple carry preserve already-computed sum bits and the
inputs of later columns. -/
theorem fullAdder_other (a b cin s co : Nat) (st : BasisState) {w : Nat}
    (ws : w ≠ s) (wc : w ≠ co) :
    ⟪fullAdder a b cin s co⟫ st w = st w := by
  simp only [fullAdder, run_cons, run_nil, applyGate,
    upd_other _ _ _ ws, upd_other _ _ _ wc]

/-- Ripple-carry adder over aligned columns. `cols` is a list of `(aᵢ, bᵢ, sumᵢ)` triples
(LSB-first); `cin` is the incoming carry wire; `couts` supplies each column's carry-out wire
(column `i`'s carry-out is column `i+1`'s carry-in). -/
def ripple : List (Nat × Nat × Nat) → Nat → List Nat → Circuit
  | [],             _,   _            => []
  | (a, b, s) :: cols, cin, co :: couts => fullAdder a b cin s co ++ ripple cols co couts
  | _ :: _,         _,   []           => []

/-- The ripple adder costs `21` T per column (one full-adder each), when there is a carry-out
wire for every column. -/
theorem ripple_tCount :
    ∀ (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat),
      couts.length = cols.length → tCount (ripple cols cin couts) = 21 * cols.length
  | [],             _,   _,            _ => by simp [ripple]
  | (a, b, s) :: cols, cin, co :: couts, h => by
      have h' : couts.length = cols.length := by
        simpa [List.length_cons, Nat.succ_inj] using h
      rw [ripple, tCount_append, fullAdder_tCount, ripple_tCount cols co couts h']
      simp [List.length_cons, Nat.mul_succ, Nat.add_comm]
  | (_ :: _),       _,   [],           h => by simp at h

end ShorECDLP
