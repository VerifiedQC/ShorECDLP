import ShorECDLP.Submission.Naive.QFT.Defs
import ShorECDLP.Framework.CostModel

namespace ShorECDLP.Quantum

/-! ============================================================
    SWAP correctness
============================================================ -/

/--
Correctness of the standard three-CNOT SWAP circuit.

For distinct wires `a` and `b`,

    CX a b;
    CX b a;
    CX a b

exchanges the values stored on `a` and `b` and leaves every other
wire unchanged.
-/
theorem run_swap_ket
    (a b : Wire)
    (s : BasisState)
    (hab : a ≠ b) :
    run (swap a b) (ket s)
      =
    ket ((s[a ↦ s b])[b ↦ s a]) := by

  have hba : b ≠ a :=
    Ne.symm hab
  let s₁ : BasisState :=
    s[b ↦ Bool.xor (s b) (s a)]

  let s₂ : BasisState :=
    s₁[a ↦ Bool.xor (s₁ a) (s₁ b)]

  let s₃ : BasisState :=
    s₂[b ↦ Bool.xor (s₂ b) (s₂ a)]

  /- First CNOT. -/
  have hfirst :
      applyGate (.CX a b) (ket s) =
        ket s₁ := by
    rw [applyGate_CX_ket]

  /- Second CNOT. -/
  have hsecond :
      applyGate (.CX b a) (ket s₁) =
        ket s₂ := by
    rw [applyGate_CX_ket]

  /- Third CNOT. -/
  have hthird :
      applyGate (.CX a b) (ket s₂) =
        ket s₃ := by
    rw [applyGate_CX_ket]

  have hswap : s₃ = (s[a ↦ s b])[b ↦ s a] := by
    funext i
    by_cases hia : i = a
    · subst i
      cases ha : s a <;>
        cases hb : s b <;>
        simp [ s₃,s₂,s₁,upd,hab,hba,ha,hb]

    · by_cases hib : i = b
      · subst i
        cases ha : s a <;>
          cases hb : s b <;>
          simp [ s₃,s₂,s₁,upd,hab,hba,ha,hb]

      · simp [ s₃,s₂,s₁,upd, hia, hib, hab, hba]

  /- Compose the three primitive CNOTs. -/
  change
    applyGate (.CX a b)
      (applyGate (.CX b a)
        (applyGate (.CX a b) (ket s)))
      =
    ket ((s[a ↦ s b])[b ↦ s a])

  rw [hfirst]
  rw [hsecond]
  rw [hthird]
  rw [hswap]


/-! ============================================================
    Useful consequences
============================================================ -/

/--
After SWAP, wire `a` contains the old value of wire `b`.
-/
theorem swap_result_left
    (a b : Wire)
    (s : BasisState)
    (hab : a ≠ b) :
    ((s[a ↦ s b])[b ↦ s a]) a =
      s b := by
  simp [upd, hab]


/--
After SWAP, wire `b` contains the old value of wire `a`.
-/
theorem swap_result_right
    (a b : Wire)
    (s : BasisState) :
    ((s[a ↦ s b])[b ↦ s a]) b =
      s a := by
  simp [upd]


/--
SWAP leaves every wire other than `a` and `b` unchanged.
-/
theorem swap_result_other
    (a b i : Wire)
    (s : BasisState)
    (hia : i ≠ a)
    (hib : i ≠ b) :
    ((s[a ↦ s b])[b ↦ s a]) i =
      s i := by
  simp [upd, hia, hib]


/-! ============================================================
    Well-formedness
============================================================ -/

/--
The three-CNOT SWAP circuit is well-formed whenever the two wires
are distinct.
-/
theorem swap_wellFormed
    (a b : Wire)
    (hab : a ≠ b) :
    CircuitWellFormed (swap a b) := by

  have hba : b ≠ a :=
    Ne.symm hab

  simp [
    swap,
    CircuitWellFormed,
    Gate.WellFormed,
    hab,
    hba
  ]


/-! ============================================================
    Unitarity / norm preservation
============================================================ -/

/--
A well-formed SWAP preserves the quantum inner product.
-/
theorem swap_preservesInner
    (a b : Wire)
    (hab : a ≠ b) :
    PreservesInner (run (swap a b)) := by
  exact
    run_preservesInner
      (swap a b)
      (swap_wellFormed a b hab)


/--
A well-formed SWAP preserves squared norm / total Born mass.
-/
theorem swap_preservesNormSq
    (a b : Wire)
    (hab : a ≠ b) :
    PreservesNormSq (run (swap a b)) := by
  exact
    run_preservesNormSq
      (swap a b)
      (swap_wellFormed a b hab)


/-! ============================================================
    T-count
============================================================ -/

/--
SWAP has zero T-count in the baseline model:

    CX + CX + CX
      = 0 + 0 + 0
      = 0.

All three constituent gates are Clifford gates.
-/
@[simp]
theorem tCount_swap
    (a b : Wire) :
    tCount (swap a b) = 0 := by
  rfl


end ShorECDLP.Quantum
