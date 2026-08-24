import ShorECDLP.Submission.QFT.Defs
import ShorECDLP.Framework.CostModel

namespace ShorECDLP.Quantum

noncomputable section

/-! ============================================================
    Controlled phase correctness
============================================================ -/

/--
Correctness of `cPhase` on a computational-basis state.

If the ancilla starts clean (`s anc = false`) and is distinct from
the two data wires, then

    CCX c t anc;
    P forward k anc;
    CCX c t anc

has no effect on the computational basis state itself.  Its only
effect is multiplication by the forward `phase k` exactly when both `c` and `t`
are set.

The fact that the result contains `ket s` also says that the ancilla
has been restored to its original clean value.
-/
theorem run_cPhase_ket
    (k : Nat)
    (c t anc : Wire)
    (s : BasisState)
    (hca : c ≠ anc)
    (hta : t ≠ anc)
    (hanc : s anc = false) :
    run (cPhase k c t anc) (ket s)
      =
    (if s c && s t then
      Complex.exp (Complex.I * (2 * Real.pi / (2 : ℝ) ^ k : ℂ))
      else 1) • ket s := by

  --`bit` is the value computed into the clean ancilla by the first Toffoli.
  let bit : Bool := s c && s t
  --State after the first Toffoli. Since the ancilla begins at zero, it now stores `c ∧ t`.
  let s₁ : BasisState := s[anc ↦ bit]
  have hac : anc ≠ c := Ne.symm hca
  have hat : anc ≠ t := Ne.symm hta

  --Step 1: compute c ∧ t into the ancilla
  have hfirst : applyGate (.CCX c t anc) (ket s) = ket s₁ := by
    rw [applyGate_CCX_ket]
    have hx : Bool.xor (s anc) (s c && s t) = bit := by
      simp [hanc, bit]
    rw [hx]

  --Values of the relevant wires in the intermediate state.
  have hs₁anc : s₁ anc = bit := by
    simp [s₁]

  have hs₁c : s₁ c = s c := by
    simp [s₁, upd, hca]

  have hs₁t : s₁ t = s t := by
    simp [s₁, upd, hta]

  --Step 2: apply the phase to the computed AND bit
  have hphase :
      applyGate (.P .forward k anc) (ket s₁)
        =
      (if bit then
        Complex.exp (Complex.I * (2 * Real.pi / (2 : ℝ) ^ k : ℂ))
        else 1) • ket s₁ := by
    rw [applyGate_P_ket]
    rw [hs₁anc]
    simp [phaseCoeff, phaseAngle]

  --Step 3: uncompute the ancilla
  have hxor :
      Bool.xor
          (s₁ anc)
          (s₁ c && s₁ t)
        =
      false := by
    rw [hs₁anc, hs₁c, hs₁t]
    simp [bit]

  --Once the second Toffoli writes `false` back into the ancilla,
  --the entire basis state is exactly the original state `s`.
  have hrestore : s₁[anc ↦ false] = s := by
    funext i
    by_cases hi : i = anc
    · subst i
      simp [s₁, hanc]
    · simp [s₁, upd, hi]
  have hlast : applyGate (.CCX c t anc) (ket s₁) = ket s := by
    rw [applyGate_CCX_ket]
    rw [hxor]
    rw [hrestore]
  --Compose the three primitive gates
  simp only [cPhase, run_cons]
  rw [hfirst]
  rw [hphase]
  --The last CCX acts through the scalar by linearity.
  rw [applyGate_smul]
  rw [hlast]
  rfl


/-! ============================================================
    Well-formedness
============================================================ -/

/--
`cPhase` is a well-formed physical circuit when `c`, `t`, and `anc`
are pairwise distinct.
-/
theorem cPhase_wellFormed
    (k : Nat)
    (c t anc : Wire)
    (hct : c ≠ t)
    (hca : c ≠ anc)
    (hta : t ≠ anc) :
    CircuitWellFormed (cPhase k c t anc) := by
  simp [
    cPhase,
    CircuitWellFormed,
    Gate.WellFormed,
    hct,
    hca,
    hta
  ]


/-! ============================================================
    Unitarity / norm preservation
============================================================ -/

/--
A well-formed `cPhase` preserves the inner product.
-/
theorem cPhase_preservesInner
    (k : Nat)
    (c t anc : Wire)
    (hct : c ≠ t)
    (hca : c ≠ anc)
    (hta : t ≠ anc) :
    PreservesInner (run (cPhase k c t anc)) := by
  exact
    run_preservesInner
      (cPhase k c t anc)
      (cPhase_wellFormed k c t anc hct hca hta)


/--
A well-formed `cPhase` preserves total squared norm / Born mass.
-/
theorem cPhase_preservesNormSq
    (k : Nat)
    (c t anc : Wire)
    (hct : c ≠ t)
    (hca : c ≠ anc)
    (hta : t ≠ anc) :
    PreservesNormSq (run (cPhase k c t anc)) := by
  exact
    run_preservesNormSq
      (cPhase k c t anc)
      (cPhase_wellFormed k c t anc hct hca hta)


/-! ============================================================
    Cost
============================================================ -/

/--
A controlled phase costs

    CCX + P + CCX
      = 7 + 1 + 7
      = 15 T gates

in the baseline cost model.
-/
@[simp]
theorem tCount_cPhase
    (k : Nat)
    (c t anc : Wire) :
    tCount (cPhase k c t anc) = 15 := by
  rfl


end

end ShorECDLP.Quantum
