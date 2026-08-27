import ShorECDLP.Framework.Quantum.InnerProduct

/-!
# Joint-register measurement

This file contains only the Born-rule semantics for measuring two named
registers.  It does not define order finding, classical postprocessing,
repetition, or a submission contract.
-/

namespace ShorECDLP.Quantum.OrderFinding

open scoped BigOperators

noncomputable section

/-- Born probability of measuring the two named registers as `(a,b)`. -/
def jointRegisterProbability
    (aReg bReg : List Wire)
    (a b : Nat)
    (psi : State) : Real := by
  classical
  exact
    ∑ s ∈ psi.support,
      if regValue aReg s = a ∧ regValue bReg s = b
      then Complex.normSq (psi s)
      else 0

private theorem regValue_lt_two_pow
    (ws : List Wire) (s : BasisState) :
    regValue ws s < 2 ^ ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      rw [regValue_cons, List.length_cons, Nat.pow_succ]
      by_cases h : s w <;> simp [h] <;> omega

private theorem normSq_eq_support_sum (psi : State) :
    normSq psi = ∑ s ∈ psi.support, Complex.normSq (psi s) := by
  classical
  have hinner :
      inner psi psi =
        ((∑ s ∈ psi.support, Complex.normSq (psi s) : Real) : Complex) := by
    unfold inner
    change
      (∑ s ∈ psi.support,
        (starRingEnd Complex) (psi s) * psi s) =
      ((∑ s ∈ psi.support, Complex.normSq (psi s) : Real) : Complex)
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    exact (Complex.normSq_eq_conj_mul_self).symm
  unfold normSq
  rw [hinner]
  simp

/-- Summing all two-register outcomes gives the state's total Born mass. -/
theorem jointRegisterProbability_sum_eq_normSq
    (aReg bReg : List Wire)
    (precision : Nat)
    (ha : aReg.length = precision)
    (hb : bReg.length = precision)
    (psi : State) :
    (∑ a : Fin (2 ^ precision),
      ∑ b : Fin (2 ^ precision),
        jointRegisterProbability aReg bReg a.val b.val psi) = normSq psi := by
  classical
  rw [normSq_eq_support_sum]
  unfold jointRegisterProbability
  calc
    (∑ a : Fin (2 ^ precision),
        ∑ b : Fin (2 ^ precision),
          ∑ s ∈ psi.support,
            if regValue aReg s = a.val ∧ regValue bReg s = b.val
            then Complex.normSq (psi s) else 0) =
      ∑ a : Fin (2 ^ precision),
        ∑ s ∈ psi.support,
          ∑ b : Fin (2 ^ precision),
            if regValue aReg s = a.val ∧ regValue bReg s = b.val
            then Complex.normSq (psi s) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ s ∈ psi.support,
        ∑ a : Fin (2 ^ precision),
          ∑ b : Fin (2 ^ precision),
            if regValue aReg s = a.val ∧ regValue bReg s = b.val
            then Complex.normSq (psi s) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s ∈ psi.support, Complex.normSq (psi s) := by
      apply Finset.sum_congr rfl
      intro s _
      let a : Fin (2 ^ precision) :=
        ⟨regValue aReg s,
          by simpa [ha] using regValue_lt_two_pow aReg s⟩
      let b : Fin (2 ^ precision) :=
        ⟨regValue bReg s,
          by simpa [hb] using regValue_lt_two_pow bReg s⟩
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp [a, b]
        · intro b' _ hne
          have hbval : regValue bReg s ≠ b'.val := by
            intro h
            exact hne (Fin.ext h.symm)
          simp [hbval]
        · simp
      · intro a' _ hne
        have haval : regValue aReg s ≠ a'.val := by
          intro h
          exact hne (Fin.ext h.symm)
        simp [haval]
      · simp

/-- A joint-register Born probability is nonnegative. -/
theorem jointRegisterProbability_nonneg
    (aReg bReg : List Wire) (a b : Nat) (psi : State) :
    0 ≤ jointRegisterProbability aReg bReg a b psi := by
  classical
  unfold jointRegisterProbability
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

end

end ShorECDLP.Quantum.OrderFinding
