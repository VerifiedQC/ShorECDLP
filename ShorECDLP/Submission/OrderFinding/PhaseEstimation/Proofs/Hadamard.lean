import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Defs

namespace ShorECDLP.Quantum.PhaseEstimation

open scoped BigOperators

noncomputable section

private noncomputable def hadamardNorm (n : Nat) : ℂ :=
  (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ) : ℂ)

private theorem hadamardNorm_succ (n : Nat) :
    hadamardNorm (n + 1) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * hadamardNorm n := by
  unfold hadamardNorm
  norm_cast
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by
    rw [pow_succ']
  simp [hpow]
  field_simp

private theorem sum_range_double_even_odd
    {α : Type*} [AddCommMonoid α]
    (f : Nat → α) (n : Nat) :
    ∑ y ∈ Finset.range (2 * n), f y =
      ∑ y ∈ Finset.range n, (f (2 * y) + f (2 * y + 1)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.mul_succ]
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      ac_rfl

private theorem writeReg_cons_even
    (w : Wire) (ws : List Wire) (y : Nat) (s : BasisState) :
    writeReg (w :: ws) (2 * y) s =
      writeReg ws y (s[w ↦ false]) := by
  simp only [writeReg]
  have hdiv : 2 * y / 2 = y := by omega
  have hmod : 2 * y % 2 = 0 := by omega
  rw [hdiv, Nat.testBit_zero, hmod]
  simp

private theorem writeReg_cons_odd
    (w : Wire) (ws : List Wire) (y : Nat) (s : BasisState) :
    writeReg (w :: ws) (2 * y + 1) s =
      writeReg ws y (s[w ↦ true]) := by
  simp only [writeReg]
  have hdiv : (2 * y + 1) / 2 = y := by omega
  have hmod : (2 * y + 1) % 2 = 1 := by omega
  rw [hdiv, Nat.testBit_zero, hmod]
  simp

private theorem writeRegSum_cons
    (w : Wire) (ws : List Wire) (s : BasisState) :
    (∑ y ∈ Finset.range (2 ^ (w :: ws).length),
        ket (writeReg (w :: ws) y s)) =
      (∑ y ∈ Finset.range (2 ^ ws.length),
        ket (writeReg ws y (s[w ↦ false]))) +
      (∑ y ∈ Finset.range (2 ^ ws.length),
        ket (writeReg ws y (s[w ↦ true]))) := by
  let f : Nat → State := fun y => ket (writeReg (w :: ws) y s)
  change (∑ y ∈ Finset.range (2 ^ (w :: ws).length), f y) = _
  have h := sum_range_double_even_odd f (2 ^ ws.length)
  rw [show
    (∑ y ∈ Finset.range (2 ^ (w :: ws).length), f y) =
      ∑ y ∈ Finset.range (2 ^ ws.length),
        (f (2 * y) + f (2 * y + 1)) by
          simpa [pow_succ, Nat.mul_comm] using h]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro y _
    dsimp [f]
    rw [writeReg_cons_even]
  · apply Finset.sum_congr rfl
    intro y _
    dsimp [f]
    rw [writeReg_cons_odd]

@[simp]
theorem labelState_ket
    (phaseReg : List Wire)
    (value : Nat)
    (s : BasisState) :
    labelState phaseReg value (ket s) =
      ket (writeReg phaseReg value s) := by
  classical
  simp [labelState, ket]

private theorem run_hadamards_ket_zero
    (phaseReg : List Wire)
    (s : BasisState)
    (hzero : regValue phaseReg s = 0)
    (hnd : phaseReg.Nodup) :
    run (hadamards phaseReg) (ket s) =
      hadamardNorm phaseReg.length •
        ∑ y ∈ Finset.range (2 ^ phaseReg.length),
          ket (writeReg phaseReg y s) := by
  induction phaseReg generalizing s with
  | nil =>
      simp [hadamards, hadamardNorm, writeReg]
  | cons w ws ih =>
      have hwmem : w ∉ ws := (List.nodup_cons.mp hnd).1
      have hnd' : ws.Nodup := (List.nodup_cons.mp hnd).2
      have hw : s w = false := by
        cases hsw : s w with
        | false =>
            rfl
        | true =>
            rw [regValue_cons, hsw] at hzero
            simp only [if_true] at hzero
            omega
      have hzero' : regValue ws s = 0 := by
        rw [regValue_cons, hw] at hzero
        omega
      have hsfalse : s[w ↦ false] = s := by
        funext i
        by_cases hi : i = w
        · subst i
          simp [hw]
        · simp [upd, hi]
      have hzeroTrue : regValue ws s[w ↦ true] = 0 := by
        rw [regValue_upd_not_mem ws s w true hwmem]
        exact hzero'
      change
        run (hadamards ws) (applyGate (.H w) (ket s)) =
          hadamardNorm (w :: ws).length •
            ∑ y ∈ Finset.range (2 ^ (w :: ws).length),
              ket (writeReg (w :: ws) y s)
      rw [applyGate_H_ket, hw]
      rw [hsfalse]
      rw [run_add, run_smul, run_smul]
      rw [ih s hzero' hnd']
      rw [ih (s[w ↦ true]) hzeroTrue hnd']
      rw [writeRegSum_cons]
      rw [hsfalse]
      have hnorm :
          hadamardNorm (w :: ws).length =
            (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * hadamardNorm ws.length := by
        simpa using hadamardNorm_succ ws.length
      rw [hnorm]
      simp [smul_add, smul_smul]

private theorem linearMap_apply_eq_of_eq_on_support
    (A B : State →ₗ[ℂ] State)
    (psi : State)
    (h : ∀ s ∈ psi.support, A (ket s) = B (ket s)) :
    A psi = B psi := by
  classical
  have hdecomp :
      (Finsupp.linearCombination ℂ ket) psi = psi := by
    rw [Finsupp.linearCombination_apply]
    simp [ket]
  rw [← hdecomp, Finsupp.linearCombination_apply]
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro s hs
  rw [A.map_smul, B.map_smul, h s hs]

theorem run_hadamards_clean
    (phaseReg : List Wire)
    (psi : State)
    (hphaseZero : ∀ s, psi s ≠ 0 → regValue phaseReg s = 0)
    (hphaseReg : phaseReg.Nodup) :
    run (hadamards phaseReg) psi =
      (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
        ∑ y ∈ Finset.range (2 ^ phaseReg.length),
          labelState phaseReg y psi := by
  classical
  let T : State →ₗ[ℂ] State :=
    (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
      ∑ y ∈ Finset.range (2 ^ phaseReg.length),
        labelState phaseReg y
  have h :
      run (hadamards phaseReg) psi = T psi := by
    apply linearMap_apply_eq_of_eq_on_support
    intro s hs
    have hs0 : regValue phaseReg s = 0 :=
      hphaseZero s (by simpa using hs)
    rw [run_hadamards_ket_zero phaseReg s hs0 hphaseReg]
    simp [T, hadamardNorm]
  simpa [T] using h

end

end ShorECDLP.Quantum.PhaseEstimation
