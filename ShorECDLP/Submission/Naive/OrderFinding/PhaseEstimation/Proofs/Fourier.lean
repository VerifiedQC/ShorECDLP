import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Proofs.Eigenphase
import ShorECDLP.Submission.Naive.QFT.Main
import Mathlib.Analysis.Fourier.ZMod

namespace ShorECDLP.Quantum.PhaseEstimation

open scoped BigOperators

private theorem writeReg_eq_setReg
    (r : List Wire) (y : Nat) (s : BasisState) :
    writeReg r y s = setReg r y s := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [writeReg, setReg]
      have hbit : y.testBit 0 = (y % 2 == 1) := by
        rw [Nat.testBit_zero]
        by_cases h : y % 2 = 1 <;> simp [h]
      rw [hbit]
      exact ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)])

private theorem setReg_not_mem
    (r : List Wire) (y : Nat) (s : BasisState)
    {i : Wire} (hi : i ∉ r) :
    setReg r y s i = s i := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [setReg]
      rw [ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)]) hi.2]
      exact upd_other s w _ hi.1

private theorem upd_comm
    (s : BasisState) (i j : Wire) (bi bj : Bool)
    (h : i ≠ j) :
    (s[i ↦ bi])[j ↦ bj] = (s[j ↦ bj])[i ↦ bi] := by
  funext x
  by_cases hxi : x = i
  · subst x
    simp [upd, h]
  · by_cases hxj : x = j
    · subst x
      simp [upd, Ne.symm h]
    · simp [upd, hxi, hxj]

private theorem setReg_upd_not_mem
    (r : List Wire) (y : Nat) (s : BasisState)
    (i : Wire) (b : Bool) (hi : i ∉ r) :
    setReg r y s[i ↦ b] = (setReg r y s)[i ↦ b] := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [setReg]
      rw [upd_comm s i w b (y % 2 == 1) hi.1]
      exact ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)]) hi.2

private theorem setReg_overwrite
    (r : List Wire) (x y : Nat) (s : BasisState)
    (hnd : r.Nodup) :
    setReg r y (setReg r x s) = setReg r y s := by
  induction r generalizing x y s with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.mp hnd).1
      have hws : ws.Nodup := (List.nodup_cons.mp hnd).2
      simp only [setReg]
      rw [← setReg_upd_not_mem ws (x / 2) (s[w ↦ (x % 2 == 1)])
        w (y % 2 == 1) hw]
      rw [ih (x := x / 2) (y := y / 2)
        (s := (s[w ↦ (x % 2 == 1)])[w ↦ (y % 2 == 1)]) hws]
      congr 1
      funext i
      by_cases hi : i = w
      · simp [upd, hi]
      · simp [upd, hi]


private theorem regValue_setReg_of_lt
    (r : List Wire) (y : Nat) (s : BasisState)
    (hnd : r.Nodup)
    (hy : y < 2 ^ r.length) :
    regValue r (setReg r y s) = y := by
  induction r generalizing y s with
  | nil =>
      simp only [List.length_nil, pow_zero] at hy
      have : y = 0 := by omega
      subst y
      rfl
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.mp hnd).1
      have hws : ws.Nodup := (List.nodup_cons.mp hnd).2
      have hpow : 2 ^ (w :: ws).length = 2 * 2 ^ ws.length := by
        simp [pow_succ, Nat.mul_comm]
      have hy' : y / 2 < 2 ^ ws.length := by
        rw [hpow] at hy
        omega
      simp only [setReg]
      rw [regValue_cons]
      rw [setReg_not_mem ws (y / 2) (s[w ↦ (y % 2 == 1)]) hw]
      rw [upd_same]
      rw [ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)]) hws hy']
      have hmod : y % 2 < 2 := Nat.mod_lt _ (by omega)
      have hdiv := Nat.mod_add_div y 2
      by_cases hodd : y % 2 = 1
      · simp [hodd]
        omega
      · have heven : y % 2 = 0 := by omega
        simp [heven]
        omega

private theorem labelState_ket
    (phaseReg : List Wire)
    (value : Nat)
    (s : BasisState) :
    labelState phaseReg value (ket s) =
      ket (setReg phaseReg value s) := by
  classical
  simp [labelState, ket, writeReg_eq_setReg]

private theorem run_qft_labelState_ket
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (value : Fin (2 ^ phaseReg.length))
    (hancilla : qftAncilla ∉ phaseReg)
    (hphaseReg : phaseReg.Nodup)
    (hancillaZero : s qftAncilla = false) :
    run (qft phaseReg qftAncilla)
        (labelState phaseReg value.val (ket s)) =
      (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
        ∑ y ∈ Finset.range (2 ^ phaseReg.length),
          qftPhase (2 ^ phaseReg.length) value.val y •
            labelState phaseReg y (ket s) := by
  rw [labelState_ket]
  have hanc :
      setReg phaseReg value.val s qftAncilla = false := by
    rw [setReg_not_mem phaseReg value.val s hancilla]
    exact hancillaZero
  rw [qft_correct phaseReg qftAncilla
    (setReg phaseReg value.val s) hancilla hphaseReg hanc]
  rw [regValue_setReg_of_lt phaseReg value.val s hphaseReg value.isLt]
  apply congrArg
    (fun φ : State =>
      (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) • φ)
  apply Finset.sum_congr rfl
  intro y _
  rw [setReg_overwrite phaseReg value.val y s hphaseReg]
  rw [labelState_ket]

theorem run_qft_labelState
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (psi : State)
    (value : Fin (2 ^ phaseReg.length))
    (hancillaZero : ∀ s, psi s ≠ 0 → s qftAncilla = false)
    (hancilla : qftAncilla ∉ phaseReg)
    (hphaseReg : phaseReg.Nodup) :
    run (qft phaseReg qftAncilla)
        (labelState phaseReg value.val psi) =
      (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
        ∑ y ∈ Finset.range (2 ^ phaseReg.length),
          qftPhase (2 ^ phaseReg.length) value.val y •
            labelState phaseReg y psi := by
  classical
  let T : State →ₗ[ℂ] State :=
    (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
      ∑ y ∈ Finset.range (2 ^ phaseReg.length),
        qftPhase (2 ^ phaseReg.length) value.val y •
          labelState phaseReg y
  have hrepr : Finsupp.linearCombination ℂ ket psi = psi := by
    ext s
    simp [Finsupp.linearCombination_apply, ket]
  have h :
      ((run (qft phaseReg qftAncilla)).comp
        (labelState phaseReg value.val)) psi = T psi := by
    rw [← hrepr]
    rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum,
      Function.comp_apply]
    apply Finset.sum_congr rfl
    intro s hs
    apply congrArg (fun φ : State => psi s • φ)
    have hsanc : s qftAncilla = false :=
      hancillaZero s (Finsupp.mem_support_iff.mp hs)
    simpa [T] using
      run_qft_labelState_ket phaseReg qftAncilla s value
        hancilla hphaseReg hsanc
  simpa [T] using h

theorem exact_phase_state_eq_run_qft
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (psi : State)
    (value : Fin (2 ^ phaseReg.length))
    (hancillaZero : ∀ s, psi s ≠ 0 → s qftAncilla = false)
    (hancilla : qftAncilla ∉ phaseReg)
    (hphaseReg : phaseReg.Nodup) :
    (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
        ∑ y ∈ Finset.range (2 ^ phaseReg.length),
          eigenvalue
              ((value.val : ℝ) / (2 ^ phaseReg.length : Nat)) ^ y •
            labelState phaseReg y psi =
      run (qft phaseReg qftAncilla)
        (labelState phaseReg value.val psi) := by
  rw [run_qft_labelState phaseReg qftAncilla psi value
    hancillaZero hancilla hphaseReg]
  apply congrArg
    (fun φ : State =>
      (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) • φ)
  apply Finset.sum_congr rfl
  intro y _
  rw [eigenvalue_exact_pow_eq_qftPhase phaseReg.length value.val y]

noncomputable def qpeAmplitude
    (precision : Nat)
    (phase : ℝ)
    (value : Nat) : ℂ :=
  (((2 ^ precision : Nat) : ℂ)⁻¹) *
    ∑ y ∈ Finset.range (2 ^ precision),
      eigenvalue
        (phase - (value : ℝ) / (2 ^ precision : Nat)) ^ y

private theorem zmod_sum_univ_eq_sum_range
    {n : Nat} [NeZero n] {α : Type*} [AddCommMonoid α]
    (f : ZMod n → α) :
    ∑ i : ZMod n, f i = ∑ i ∈ Finset.range n, f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  cases n with
  | zero => exact (neZero_zero_iff_false.mp ‹NeZero 0›).elim
  | succ n => simp [ZMod]

theorem qpeAmplitude_fourier_inversion
    (precision : Nat)
    (phase : ℝ)
    (y : Fin (2 ^ precision)) :
    ∑ z ∈ Finset.range (2 ^ precision),
        qpeAmplitude precision phase z * qftPhase (2 ^ precision) z y.val =
      eigenvalue phase ^ y.val := by
  letI : NeZero (2 ^ precision) := ⟨by positivity⟩
  let Φ : ZMod (2 ^ precision) → ℂ :=
    fun k => eigenvalue phase ^ k.val
  have hqpe (z : Nat) (hz : z < 2 ^ precision) :
      qpeAmplitude precision phase z =
        (((2 ^ precision : Nat) : ℂ)⁻¹) *
          ZMod.dft Φ (z : ZMod (2 ^ precision)) := by
    unfold qpeAmplitude
    rw [ZMod.dft_apply, zmod_sum_univ_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < 2 ^ precision := Finset.mem_range.mp hk
    simp only [Φ, ZMod.val_natCast_of_lt hklt, smul_eq_mul]
    have hcast :
        -((k : ZMod (2 ^ precision)) * (z : ZMod (2 ^ precision))) =
          ((-((k : ℤ) * (z : ℤ)) : ℤ) : ZMod (2 ^ precision)) := by
      push_cast
      rfl
    rw [hcast, ZMod.stdAddChar_coe]
    unfold eigenvalue
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hphase (z : Nat) :
      qftPhase (2 ^ precision) z y.val =
        ZMod.stdAddChar
          ((z : ZMod (2 ^ precision)) *
            (y.val : ZMod (2 ^ precision))) := by
    have hcast :
        (z : ZMod (2 ^ precision)) *
            (y.val : ZMod (2 ^ precision)) =
          (((z : ℤ) * (y.val : ℤ) : ℤ) :
            ZMod (2 ^ precision)) := by
      push_cast
      rfl
    rw [hcast, ZMod.stdAddChar_coe]
    unfold qftPhase
    congr 1
    push_cast
    field_simp
  calc
    ∑ z ∈ Finset.range (2 ^ precision),
        qpeAmplitude precision phase z *
          qftPhase (2 ^ precision) z y.val =
      ∑ z ∈ Finset.range (2 ^ precision),
        ((((2 ^ precision : Nat) : ℂ)⁻¹) *
            ZMod.dft Φ (z : ZMod (2 ^ precision))) *
          ZMod.stdAddChar
            ((z : ZMod (2 ^ precision)) *
              (y.val : ZMod (2 ^ precision))) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hqpe z (Finset.mem_range.mp hz), hphase z]
    _ =
      ∑ z : ZMod (2 ^ precision),
        ((((2 ^ precision : Nat) : ℂ)⁻¹) *
            ZMod.dft Φ z) *
          ZMod.stdAddChar
            (z * (y.val : ZMod (2 ^ precision))) := by
        symm
        exact zmod_sum_univ_eq_sum_range
          (fun z : ZMod (2 ^ precision) =>
            ((((2 ^ precision : Nat) : ℂ)⁻¹) *
                ZMod.dft Φ z) *
              ZMod.stdAddChar
                (z * (y.val : ZMod (2 ^ precision))))
    _ =
      (ZMod.dft.symm (ZMod.dft Φ))
        (y.val : ZMod (2 ^ precision)) := by
        rw [ZMod.invDFT_apply]
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
    _ = Φ (y.val : ZMod (2 ^ precision)) := by
      simp
    _ = eigenvalue phase ^ y.val := by
      dsimp [Φ]
      rw [ZMod.val_natCast_of_lt y.isLt]

private theorem sum_smul_fourier_swap
    {α β : Type*}
    (s : Finset α)
    (t : Finset β)
    (a : α → ℂ)
    (b : α → β → ℂ)
    (c : ℂ)
    (v : β → State) :
    (∑ i ∈ s,
        a i •
          (c • ∑ j ∈ t, b i j • v j)) =
      c • ∑ j ∈ t,
        (∑ i ∈ s, a i * b i j) • v j := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ t,
        (a i * c * b i j) • v j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_smul, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [smul_smul]
    _ = ∑ j ∈ t, ∑ i ∈ s,
        (a i * c * b i j) • v j := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ t, ∑ i ∈ s,
        (c * (a i * b i j)) • v j := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          ring
    _ = c • ∑ j ∈ t,
        (∑ i ∈ s, a i * b i j) • v j := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [smul_smul, Finset.mul_sum, Finset.sum_smul]

theorem run_iqft_kicked_phase_state
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (psi : State)
    (phase : ℝ)
    (hancillaZero : ∀ s, psi s ≠ 0 → s qftAncilla = false)
    (hancilla : qftAncilla ∉ phaseReg)
    (hphaseReg : phaseReg.Nodup) :
    run (iqft phaseReg qftAncilla)
        ((((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ) •
          ∑ y ∈ Finset.range (2 ^ phaseReg.length),
            eigenvalue phase ^ y •
              labelState phaseReg y psi) =
      ∑ z ∈ Finset.range (2 ^ phaseReg.length),
        qpeAmplitude phaseReg.length phase z •
          labelState phaseReg z psi := by
  let c : ℂ :=
    (((Real.sqrt (2 ^ phaseReg.length))⁻¹ : ℝ) : ℂ)
  let output : State :=
    ∑ z ∈ Finset.range (2 ^ phaseReg.length),
      qpeAmplitude phaseReg.length phase z •
        labelState phaseReg z psi
  let kicked : State :=
    c • ∑ y ∈ Finset.range (2 ^ phaseReg.length),
      eigenvalue phase ^ y • labelState phaseReg y psi
  have hqft :
      run (qft phaseReg qftAncilla) output = kicked := by
    dsimp [output, kicked]
    calc
      run (qft phaseReg qftAncilla)
          (∑ z ∈ Finset.range (2 ^ phaseReg.length),
            qpeAmplitude phaseReg.length phase z •
              labelState phaseReg z psi) =
        ∑ z ∈ Finset.range (2 ^ phaseReg.length),
          qpeAmplitude phaseReg.length phase z •
            run (qft phaseReg qftAncilla)
              (labelState phaseReg z psi) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro z _
          rw [map_smul]
      _ =
        ∑ z ∈ Finset.range (2 ^ phaseReg.length),
          qpeAmplitude phaseReg.length phase z •
            (c •
              ∑ y ∈ Finset.range (2 ^ phaseReg.length),
                qftPhase (2 ^ phaseReg.length) z y •
                  labelState phaseReg y psi) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [run_qft_labelState phaseReg qftAncilla psi
            ⟨z, Finset.mem_range.mp hz⟩
            hancillaZero hancilla hphaseReg]
      _ =
        c •
          ∑ y ∈ Finset.range (2 ^ phaseReg.length),
            (∑ z ∈ Finset.range (2 ^ phaseReg.length),
              qpeAmplitude phaseReg.length phase z *
                qftPhase (2 ^ phaseReg.length) z y) •
              labelState phaseReg y psi := by
          exact sum_smul_fourier_swap
            (Finset.range (2 ^ phaseReg.length))
            (Finset.range (2 ^ phaseReg.length))
            (qpeAmplitude phaseReg.length phase)
            (fun z y =>
              qftPhase (2 ^ phaseReg.length) z y)
            c
            (fun y => labelState phaseReg y psi)
      _ =
        c •
          ∑ y ∈ Finset.range (2 ^ phaseReg.length),
            eigenvalue phase ^ y •
              labelState phaseReg y psi := by
          apply congrArg (fun φ : State => c • φ)
          apply Finset.sum_congr rfl
          intro y hy
          rw [qpeAmplitude_fourier_inversion
            phaseReg.length phase
            ⟨y, Finset.mem_range.mp hy⟩]
  change
    run (iqft phaseReg qftAncilla) kicked = output
  rw [← hqft]
  exact iqft_qft_cancel phaseReg qftAncilla output
    hancilla hphaseReg

end ShorECDLP.Quantum.PhaseEstimation
