import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Defs

namespace ShorECDLP.Quantum.PhaseEstimation

open scoped BigOperators

noncomputable section

private theorem writeReg_not_mem
    (r : List Wire) (y : Nat) (s : BasisState)
    {i : Wire} (hi : i ∉ r) :
    writeReg r y s i = s i := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [writeReg]
      rw [ih (y := y / 2) (s := s[w ↦ y.testBit 0]) hi.2]
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

private theorem writeReg_upd_not_mem
    (r : List Wire) (y : Nat) (s : BasisState)
    (i : Wire) (b : Bool) (hi : i ∉ r) :
    writeReg r y s[i ↦ b] = (writeReg r y s)[i ↦ b] := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [writeReg]
      rw [upd_comm s i w b (y.testBit 0) hi.1]
      exact ih (y := y / 2) (s := s[w ↦ y.testBit 0]) hi.2

private theorem writeReg_overwrite
    (r : List Wire) (x y : Nat) (s : BasisState)
    (hnd : r.Nodup) :
    writeReg r y (writeReg r x s) = writeReg r y s := by
  induction r generalizing x y s with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.mp hnd).1
      have hws : ws.Nodup := (List.nodup_cons.mp hnd).2
      simp only [writeReg]
      rw [← writeReg_upd_not_mem ws (x / 2) (s[w ↦ x.testBit 0])
        w (y.testBit 0) hw]
      rw [ih (x := x / 2) (y := y / 2)
        (s := (s[w ↦ x.testBit 0])[w ↦ y.testBit 0]) hws]
      congr 1
      funext i
      by_cases hi : i = w
      · simp [upd, hi]
      · simp [upd, hi]

private theorem writeReg_zero_eq_of_regValue_zero
    (r : List Wire) (s : BasisState)
    (hzero : regValue r s = 0) :
    writeReg r 0 s = s := by
  induction r generalizing s with
  | nil => rfl
  | cons w ws ih =>
      have hw : s w = false := by
        cases hsw : s w with
        | false => rfl
        | true =>
            rw [regValue_cons, hsw] at hzero
            simp only [if_true] at hzero
            omega
      have hws : regValue ws s = 0 := by
        rw [regValue_cons, hw] at hzero
        omega
      have hupd : s[w ↦ false] = s := by
        funext i
        by_cases hi : i = w
        · subst i
          simp [hw]
        · simp [upd, hi]
      simp only [writeReg, Nat.zero_div, Nat.zero_testBit]
      rw [hupd]
      exact ih s hws

private theorem regValue_writeReg_of_lt
    (r : List Wire) (y : Nat) (s : BasisState)
    (hnd : r.Nodup)
    (hy : y < 2 ^ r.length) :
    regValue r (writeReg r y s) = y := by
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
      simp only [writeReg]
      rw [regValue_cons]
      rw [writeReg_not_mem ws (y / 2) (s[w ↦ y.testBit 0]) hw]
      rw [upd_same]
      rw [ih (y := y / 2) (s := s[w ↦ y.testBit 0]) hws hy']
      rw [Nat.testBit_zero]
      have hmod : y % 2 < 2 := Nat.mod_lt _ (by omega)
      have hdiv := Nat.mod_add_div y 2
      by_cases hodd : y % 2 = 1
      · simp [hodd]
        omega
      · have heven : y % 2 = 0 := by omega
        simp [heven]
        omega

private theorem labelState_eq_mapDomain
    (phaseReg : List Wire)
    (value : Nat)
    (psi : State) :
    labelState phaseReg value psi =
      Finsupp.mapDomain (writeReg phaseReg value) psi := by
  classical
  unfold labelState
  rw [Finsupp.linearCombination_apply]
  unfold Finsupp.mapDomain
  apply Finsupp.sum_congr
  intro s _
  simp [ket]

private theorem writeReg_injOn_support_clean
    (phaseReg : List Wire)
    (value : Nat)
    (psi : State)
    (hphaseZero : ∀ s, psi s ≠ 0 → regValue phaseReg s = 0)
    (hphaseReg : phaseReg.Nodup) :
    Set.InjOn (writeReg phaseReg value) ↑psi.support := by
  intro s hs t ht hst
  have hs0 : regValue phaseReg s = 0 :=
    hphaseZero s (Finsupp.mem_support_iff.mp hs)
  have ht0 : regValue phaseReg t = 0 :=
    hphaseZero t (Finsupp.mem_support_iff.mp ht)
  have h := congrArg (writeReg phaseReg 0) hst
  rw [writeReg_overwrite phaseReg value 0 s hphaseReg,
    writeReg_overwrite phaseReg value 0 t hphaseReg,
    writeReg_zero_eq_of_regValue_zero phaseReg s hs0,
    writeReg_zero_eq_of_regValue_zero phaseReg t ht0] at h
  exact h

private theorem normSq_eq_support_sum
    (psi : State) :
    normSq psi =
      ∑ s ∈ psi.support, Complex.normSq (psi s) := by
  classical
  have hinner :
      inner psi psi =
        ((∑ s ∈ psi.support, Complex.normSq (psi s) : ℝ) : ℂ) := by
    unfold inner
    change
      (∑ s ∈ psi.support,
        (starRingEnd ℂ) (psi s) * psi s) =
      ((∑ s ∈ psi.support, Complex.normSq (psi s) : ℝ) : ℂ)
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    exact (Complex.normSq_eq_conj_mul_self).symm
  unfold normSq
  rw [hinner]
  simp

private theorem normSq_smul
    (c : ℂ) (psi : State) :
    normSq (c • psi) =
      Complex.normSq c * normSq psi := by
  unfold normSq
  rw [inner_smul_smul]
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

private theorem normSq_labelState_clean
    (phaseReg : List Wire)
    (psi : State)
    (value : Nat)
    (hphaseZero : ∀ s, psi s ≠ 0 → regValue phaseReg s = 0)
    (hphaseReg : phaseReg.Nodup) :
    normSq (labelState phaseReg value psi) = normSq psi := by
  classical
  let f : BasisState → BasisState := writeReg phaseReg value
  have hinj : Set.InjOn f ↑psi.support := by
    simpa [f] using
      writeReg_injOn_support_clean phaseReg value psi
        hphaseZero hphaseReg
  rw [labelState_eq_mapDomain]
  change normSq (Finsupp.mapDomain f psi) = normSq psi
  rw [normSq_eq_support_sum, normSq_eq_support_sum]
  rw [Finsupp.mapDomain_support_of_injOn psi hinj]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finsupp.mapDomain_apply' (↑psi.support) (f := f) psi
    Set.Subset.rfl hinj hs]

private theorem filter_labelState_eq_self
    (phaseReg : List Wire)
    (psi : State)
    (value : Nat)
    (hvalue : value < 2 ^ phaseReg.length)
    (hphaseReg : phaseReg.Nodup) :
    Finsupp.filter
        (fun s => regValue phaseReg s = value)
        (labelState phaseReg value psi) =
      labelState phaseReg value psi := by
  classical
  apply (Finsupp.filter_eq_self_iff _ _).mpr
  intro t ht
  have htmem :
      t ∈ (Finsupp.mapDomain
        (writeReg phaseReg value) psi).support := by
    rw [← labelState_eq_mapDomain]
    exact Finsupp.mem_support_iff.mpr ht
  have htimg :
      t ∈ Finset.image (writeReg phaseReg value) psi.support :=
    Finsupp.mapDomain_support htmem
  rcases Finset.mem_image.mp htimg with ⟨s, _, rfl⟩
  exact regValue_writeReg_of_lt phaseReg value s hphaseReg hvalue

private theorem filter_labelState_eq_zero
    (phaseReg : List Wire)
    (psi : State)
    (z value : Nat)
    (hz : z < 2 ^ phaseReg.length)
    (hne : z ≠ value)
    (hphaseReg : phaseReg.Nodup) :
    Finsupp.filter
        (fun s => regValue phaseReg s = value)
        (labelState phaseReg z psi) = 0 := by
  classical
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro t htvalue
  by_contra ht
  have htmem :
      t ∈ (Finsupp.mapDomain
        (writeReg phaseReg z) psi).support := by
    rw [← labelState_eq_mapDomain]
    exact Finsupp.mem_support_iff.mpr ht
  have htimg :
      t ∈ Finset.image (writeReg phaseReg z) psi.support :=
    Finsupp.mapDomain_support htmem
  rcases Finset.mem_image.mp htimg with ⟨s, _, rfl⟩
  have hzvalue :=
    regValue_writeReg_of_lt phaseReg z s hphaseReg hz
  exact hne (hzvalue.symm.trans htvalue)

private theorem registerProbability_eq_normSq_filter
    (phaseReg : List Wire)
    (value : Nat)
    (psi : State) :
    registerProbability phaseReg value psi =
      normSq
        (Finsupp.filter
          (fun s => regValue phaseReg s = value) psi) := by
  classical
  unfold registerProbability
  rw [normSq_eq_support_sum]
  rw [Finsupp.support_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : regValue phaseReg s = value
  · simp [h]
  · simp [h]

private theorem filter_sum_smul_labelState
    (phaseReg : List Wire)
    (psi : State)
    (a : Nat → ℂ)
    (value : Nat) :
    Finsupp.filter
        (fun s => regValue phaseReg s = value)
        (∑ z ∈ Finset.range (2 ^ phaseReg.length),
          a z • labelState phaseReg z psi) =
      ∑ z ∈ Finset.range (2 ^ phaseReg.length),
        a z •
          Finsupp.filter
            (fun s => regValue phaseReg s = value)
            (labelState phaseReg z psi) := by
  classical
  ext s
  by_cases h : regValue phaseReg s = value
  · simp [h, Finset.sum_apply]
  · simp [h, Finset.sum_apply]

theorem registerProbability_label_superposition
    (phaseReg : List Wire)
    (psi : State)
    (a : Nat → ℂ)
    (value : Fin (2 ^ phaseReg.length))
    (hphaseZero : ∀ s, psi s ≠ 0 → regValue phaseReg s = 0)
    (hphaseReg : phaseReg.Nodup) :
    registerProbability phaseReg value.val
        (∑ z ∈ Finset.range (2 ^ phaseReg.length),
          a z • labelState phaseReg z psi) =
      Complex.normSq (a value.val) * normSq psi := by
  classical
  rw [registerProbability_eq_normSq_filter]
  rw [filter_sum_smul_labelState phaseReg psi a value.val]
  rw [Finset.sum_eq_single value.val]
  · rw [filter_labelState_eq_self phaseReg psi value.val value.isLt hphaseReg]
    rw [normSq_smul]
    rw [normSq_labelState_clean phaseReg psi value.val hphaseZero hphaseReg]
  · intro z hz hzne
    have hzlt : z < 2 ^ phaseReg.length := Finset.mem_range.mp hz
    rw [filter_labelState_eq_zero phaseReg psi z value.val hzlt hzne hphaseReg]
    simp
  · intro hnot
    exact (hnot (Finset.mem_range.mpr value.isLt)).elim
end

end ShorECDLP.Quantum.PhaseEstimation
