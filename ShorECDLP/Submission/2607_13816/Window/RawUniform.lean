import ShorECDLP.Submission.«2607_13816».Window.RawFibers
import ShorECDLP.Submission.«2607_13816».Window.ReducedUniform
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

private theorem inner_list_left (s : BasisState) (xs : List BasisState)
    (h : s ∉ xs) : inner (ket s) (xs.map ket).sum = 0 := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    simp only [List.mem_cons, not_or] at h
    simp [inner_add_right, inner_ket_ne h.1, ih h.2]

private theorem inner_list_right (s : BasisState) (xs : List BasisState)
    (h : s ∉ xs) : inner (xs.map ket).sum (ket s) = 0 := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    simp only [List.mem_cons, not_or] at h
    simp [inner_add_left, inner_ket_ne (Ne.symm h.1), ih h.2]

/-- Distinct physical basis assignments have no interference in their total mass. -/
theorem normSq_distinct_kets (xs : List BasisState) (hn : xs.Nodup) :
    normSq (xs.map ket).sum = xs.length := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    have h := List.nodup_cons.mp hn
    simp only [List.map_cons, List.sum_cons, normSq, inner_add_add,
      inner_ket_self, inner_list_left s xs h.1, inner_list_right s xs h.1,
      add_zero, Complex.add_re, Complex.one_re, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    rw [← normSq, ih h.2]
    ring

/-- The mass of any selected part of the physical uniform sum is its word count. -/
theorem phaseUniformSum_filtered_mass (ws : List Wire) (hn : ws.Nodup)
    (s : BasisState) (p : BasisState → Prop) [DecidablePred p] :
    normSq (((fourierOutcomes ws.length).filter (fun bs => p (phaseWordState ws bs s))).map
      (fun bs => ket (phaseWordState ws bs s))).sum =
    ((fourierOutcomes ws.length).filter (fun bs => p (phaseWordState ws bs s))).length := by
  let xs := (fourierOutcomes ws.length).filter (fun bs => p (phaseWordState ws bs s))
  have hx : xs.Nodup := (fourierOutcomes_nodup _).filter _
  have hi : xs.Pairwise (fun a b => phaseWordState ws a s ≠ phaseWordState ws b s) := by
    apply hx.imp_of_mem
    intro a b ha hb hab he
    have ha' := (fourierOutcomes_mem _ _).mp (List.mem_of_mem_filter ha)
    have hb' := (fourierOutcomes_mem _ _).mp (List.mem_of_mem_filter hb)
    apply hab
    have hw := congrArg (wireValues ws) he
    simpa only [phaseWordState_word ws hn a ha' s, phaseWordState_word ws hn b hb' s] using hw
  have ht := normSq_distinct_kets (xs.map (fun bs => phaseWordState ws bs s))
    (List.pairwise_map.mpr hi)
  simpa only [List.map_map, Function.comp_def, List.length_map] using ht

/-- The first physical window and the remaining 448 bits form the emitted uniform sum. -/
theorem reducedPhaseUniformSum_firstWindow (s : BasisState) :
    phaseUniformSum reducedPhaseWires s =
      ((fourierOutcomes 16).map (fun bs =>
        phaseUniformSum (List.range' 871 240 ++ List.range' 1127 208)
          (phaseWordState (List.range' 855 16) bs s))).sum := by
  have hw : reducedPhaseWires = List.range' 855 16 ++
      (List.range' 871 240 ++ List.range' 1127 208) := by decide +kernel
  rw [hw, phaseUniformSum_append]
  simp only [List.length_range']
/-- Normalization turns the exact orthogonal word count into Born mass. -/
theorem phaseUniformSum_filtered_normalized_mass (ws : List Wire) (hn : ws.Nodup)
    (s : BasisState) (p : BasisState → Prop) [DecidablePred p] :
    normSq ((((((Real.sqrt 2)⁻¹:ℝ):ℂ))^ws.length) •
      (((fourierOutcomes ws.length).filter (fun bs => p (phaseWordState ws bs s))).map
        (fun bs => ket (phaseWordState ws bs s))).sum) =
    (((fourierOutcomes ws.length).filter (fun bs => p (phaseWordState ws bs s))).length : ℝ) /
      2^ws.length := by
  have hc : Complex.normSq (((Real.sqrt 2)⁻¹:ℝ):ℂ) = (2:ℝ)⁻¹ := by
    simp only [Complex.normSq_ofReal]
    rw [← mul_inv, ← pow_two]
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hs (c : ℂ) (ψ : State) : normSq (c • ψ)=Complex.normSq c * normSq ψ := by
    unfold normSq
    rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
    simp
  rw [hs, map_pow, hc, phaseUniformSum_filtered_mass ws hn s p]
  simp [div_eq_mul_inv, mul_comm]

theorem phaseBasisSum_filter (xs : List BasisState) (p : BasisState → Prop)
    [DecidablePred p] : ((xs.map ket).sum).filter p = ((xs.filter p).map ket).sum := by
  induction xs with
  | nil => simp [Finsupp.filter_zero]
  | cons s xs ih =>
    by_cases h : p s
    · simp [Finsupp.filter_add, ket, Finsupp.filter_single_of_pos p h, h, ih]
    · simp [Finsupp.filter_add, ket, Finsupp.filter_single_of_neg p h, h, ih]

/-- Born mass after distinct clean-wire Hadamards equals the normalized count
of assignments satisfying the event. The background may contain nonzero wires. -/
theorem phaseHadamards_filtered_mass (ws : List Wire) (hn : ws.Nodup)
    (s : BasisState) (hz : Clean ws s) (p : BasisState → Prop) [DecidablePred p] :
    normSq ((Quantum.run (ws.map Gate.H) (ket s)).filter p) =
      (((fourierOutcomes ws.length).filter
        (fun bs => p (phaseWordState ws bs s))).length : ℝ) / 2^ws.length := by
  rw [phaseHadamards_uniform ws hn s hz,Finsupp.filter_smul]
  have hf := phaseBasisSum_filter
    ((fourierOutcomes ws.length).map (fun bs => phaseWordState ws bs s)) p
  simp only [List.map_map,Function.comp_def,List.filter_map] at hf
  unfold phaseUniformSum
  rw [hf]
  exact phaseUniformSum_filtered_normalized_mass ws hn s p

/-- An actual projection of the prepared state has the exact normalized word count. -/
theorem reducedPhasePrepare_filtered_mass (p : BasisState → Prop) [DecidablePred p] :
    normSq ((Quantum.run reducedPhasePrepare (ket zeroBasisState)).filter p) =
      (((fourierOutcomes 464).filter
        (fun bs => p (phaseWordState reducedPhaseWires bs zeroBasisState))).length : ℝ) / 2^464 := by
  have h := phaseHadamards_filtered_mass reducedPhaseWires (by decide +kernel)
    zeroBasisState (by intro w hw; rfl) p
  simpa only [reducedPhasePrepare,reducedPhaseWires,List.length_append,List.length_range'] using h

end
end ShorECDLP.Paper2607_13816
