import ShorECDLP.Framework.Quantum.CoherentRefinement
namespace ShorECDLP.Quantum
open scoped BigOperators
noncomputable section

private theorem mass_sum (ψ : State) :
    normSq ψ = ∑ s ∈ ψ.support, Complex.normSq (ψ s) := by
  classical
  have he : inner ψ ψ = ((∑ s ∈ ψ.support, Complex.normSq (ψ s) : ℝ) : ℂ) := by
    unfold inner
    change (∑ s ∈ ψ.support, (starRingEnd ℂ) (ψ s) * ψ s) = _
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [normSq, he]
  simp

private theorem mass_on (ψ : State) (S : Finset BasisState) (h : ψ.support ⊆ S) :
    normSq ψ = ∑ s ∈ S, Complex.normSq (ψ s) := by
  classical
  rw [mass_sum]
  apply Finset.sum_subset h
  intro s _ hs
  have hz : ψ s = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hs
  simp [hz]

/-- Squared norm of a coherent sum, with the cross term bounded in both directions. -/
theorem normSq_interference (ψ φ : State) :
    (3/4:ℝ)*normSq ψ - 3*normSq φ ≤ normSq (ψ+φ) ∧
    normSq (ψ+φ) ≤ (5/4:ℝ)*normSq ψ + 5*normSq φ := by
  classical
  let S := ψ.support ∪ φ.support
  have ha : (ψ+φ).support ⊆ S := Finsupp.support_add
  rw [mass_on ψ S Finset.subset_union_left, mass_on φ S Finset.subset_union_right,
    mass_on (ψ+φ) S ha]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  constructor <;> apply Finset.sum_le_sum <;> intro s _
  all_goals
    simp only [Finsupp.add_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg ((ψ s).re/2 + 2*(φ s).re),
      sq_nonneg ((ψ s).im/2 + 2*(φ s).im),
      sq_nonneg ((ψ s).re/2 - 2*(φ s).re),
      sq_nonneg ((ψ s).im/2 - 2*(φ s).im)]

/-- Projection to a basis event cannot increase Born mass. -/
theorem normSq_filter_le (event : BasisState → Prop) [DecidablePred event] (ψ : State) :
    normSq (ψ.filter event) ≤ normSq ψ := by
  classical
  rw [mass_on (ψ.filter event) ψ.support (by simp only [Finsupp.support_filter]; exact Finset.filter_subset _ _), mass_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : event s
  · simp [hs]
  · simp [hs, Complex.normSq_nonneg]

/-- Probability weight of a basis event, summed over all internal histories. -/
def Instrument.eventMass (I : Instrument) (event : BasisState → Prop) [DecidablePred event]
    (ψ : State) : ℝ := (I.map fun b => normSq ((b.kraus ψ).filter event)).sum

theorem Instrument.eventMass_le_bornMass (I : Instrument) (event : BasisState → Prop)
    [DecidablePred event] (ψ : State) : I.eventMass event ψ ≤ I.bornMass ψ := by
  induction I with
  | nil => simp [eventMass, bornMass]
  | cons b bs ih =>
    simp only [eventMass, bornMass, List.map_cons, List.sum_cons] at *
    exact add_le_add (normSq_filter_le event _) ih

/-- Internal histories are summed incoherently, but each branch retains the input cross term. -/
theorem Instrument.eventMass_interference (I : Instrument) (event : BasisState → Prop)
    [DecidablePred event] (ψ φ : State) :
    (3/4:ℝ)*I.eventMass event ψ - 3*I.eventMass event φ ≤ I.eventMass event (ψ+φ) ∧
    I.eventMass event (ψ+φ) ≤ (5/4:ℝ)*I.eventMass event ψ + 5*I.eventMass event φ := by
  induction I with
  | nil => simp [eventMass]
  | cons b bs ih =>
    have hb := normSq_interference ((b.kraus ψ).filter event) ((b.kraus φ).filter event)
    simp only [eventMass, List.map_cons, List.sum_cons] at *
    simp only [map_add, Finsupp.filter_add] at *
    constructor <;> linarith [hb.1, hb.2, ih.1, ih.2]
private theorem mass_smul (c : ℂ) (ψ : State) :
    normSq (c • ψ) = Complex.normSq c * normSq ψ := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

/-- An injective map on the input support preserves its squared norm. -/
theorem normSq_mapDomain (f : BasisState → BasisState) (ψ : State)
    (hf : Set.InjOn f ψ.support) : normSq (ψ.mapDomain f) = normSq ψ := by
  classical
  rw [mass_sum, mass_sum, Finsupp.mapDomain_support_of_injOn _ hf,
    Finset.sum_image (fun a ha b hb hab => hf ha hb hab)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finsupp.mapDomain_apply' (↑ψ.support : Set BasisState) ψ (fun _ h => h) hf hs]

@[simp] theorem normSq_neg (ψ : State) : normSq (-ψ) = normSq ψ := by
  simpa only [neg_one_smul, Complex.normSq_neg, Complex.normSq_one, one_mul] using
    mass_smul (-1) ψ

/-- A coherent implementation has the ideal event weight on any supported input. -/
theorem CoherentlyImplementsOn.eventMass {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State} {Valid : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) {ψ : State}
    (hs : SupportedOn Valid ψ) (event : BasisState → Prop) [DecidablePred event] :
    program.run.eventMass event ψ = normSq ((ideal ψ).filter event) := by
  obtain ⟨cs, ha, hm⟩ := coherent_on_supported_state h hs
  have he : program.run.eventMass event ψ =
      (cs.map Complex.normSq).sum * normSq ((ideal ψ).filter event) := by
    clear hm
    generalize program.run = I at ha ⊢
    induction ha with
    | nil => simp [Instrument.eventMass]
    | @cons b c bs cs hb ht ih =>
      simp only [Instrument.eventMass, List.map_cons, List.sum_cons] at *
      rw [hb, Finsupp.filter_smul, mass_smul, ih]
      ring
  rw [he, hm, one_mul]

end
end ShorECDLP.Quantum
