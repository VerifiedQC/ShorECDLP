import ShorECDLP.Framework.Quantum.Interference
namespace ShorECDLP.Quantum
noncomputable section

private theorem mass_nonneg (ψ : State) : 0 ≤ normSq ψ := by
  have h := normSq_interference (0 : State) ψ
  simp only [zero_add] at h
  have hz : normSq (0 : State)=0 := by simp [normSq]
  rw [hz] at h
  linarith [h.2]

theorem Instrument.bornMass_filter_le (I : Instrument) (p : InstrumentBranch → Bool) (ψ : State) :
    Instrument.bornMass (I.filter p) ψ ≤ I.bornMass ψ := by
  induction I with
  | nil => simp [bornMass]
  | cons b bs ih =>
    by_cases hb : p b
    · simpa [bornMass, hb] using add_le_add_left ih (normSq (b.kraus ψ))
    · simpa [bornMass, hb] using ih.trans (le_add_of_nonneg_left (mass_nonneg _))

theorem Instrument.bornMass_interference (I : Instrument) (ψ φ : State) :
    (3/4:ℝ)*I.bornMass ψ-3*I.bornMass φ ≤ I.bornMass (ψ+φ) ∧
    I.bornMass (ψ+φ) ≤ (5/4:ℝ)*I.bornMass ψ+5*I.bornMass φ := by
  induction I with
  | nil => simp [bornMass]
  | cons b bs ih =>
    have h := normSq_interference (b.kraus ψ) (b.kraus φ)
    simp only [bornMass, List.map_cons, List.sum_cons, map_add] at *
    constructor <;> linarith [h.1, h.2, ih.1, ih.2]

@[simp] theorem Instrument.bornMass_neg (I : Instrument) (ψ : State) :
    I.bornMass (-ψ)=I.bornMass ψ := by simp [bornMass]

private theorem mass_smul (c : ℂ) (ψ : State) :
    normSq (c • ψ)=Complex.normSq c*normSq ψ := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

private theorem seq_mass (I J : Instrument) (ψ : State) :
    (I.seq J).bornMass ψ = (I.map (fun b => J.bornMass (b.kraus ψ))).sum := by
  induction I with
  | nil => simp [Instrument.seq, Instrument.bornMass]
  | cons b bs ih =>
    simpa [Instrument.seq, Instrument.bornMass, List.map_map,
      InstrumentBranch.seq, LinearMap.comp_apply, Function.comp_def] using
      congrArg ((J.map (fun x => normSq (x.kraus (b.kraus ψ)))).sum + ·) ih

/-- A norm-contractive terminal selection remains contractive after a normalized prefix. -/
theorem Instrument.seq_bornMass_le (I J : Instrument)
    (hJ : ∀ ψ, J.bornMass ψ ≤ normSq ψ) (ψ : State) :
    (I.seq J).bornMass ψ ≤ I.bornMass ψ := by
  rw [seq_mass]
  induction I with
  | nil => simp [bornMass]
  | cons b bs ih =>
    simp only [bornMass, List.map_cons, List.sum_cons] at *
    exact add_le_add (hJ _) ih

/-- Coherent refinement transports any selected terminal instrument on supported inputs. -/
theorem CoherentlyImplementsOn.terminalMass {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State} {Valid : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) {ψ : State}
    (hs : SupportedOn Valid ψ) (J : Instrument) :
    (program.run.seq J).bornMass ψ = J.bornMass (ideal ψ) := by
  obtain ⟨cs, ha, hm⟩ := coherent_on_supported_state h hs
  have scale (c : ℂ) (φ : State) : J.bornMass (c • φ)=Complex.normSq c*J.bornMass φ := by
    simp only [Instrument.bornMass, map_smul, mass_smul]
    induction J with
    | nil => simp
    | cons b bs ih => simp only [List.map_cons, List.sum_cons] at *; rw [ih]; ring
  rw [seq_mass]
  have he : (program.run.map (fun b => J.bornMass (b.kraus ψ))).sum =
      (cs.map Complex.normSq).sum * J.bornMass (ideal ψ) := by
    clear hm
    generalize program.run = I at ha ⊢
    induction ha with
    | nil => simp
    | @cons b c bs cs hb ht ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [hb, scale, ih]
      ring
  rw [he, hm, one_mul]
end
end ShorECDLP.Quantum
