import ShorECDLP.Framework.Quantum.MeasurementUncompute
/-!
# Register measurement followed by adaptive work

The complete transcript selects an adaptive continuation, which may itself
measure and branch. This is needed by Figure 15: inversion and multiplication
occur between the initial register reset and its classical phase correction.
The interpreter preserves both the reset transcript and continuation history.
-/
namespace ShorECDLP.Quantum
noncomputable section

def measureResetThen : List Wire → (List Bool → AdaptiveCircuit) → AdaptiveCircuit
  | [], next => next []
  | t :: ts, next => .xMeasureReset t
      (measureResetThen ts (fun bs => next (false :: bs)))
      (measureResetThen ts (fun bs => next (true :: bs)))

private def afterRegisterBranch (targets : List Wire) (outcomes : List Bool)
    (b : InstrumentBranch) : InstrumentBranch where
  history := outcomes ++ b.history
  kraus := b.kraus.comp (xResetRegisterKraus targets outcomes)

theorem run_measureResetThen (targets : List Wire) (next : List Bool → AdaptiveCircuit) :
    (measureResetThen targets next).run =
      (boolTranscripts targets.length).flatMap (fun outcomes =>
        (next outcomes).run.map (afterRegisterBranch targets outcomes)) := by
  induction targets generalizing next with
  | nil =>
    simp only [measureResetThen,List.length_nil,boolTranscripts,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    have h (b : InstrumentBranch) : afterRegisterBranch ([] : List Wire) ([] : List Bool) b = b := by cases b; rfl
    have hm : afterRegisterBranch ([] : List Wire) ([] : List Bool) = id := funext h
    rw [hm,List.map_id]
  | cons t ts ih =>
    simp only [measureResetThen,AdaptiveCircuit.run,ih,List.length_cons,boolTranscripts,
      List.flatMap_append,List.flatMap_map,List.map_flatMap,List.map_map]
    congr 1

theorem measureResetThen_wellFormed (targets : List Wire) (next : List Bool → AdaptiveCircuit)
    (h : ∀ outcomes, outcomes.length = targets.length → (next outcomes).WellFormed) :
    (measureResetThen targets next).WellFormed := by
  induction targets generalizing next with
  | nil => exact h [] rfl
  | cons t ts ih =>
    constructor <;> apply ih <;> intro bs hb <;> apply h <;> simp [hb]

private theorem phase_square (targets : List Wire) (outcomes : List Bool) (s : BasisState) :
    registerXPhase targets outcomes s * registerXPhase targets outcomes s = 1 := by
  induction targets generalizing outcomes with
  | nil => simp [registerXPhase]
  | cons target targets ih =>
    cases outcomes with
    | nil => simp [registerXPhase]
    | cons outcome outcomes =>
      rw [registerXPhase,mul_mul_mul_comm,ih]
      cases outcome <;> cases s target <;> norm_num

private theorem amplitude_norm (c : ℂ) (s : BasisState) :
    normSq (c • ket s) = Complex.normSq c := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

private theorem coherent_normalization_from_witness (program : AdaptiveCircuit)
    (f : BasisState → BasisState) (Valid : BasisState → Prop) (cs : List ℂ)
    (hb : List.Forall₂ (BranchCoherentOn (Finsupp.lmapDomain ℂ ℂ f) Valid) program.run cs)
    (hw : program.WellFormed) (s : BasisState) (hs : Valid s) :
    (cs.map Complex.normSq).sum = 1 := by
  have hm := program.run_preservesBornMass hw (ket s)
  rw [normSq_ket] at hm
  rw [← hm]
  unfold Instrument.bornMass
  clear hm hw
  generalize he : program.run = bs at hb ⊢
  clear he
  induction hb with
  | nil => rfl
  | @cons b c bs cs h ht ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [h s hs]
    have hf : Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by simp [ket]
    rw [hf,amplitude_norm,ih]

/-- Measurement may be followed by further adaptive work. The continuation must
reconstruct the measured register's phase on the surviving state; its own
normalized coefficients may depend on the transcript, but never on the input. -/
theorem measureResetThen_coherent (targets : List Wire)
    (next : List Bool → AdaptiveCircuit) (nextIdeal : List Bool → State →ₗ[ℂ] State)
    (Next : List Bool → BasisState → Prop) (Valid : BasisState → Prop)
    (f : BasisState → BasisState) (hnodup : targets.Nodup)
    (hw : ∀ outcomes, outcomes.length = targets.length → (next outcomes).WellFormed)
    (hn : ∀ outcomes, CoherentlyImplementsOn (next outcomes) (nextIdeal outcomes) (Next outcomes))
    (hcorrect : ∀ outcomes, outcomes.length = targets.length → ∀ s, Valid s →
      Next outcomes (clearRegister targets s) ∧
      nextIdeal outcomes (ket (clearRegister targets s)) =
        registerXPhase targets outcomes s • ket (f s))
    (witness : BasisState) (hv : Valid witness) :
    CoherentlyImplementsOn (measureResetThen targets next)
      (Finsupp.lmapDomain ℂ ℂ f) Valid := by
  classical
  choose cs hc hm using hn
  let coefficients := (boolTranscripts targets.length).flatMap
    (fun outcomes => (cs outcomes).map (fun c => registerXResetMagnitude targets.length * c))
  have hrow (outcomes : List Bool) (hout : outcomes ∈ boolTranscripts targets.length) :
      List.Forall₂ (BranchCoherentOn (Finsupp.lmapDomain ℂ ℂ f) Valid)
        ((next outcomes).run.map (afterRegisterBranch targets outcomes))
        ((cs outcomes).map (fun c => registerXResetMagnitude targets.length * c)) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply (hc outcomes).imp
    intro b c hb s hs
    have hl := mem_boolTranscripts_length hout
    have hnxt := hcorrect outcomes hl s hs
    change b.kraus (xResetRegisterKraus targets outcomes (ket s)) =
      (registerXResetMagnitude targets.length * c) • (Finsupp.lmapDomain ℂ ℂ f (ket s))
    rw [xResetRegisterKraus_ket targets outcomes s hl hnodup,
      registerXResetCoeff_eq_magnitude_mul_phase targets outcomes s hl,
      map_smul,hb _ hnxt.1,hnxt.2]
    have hf : Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by simp [ket]
    rw [hf]
    simp only [smul_smul]
    congr 1
    calc
      (registerXResetMagnitude targets.length * registerXPhase targets outcomes s) *
          (c * registerXPhase targets outcomes s) =
        (registerXResetMagnitude targets.length * c) *
          (registerXPhase targets outcomes s * registerXPhase targets outcomes s) := by ring
      _ = _ := by rw [phase_square,mul_one]
  have hall : List.Forall₂ (BranchCoherentOn (Finsupp.lmapDomain ℂ ℂ f) Valid)
      (measureResetThen targets next).run coefficients := by
    rw [run_measureResetThen]
    unfold coefficients
    have hlist (outs : List (List Bool)) (hout : ∀ o ∈ outs, o ∈ boolTranscripts targets.length) :
        List.Forall₂ (BranchCoherentOn (Finsupp.lmapDomain ℂ ℂ f) Valid)
          (outs.flatMap (fun outcomes => (next outcomes).run.map (afterRegisterBranch targets outcomes)))
          (outs.flatMap (fun outcomes => (cs outcomes).map (fun c => registerXResetMagnitude targets.length * c))) := by
      induction outs with
      | nil => exact .nil
      | cons o os ih =>
        exact List.rel_append (hrow o (hout o (by simp))) (ih (fun v hv => hout v (by simp [hv])))
    exact hlist _ (fun _ h => h)
  exact ⟨coefficients,hall,coherent_normalization_from_witness _ f Valid coefficients hall
    (measureResetThen_wellFormed targets next hw) witness hv⟩

end
end ShorECDLP.Quantum
