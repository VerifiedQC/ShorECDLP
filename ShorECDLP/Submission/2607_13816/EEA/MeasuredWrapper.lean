import ShorECDLP.Submission.«2607_13816».EEA.MeasuredForwardImage
import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveWrapper
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem basisLift_ket (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by
  simp [ket]
private theorem coherent_basis_strengthen {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State} {Valid Stronger : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ s, Stronger s → Valid s) :
    CoherentlyImplementsOn program ideal Stronger := by
  obtain ⟨cs, ha, hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (hsub s hs)),hm⟩
private theorem coherent_basis_seq {first second : AdaptiveCircuit}
    {f g : BasisState → BasisState} {Valid Next : BasisState → Prop}
    (hf : CoherentlyImplementsOn first (Finsupp.lmapDomain ℂ ℂ f) Valid)
    (hg : CoherentlyImplementsOn second (Finsupp.lmapDomain ℂ ℂ g) Next)
    (hnext : ∀ s, Valid s → Next (f s)) :
    CoherentlyImplementsOn (first.seq second)
      (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) Valid := by
  have h := hf.seq hg (by
    intro s hs
    rw [basisLift_ket]
    exact supportedOn_ket Next _ (hnext s hs))
  apply h.congrIdeal
  intro s _
  simp only [LinearMap.comp_apply,basisLift_ket]
private theorem coherent_basis_unitary (c : Circuit) (hc : HPFree c)
    (Valid : BasisState → Prop) :
    CoherentlyImplementsOn (.unitary c .done)
      (Finsupp.lmapDomain ℂ ℂ (Classical.run c)) Valid := by
  apply (CoherentlyImplementsOn.unitary c Valid).congrIdeal
  intro s _
  rw [basisLift_ket,Quantum.run_ket_agrees_classical c s hc]
/-- Complete forward wrapper with the new measured EEA schedule. -/
def secp256k1MeasuredEEAForwardWrapper : AdaptiveCircuit :=
  ((((eeaPreprocess.seq (secp256k1MeasuredEEAForward indexedStepProductionRegisters)).seq
    (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
    secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done))
/-- The complete adaptive wrapper has one input-independent normalized branch expansion
for all clean nonzero canonical inputs. Its ideal state carries the proved modular inverse. -/
theorem secp256k1MeasuredEEAForwardWrapper_coherent :
    CoherentlyImplementsOn secp256k1MeasuredEEAForwardWrapper
      (Finsupp.lmapDomain ℂ ℂ secp256k1EEAOutputIdealState) Secp256k1EEAInputValid := by
  have hc := canonicalWork2Rotation_HPFree
  have hp : CoherentlyImplementsOn eeaPreprocess
      (Finsupp.lmapDomain ℂ ℂ eeaPreprocessIdealState) Secp256k1EEAInputValid :=
    coherent_basis_strengthen preprocess_basis_coherent (fun _ h => h.1)
  have hf := secp256k1MeasuredEEAForward_coherent_preprocessed.congrIdeal
    (secondIdeal := Finsupp.lmapDomain ℂ ℂ
      (Classical.run (secp256k1EEAForwardUnitary indexedStepProductionRegisters))) (by
        intro s _
        rw [basisLift_ket,Quantum.run_ket_agrees_classical (secp256k1EEAForwardUnitary indexedStepProductionRegisters) s
          (indexedScheduleUnitary_HPFree indexedStepProductionRegisters 256 1 secp256k1ScheduleLength)])
  have hpf := coherent_basis_seq hp hf (by
    intro s hs
    exact ⟨s,hs.1,hs.2.1,hs.2.2,rfl⟩)
  have he : HPFree terminalEpochCompression := by simp [terminalEpochCompression,mcxVChain_HPFree]
  have hcanonical := coherent_basis_seq hpf
    (coherent_basis_unitary (canonicalWork2Rotation ++ terminalEpochCompression)
      ((hpFree_append _ _).mpr ⟨hc,he⟩) (fun _ => True)) (fun _ _ => trivial)
  have hparity := coherent_basis_seq hcanonical parity_basis_coherent (by
    intro s hs
    have hready := (secp256k1EEAForward_canonical_epoch s hs.1 hs.2.1 hs.2.2).2.2
    have h560 := hready 560 (by decide)
    have h561 := hready 561 (by decide)
    have h562 := hready 562 (by decide)
    simpa only [Classical.run_append] using And.intro h560 (And.intro h561 h562))
  have hclear : HPFree terminalWork1Clear := xorConstant_HPFree _ _
  have hall := coherent_basis_seq hparity
    (coherent_basis_unitary terminalWork1Clear hclear (fun _ => True)) (fun _ _ => trivial)
  apply hall.congrIdeal
  intro s _
  simp only [basisLift_ket]
  exact congrArg ket (by
    simp only [secp256k1EEAOutputIdealState, Classical.run_append])

/-- Every physical gate and measurement in the complete wrapper is well formed. -/
theorem secp256k1MeasuredEEAForwardWrapper_wellFormed : secp256k1MeasuredEEAForwardWrapper.WellFormed := by
  have he : CircuitWellFormed terminalEpochCompression := by
    simp [terminalEpochCompression,mcxVChain,mcxVChainTail,CircuitWellFormed,Gate.WellFormed]
  have hc : CircuitWellFormed (canonicalWork2Rotation ++ terminalEpochCompression) :=
    (circuitWellFormed_append _ _).mpr ⟨canonicalWork2Rotation_wellFormed,he⟩
  have hcanonical : (AdaptiveCircuit.unitary
      (canonicalWork2Rotation ++ terminalEpochCompression) .done).WellFormed := ⟨hc,trivial⟩
  have hclear : (AdaptiveCircuit.unitary terminalWork1Clear .done).WellFormed :=
    ⟨xorConstant_wellFormed _ _,trivial⟩
  exact ((((eeaPreprocess_wellFormed.seq
    (measuredIndexedSchedule_wellFormed indexedStepProductionRegisters 256 1
      secp256k1ScheduleLength secp256k1ScheduleLayout_production)).seq
      hcanonical).seq secp256k1EEAParityCorrection_wellFormed).seq hclear)

/-- Complete inverse wrapper with the new measured EEA schedule. -/
def secp256k1MeasuredEEAReverseWrapper : AdaptiveCircuit :=
  (secp256k1EEAReversePostprocessing.seq
    (secp256k1MeasuredEEAReverse indexedStepProductionRegisters)).seq eeaUnpreprocess

attribute [local irreducible] secp256k1EEAOutputIdealState secp256k1EEAReverseWrapperIdealState
  secp256k1MeasuredEEAReverse secp256k1EEAReverseUnitary

/-- Every physical gate and measurement of the complete source reverse is well formed. -/
theorem secp256k1MeasuredEEAReverseWrapper_wellFormed : secp256k1MeasuredEEAReverseWrapper.WellFormed := by
  exact (secp256k1EEAReversePostprocessing_wellFormed.seq
    (secp256k1MeasuredEEAReverse_wellFormed indexedStepProductionRegisters
      secp256k1ScheduleLayout_production)).seq eeaUnpreprocess_wellFormed

/-- One normalized expansion implements the reverse on every actual valid forward output. -/
theorem secp256k1MeasuredEEAReverseWrapper_coherent :
    CoherentlyImplementsOn secp256k1MeasuredEEAReverseWrapper
      (Finsupp.lmapDomain ℂ ℂ secp256k1EEAReverseWrapperIdealState)
      (fun s => ∃ original, Secp256k1EEAInputValid original ∧ s = secp256k1EEAOutputIdealState original) := by
  have hp := coherent_basis_strengthen secp256k1EEAReversePostprocessing_coherent
    (Stronger := fun s => ∃ original, Secp256k1EEAInputValid original ∧
      s = secp256k1EEAOutputIdealState original) (by
        intro s hs
        obtain ⟨original,ho,rfl⟩ := hs
        have h := (secp256k1EEAOutputIdealState_correct original ho.1 ho.2.1 ho.2.2).2.2.2.2
        exact ⟨h 560 (by decide),h 561 (by decide),h 562 (by decide)⟩)
  have hfree : HPFree (secp256k1EEAReverseUnitary indexedStepProductionRegisters) := by
    unfold secp256k1EEAReverseUnitary
    exact indexedScheduleInverseUnitary_HPFree indexedStepProductionRegisters 256 1 secp256k1ScheduleLength
  have hi := secp256k1MeasuredEEAReverse_coherent_forward_image.congrIdeal
    (secondIdeal := Finsupp.lmapDomain ℂ ℂ (fun s => Classical.run
      (secp256k1EEAReverseUnitary indexedStepProductionRegisters) s)) (by
        intro s hs
        rw [basisLift_ket,Quantum.run_ket_agrees_classical
          (secp256k1EEAReverseUnitary indexedStepProductionRegisters) s
          hfree])
  have hpi := coherent_basis_seq hp hi (by
    intro s hs
    obtain ⟨original,ho,rfl⟩ := hs
    exact ⟨original,ho.1,ho.2.1,ho.2.2,secp256k1EEAReversePostprocessing_output original ho⟩)
  have hall := coherent_basis_seq hpi eeaUnpreprocess_coherent (by
    intro s hs
    obtain ⟨original,ho,rfl⟩ := hs
    refine ⟨original,ho,?_⟩
    rw [secp256k1EEAReversePostprocessing_output original ho]
    exact secp256k1EEAReverseUnitary_after_forward_preprocessed original ho.1 ho.2.1 ho.2.2)
  apply hall.congrIdeal
  intro s hs
  simp only [basisLift_ket]
  simp only [secp256k1EEAReverseWrapperIdealState]


end
end ShorECDLP.Paper2607_13816
