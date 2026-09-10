import ShorECDLP.Submission.«2607_13816».EEA.TerminalClear
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem basisLift_ket (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by
  simp [ket]
private theorem basisAmplitude_norm (c : ℂ) (s : BasisState) :
    normSq (c • ket s) = Complex.normSq c := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp
private theorem coherent_of_basis_branches (program : AdaptiveCircuit)
    (f : BasisState → BasisState) (Valid : BasisState → Prop)
    (amplitude : InstrumentBranch → ℂ)
    (hw : program.WellFormed) (witness : BasisState) (hv : Valid witness)
    (hbranch : ∀ b ∈ program.run, ∀ s, Valid s →
      b.kraus (ket s) = amplitude b • ket (f s)) :
    CoherentlyImplementsOn program (Finsupp.lmapDomain ℂ ℂ f) Valid := by
  refine ⟨program.run.map amplitude, ?_, ?_⟩
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro b hb s hs
    rw [basisLift_ket]
    exact hbranch b hb s hs
  · have hmass := program.run_preservesBornMass hw (ket witness)
    rw [normSq_ket] at hmass
    rw [List.map_map]
    change (program.run.map (fun b => Complex.normSq (amplitude b))).sum = 1
    rw [← hmass]
    unfold Instrument.bornMass
    congr 1
    apply List.map_congr_left
    intro b hb
    rw [hbranch b hb witness hv, basisAmplitude_norm]
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
private theorem preprocess_basis_coherent :
    CoherentlyImplementsOn eeaPreprocess (Finsupp.lmapDomain ℂ ℂ eeaPreprocessIdealState)
      (Clean (List.range' 0 263 ++ List.range' 519 61)) := by
  apply coherent_of_basis_branches eeaPreprocess eeaPreprocessIdealState _
    (fun b => registerXResetMagnitude b.history.length) eeaPreprocess_wellFormed
    (fun _ => false) (by intro w hw; rfl)
  intro b hb s hs
  exact eeaPreprocess_branch_correct s hs b hb
private theorem parity_basis_coherent :
    CoherentlyImplementsOn secp256k1EEAParityCorrection
      (Finsupp.lmapDomain ℂ ℂ secp256k1EEAParityIdealState)
      (fun s => s 560=false ∧ s 561=false ∧ s 562=false) := by
  apply coherent_of_basis_branches secp256k1EEAParityCorrection
    secp256k1EEAParityIdealState _ (fun b => registerXResetMagnitude b.history.length)
    secp256k1EEAParityCorrection_wellFormed (fun _ => false) (by simp)
  intro b hb s hs
  exact secp256k1EEAParityCorrection_branch s hs.1 hs.2.1 hs.2.2 b hb

/-- Original input assumptions for the complete forward EEA wrapper. -/
def Secp256k1EEAInputValid (s : BasisState) : Prop :=
  Clean (List.range' 0 263 ++ List.range' 519 61) s ∧
  0 < boolWordToNat (wireValues (List.range' 263 256) s) ∧
  boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p
/-- Pinned forward wrapper: preprocessing, fixed EEA schedule, canonicalization, epoch
compression, parity correction and known Work1 clearing, in that order. -/
def secp256k1EEAForwardWrapper : AdaptiveCircuit :=
  ((((eeaPreprocess.seq (secp256k1EEAForwardAdaptive indexedStepProductionRegisters)).seq
    (.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done)).seq
    secp256k1EEAParityCorrection).seq (.unitary terminalWork1Clear .done))
/-- The complete adaptive wrapper has one input-independent normalized branch expansion
for all clean nonzero canonical inputs. Its ideal state carries the proved modular inverse. -/
theorem secp256k1EEAForwardWrapper_coherent :
    CoherentlyImplementsOn secp256k1EEAForwardWrapper
      (Finsupp.lmapDomain ℂ ℂ secp256k1EEAOutputIdealState) Secp256k1EEAInputValid := by
  have hc := canonicalWork2Rotation_HPFree
  have hp : CoherentlyImplementsOn eeaPreprocess
      (Finsupp.lmapDomain ℂ ℂ eeaPreprocessIdealState) Secp256k1EEAInputValid :=
    coherent_basis_strengthen preprocess_basis_coherent (fun _ h => h.1)
  have hf := secp256k1EEAForwardAdaptive_coherent_preprocessed.congrIdeal
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
theorem secp256k1EEAForwardWrapper_wellFormed : secp256k1EEAForwardWrapper.WellFormed := by
  have he : CircuitWellFormed terminalEpochCompression := by
    simp [terminalEpochCompression,mcxVChain,mcxVChainTail,CircuitWellFormed,Gate.WellFormed]
  have hc : CircuitWellFormed (canonicalWork2Rotation ++ terminalEpochCompression) :=
    (circuitWellFormed_append _ _).mpr ⟨canonicalWork2Rotation_wellFormed,he⟩
  have hcanonical : (AdaptiveCircuit.unitary
      (canonicalWork2Rotation ++ terminalEpochCompression) .done).WellFormed := ⟨hc,trivial⟩
  have hclear : (AdaptiveCircuit.unitary terminalWork1Clear .done).WellFormed :=
    ⟨xorConstant_wellFormed _ _,trivial⟩
  exact ((((eeaPreprocess_wellFormed.seq
    (indexedScheduleAdaptive_wellFormed indexedStepProductionRegisters 256 1
      secp256k1ScheduleLength secp256k1ScheduleLayout_production)).seq
      hcanonical).seq secp256k1EEAParityCorrection_wellFormed).seq hclear)

end
end ShorECDLP.Paper2607_13816
