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

/-- The pinned inverse wrapper first restores Work1, undoes parity correction and epoch
compression, then restores the circular terminal Work2 representation. -/
def secp256k1EEAReversePostprocessing : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary terminalWork1Clear .done).seq secp256k1EEAParityCorrection).seq
    (.unitary (terminalEpochCompression ++ canonicalWork2InverseRotation) .done)
/-- Complete state of the source reverse postprocessing, including retained metadata. -/
def secp256k1EEAReversePostprocessingIdealState (s : BasisState) : BasisState :=
  Classical.run (terminalEpochCompression ++ canonicalWork2InverseRotation)
    (secp256k1EEAParityIdealState (Classical.run terminalWork1Clear s))
/-- One normalized branch expansion covers all inputs with the three clean parity auxiliaries. -/
theorem secp256k1EEAReversePostprocessing_coherent :
    CoherentlyImplementsOn secp256k1EEAReversePostprocessing
      (Finsupp.lmapDomain ℂ ℂ secp256k1EEAReversePostprocessingIdealState)
      (fun s => s 560=false ∧ s 561=false ∧ s 562=false) := by
  have hc := coherent_basis_unitary terminalWork1Clear (xorConstant_HPFree _ _)
    (fun s => s 560=false ∧ s 561=false ∧ s 562=false)
  have hp := coherent_basis_seq hc parity_basis_coherent (by
    intro s hs
    have hf := (xorConstant_correct (List.range' 4 259) (ShorECDLP.p+2^258) s List.nodup_range').2
    exact ⟨(hf 560 (by decide)).trans hs.1,(hf 561 (by decide)).trans hs.2.1,
      (hf 562 (by decide)).trans hs.2.2⟩)
  have he : HPFree terminalEpochCompression := by simp [terminalEpochCompression,mcxVChain_HPFree]
  have hall := coherent_basis_seq hp (coherent_basis_unitary
    (terminalEpochCompression ++ canonicalWork2InverseRotation)
    ((hpFree_append _ _).mpr ⟨he,canonicalWork2InverseRotation_HPFree⟩) (fun _ => True))
    (fun _ _ => trivial)
  apply hall.congrIdeal
  intro s _
  simp only [basisLift_ket]
  rfl
/-- Every actual gate and measurement of reverse postprocessing is physically well formed. -/
theorem secp256k1EEAReversePostprocessing_wellFormed :
    secp256k1EEAReversePostprocessing.WellFormed := by
  have he : CircuitWellFormed terminalEpochCompression := by
    simp [terminalEpochCompression,mcxVChain,mcxVChainTail,CircuitWellFormed,Gate.WellFormed]
  have hc : (AdaptiveCircuit.unitary terminalWork1Clear .done).WellFormed :=
    ⟨xorConstant_wellFormed _ _,trivial⟩
  have ht : (AdaptiveCircuit.unitary
      (terminalEpochCompression ++ canonicalWork2InverseRotation) .done).WellFormed :=
    ⟨(circuitWellFormed_append _ _).mpr ⟨he,canonicalWork2InverseRotation_wellFormed⟩,trivial⟩
  exact (hc.seq secp256k1EEAParityCorrection_wellFormed).seq ht
private theorem reverseEpoch_cancel (s : BasisState) : run terminalEpochCompression (run terminalEpochCompression s)=s := by
  have hw : CircuitWellFormed terminalEpochCompression := by
    simp [terminalEpochCompression,mcxVChain,mcxVChainTail,CircuitWellFormed,Gate.WellFormed]
  have ha : terminalEpochCompression.adjoint=terminalEpochCompression := by decide +kernel
  simpa only [ha] using run_adjoint_run_classical terminalEpochCompression hw s
private theorem reverseClear_cancel (s : BasisState) : run terminalWork1Clear (run terminalWork1Clear s)=s := by
  exact run_xorConstant_twice (List.range' 4 259) (ShorECDLP.p+2^258) s List.nodup_range'
private theorem reverseParity_cancel (s : BasisState)
    (hx : boolWordToNat (wireValues (List.range' 263 256) s)≤ShorECDLP.p) :
    secp256k1EEAParityIdealState (secp256k1EEAParityIdealState s)=s := by
  let flip (t : BasisState) : BasisState := t[2 ↦ !t 2]
  have hf (t : BasisState) : flip (flip t)=t := by
    funext w
    by_cases hw : w=2
    · subst w; simp [flip,upd]
    · simp [flip,upd,hw]
  have hinput : wireValues (List.range' 263 256) (flip s)=wireValues (List.range' 263 256) s := by
    apply List.map_congr_left
    intro w hw
    exact upd_other _ _ _ (by obtain ⟨i,hi,he⟩ := List.mem_range'.mp hw; dsimp only [Wire] at *; omega)
  have hm := constMinusIdealState_involutive (List.range' 263 256) secp256k1ModulusBits
    2 ShorECDLP.p (flip s) (by simp) (by simp [secp256k1ModulusBits]) List.nodup_range' (by decide)
    (by decide +kernel) (by decide +kernel) (by rw [hinput];exact hx)
  change flip (constMinusIdealState _ _ 2 (flip (flip (constMinusIdealState _ _ 2 (flip s)))))=s
  rw [hf,hm,hf]
/-- Reverse postprocessing cancels the exact forward postprocessing on every canonical coefficient. -/
theorem secp256k1EEAReversePostprocessing_after_forward (s : BasisState)
    (hx : boolWordToNat (wireValues (List.range' 263 256)
      (Classical.run (canonicalWork2Rotation ++ terminalEpochCompression) s))≤ShorECDLP.p) :
    secp256k1EEAReversePostprocessingIdealState
      (Classical.run terminalWork1Clear (secp256k1EEAParityIdealState
        (Classical.run (canonicalWork2Rotation ++ terminalEpochCompression) s)))=s := by
  simp only [secp256k1EEAReversePostprocessingIdealState,Classical.run_append] at hx ⊢
  rw [reverseClear_cancel,reverseParity_cancel _ hx,reverseEpoch_cancel,
    canonicalWork2InverseRotation_after_forward]
private theorem reverse_take_word_le (bits : List Bool) (count : Nat) :
    boolWordToNat (bits.take count)≤boolWordToNat bits := by
  induction bits generalizing count with
  | nil => simp
  | cons b bs ih =>
    cases count with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons,boolWordToNat_cons]
      have h := ih n
      omega
/-- On original valid inputs, reverse postprocessing restores the entire terminal EEA state,
not just the modular coefficient. -/
theorem secp256k1EEAReversePostprocessing_output (s : BasisState)
    (hs : Secp256k1EEAInputValid s) :
    secp256k1EEAReversePostprocessingIdealState (secp256k1EEAOutputIdealState s)=
      Classical.run (secp256k1EEAForwardUnitary indexedStepProductionRegisters)
        (eeaPreprocessIdealState s) := by
  let before := Classical.run (secp256k1EEAForwardUnitary indexedStepProductionRegisters)
    (eeaPreprocessIdealState s)
  let post := Classical.run (canonicalWork2Rotation ++ terminalEpochCompression) before
  have hfull := secp256k1EEAForward_canonical_epoch s hs.1 hs.2.1 hs.2.2
  have hbound := paperRun_preservesInvariant
    (paperInitial_invariant ShorECDLP.Secp256k1.p_prime hs.2.1 hs.2.2)
  have hb : boolWordToNat (wireValues (List.range' 263 256) post)≤ShorECDLP.p := by
    have ht := reverse_take_word_le (wireValues (List.range' 263 259) post) 256
    have hbank : wireValues (List.range' 263 259) post=constantBits 259
        (paperRun (paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s)))).tPrime := by
      simpa only [post,before,Classical.run_append] using hfull.1
    rw [show (wireValues (List.range' 263 259) post).take 256=
      wireValues (List.range' 263 256) post from by
        simp only [wireValues,←List.map_take,List.take_range'_of_length_ge (by decide : 259≥256)],
      hbank,boolWordToNat_constantBits] at ht
    exact ht.trans ((Nat.mod_le _ _).trans hbound.tPrime_le)
  have hc := secp256k1EEAReversePostprocessing_after_forward before hb
  simpa only [secp256k1EEAOutputIdealState,Classical.run_append] using hc
/-- Forward EEA followed by source reverse postprocessing coherently returns the full terminal
schedule state, with one normalized coefficient list shared across all original valid inputs. -/
theorem secp256k1EEAForwardWrapper_reversePostprocessing_coherent :
    CoherentlyImplementsOn (secp256k1EEAForwardWrapper.seq secp256k1EEAReversePostprocessing)
      (Finsupp.lmapDomain ℂ ℂ (fun s => Classical.run
        (secp256k1EEAForwardUnitary indexedStepProductionRegisters) (eeaPreprocessIdealState s)))
      Secp256k1EEAInputValid := by
  have hc := coherent_basis_seq secp256k1EEAForwardWrapper_coherent
    secp256k1EEAReversePostprocessing_coherent (by
      intro s hs
      have h := (secp256k1EEAOutputIdealState_correct s hs.1 hs.2.1 hs.2.2).2.2.2.2
      exact ⟨h 560 (by decide),h 561 (by decide),h 562 (by decide)⟩)
  apply hc.congrIdeal
  intro s hs
  simp only [basisLift_ket]
  exact congrArg ket (secp256k1EEAReversePostprocessing_output s hs)

end

attribute [local irreducible] eeaPreprocessIdealState eeaUnpreprocessIdealState eeaUnpreprocess

/-- Reverse preprocessing is coherent on the actual image of valid original inputs. -/
theorem eeaUnpreprocess_coherent :
    CoherentlyImplementsOn eeaUnpreprocess
      (Finsupp.lmapDomain ℂ ℂ eeaUnpreprocessIdealState)
      (fun s => ∃ original, Secp256k1EEAInputValid original ∧ s = eeaPreprocessIdealState original) := by
  let witness : BasisState := fun w => decide (w = 263)
  have hw : boolWordToNat (wireValues (List.range' 263 256) witness) = 1 := by decide +kernel
  have hv : Secp256k1EEAInputValid witness := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hm
      dsimp only [witness]
      dsimp only [Wire] at *
      simp only [List.mem_append, List.mem_range', Nat.one_mul] at hm
      simp [show w ≠ (263 : Nat) by
        intro he
        subst w
        norm_num at hm
        obtain ⟨i,hi,he⟩ := hm
        omega]
    · rw [hw]; omega
    · rw [hw]; decide
  apply coherent_of_basis_branches eeaUnpreprocess eeaUnpreprocessIdealState _
    (fun b => registerXResetMagnitude b.history.length) eeaUnpreprocess_wellFormed
    (eeaPreprocessIdealState witness) ⟨witness,hv,rfl⟩
  intro b hb s hs
  obtain ⟨original,ho,rfl⟩ := hs
  rw [eeaUnpreprocessIdealState_after_preprocess original ho.1 ho.2.1 ho.2.2]
  exact eeaUnpreprocess_after_preprocess original ho.1 ho.2.1 ho.2.2 b hb

/-- Preprocessing followed by its explicit source reverse preserves every valid superposition. -/
theorem eeaPreprocess_unpreprocess_coherent :
    CoherentlyImplementsOn (eeaPreprocess.seq eeaUnpreprocess)
      (Finsupp.lmapDomain ℂ ℂ (fun s : BasisState => s)) Secp256k1EEAInputValid := by
  have hp := coherent_basis_strengthen preprocess_basis_coherent
    (Stronger := Secp256k1EEAInputValid) (fun _ hs => hs.1)
  have hall := coherent_basis_seq hp eeaUnpreprocess_coherent
    (fun s hs => ⟨s,hs,rfl⟩)
  apply hall.congrIdeal
  intro s hs
  rw [basisLift_ket,basisLift_ket,
    eeaUnpreprocessIdealState_after_preprocess s hs.1 hs.2.1 hs.2.2]

end ShorECDLP.Paper2607_13816
