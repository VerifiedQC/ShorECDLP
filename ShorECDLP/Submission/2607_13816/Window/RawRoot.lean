import ShorECDLP.Submission.«2607_13816».Window.RawTerminal
import ShorECDLP.Submission.«2607_13816».Fourier.Commutation
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] reducedFourierProgram

/-- Root setup is exactly the basis permutation, on arbitrary states. -/
theorem scalarRootFlip_run (ψ : State) :
    Quantum.run [.X 836] ψ=Finsupp.lmapDomain ℂ ℂ scalarRootFlip ψ := by
  induction ψ using Finsupp.induction with
  | zero => simp
  | @single_add s a ψ hs ha ih =>
    have he : Finsupp.single s a=a • ket s := by simp [ket]
    simp only [map_add, he, map_smul, ih]
    have hk := Quantum.run_ket_agrees_classical [.X 836] s (by simp [HPFree])
    have hm : Finsupp.lmapDomain ℂ ℂ scalarRootFlip (ket s)=ket (scalarRootFlip s) := by simp [ket]
    rw [hm]
    congr 2

theorem scalarRootFlip_normSq (ψ : State) :
    normSq (Finsupp.lmapDomain ℂ ℂ scalarRootFlip ψ)=normSq ψ := by
  rw [←scalarRootFlip_run]
  exact normSq_run _ (by simp [CircuitWellFormed, Gate.WellFormed]) ψ

/-- The physical scalar output ignores the root control when reading both input registers. -/
theorem reducedScalarOutput_root (P Q : Point) (s : BasisState) :
    reducedScalarOutput P Q (scalarRootFlip s)=scalarRootFlip (reducedScalarOutput P Q s) := by
  simp only [reducedScalarOutput, scalarRootFlip_register, scalarRootFlip_pointWrite]

theorem reducedScalarMap_root (P Q : Point) (ψ : State) :
    Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q) (Finsupp.lmapDomain ℂ ℂ scalarRootFlip ψ)=
    Finsupp.lmapDomain ℂ ℂ scalarRootFlip (Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q) ψ) := by
  induction ψ using Finsupp.induction with
  | zero => simp
  | @single_add s a ψ hs ha ih =>
    simp only [map_add, ih]
    congr 1
    simp [reducedScalarOutput_root]

/-- A root flip outside a Fourier bank commutes with every actual measurement branch. -/
theorem fourierBranch_root (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (h : 836 ∉ ws) (ψ : State) :
    fourierBranch dir ws prior bs (Finsupp.lmapDomain ℂ ℂ scalarRootFlip ψ)=
    Finsupp.lmapDomain ℂ ℂ scalarRootFlip (fourierBranch dir ws prior bs ψ) := by
  apply fourierBranch_mapDomain_commute
  · intro w hw s
    have hn : w≠836 := by intro he; subst w; exact h hw
    simp [scalarRootFlip, upd, hn]
  · intro w hw s
    have hn : w≠836 := by intro he; subst w; exact h hw
    funext v
    simp only [scalarRootFlip, upd]
    split_ifs <;> simp_all

private theorem slice_root (a b : List Bool) (ψ : State) :
    (reducedFourierSlice a b).bornMass (Finsupp.lmapDomain ℂ ℂ scalarRootFlip ψ)=
    (reducedFourierSlice a b).bornMass ψ := by
  simp only [reducedFourierSlice, Instrument.bornMass, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, LinearMap.comp_apply]
  rw [fourierBranch_root _ _ _ _ (by decide +kernel),
    fourierBranch_root _ _ _ _ (by decide +kernel), scalarRootFlip_normSq]

/-- Root setup does not change the probability of any selected Fourier transcript event. -/
theorem reducedFourierSelection_root (accept : List Bool × List Bool → Bool) (ψ : State) :
    (reducedFourierSelection accept).bornMass (Finsupp.lmapDomain ℂ ℂ scalarRootFlip ψ)=
    (reducedFourierSelection accept).bornMass ψ := by
  have hb (b : InstrumentBranch) (h : b∈reducedFourierProgram.run) :
      normSq (b.kraus (Finsupp.lmapDomain ℂ ℂ scalarRootFlip ψ))=normSq (b.kraus ψ) := by
    rw [reducedFourierProgram_run] at h
    obtain ⟨a, _, hb'⟩ := List.mem_flatMap.mp h
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hb'
    simp only [reducedFourierSlice, List.mem_singleton] at hc
    subst b
    simpa only [reducedFourierSlice, Instrument.bornMass, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] using slice_root a c ψ
  unfold Instrument.bornMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb'
  exact hb b ((List.mem_filter.mp hb').1)

/-- Remove root setup from the full ideal acceptance probability, without changing arithmetic. -/
theorem reducedRawIdealFourierEventMass_root (P Q : Point) (accept : List Bool × List Bool → Bool) :
    reducedRawIdealFourierEventMass P Q accept =
      (reducedFourierSelection accept).bornMass
        (Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)
          (Quantum.run reducedPhasePrepare (ket zeroBasisState))) := by
  unfold reducedRawIdealFourierEventMass reducedRawEntryState
  rw [scalarRootFlip_run, reducedScalarMap_root, reducedFourierSelection_root]
end
end ShorECDLP.Paper2607_13816
