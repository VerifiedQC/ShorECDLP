import ShorECDLP.Submission.«2607_13816».Fourier.Continuation
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem coeff_frame (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (f : BasisState → BasisState) (hbit : ∀ w∈ws,∀ s,f s w=s w)
    (hr : ∀ w∈ws,∀ s,f (s[w ↦ false])=(f s)[w ↦ false]) (s : BasisState) :
    fourierBranchCoeff dir ws prior bs (f s)=fourierBranchCoeff dir ws prior bs s := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [fourierBranchCoeff,hbit w (by simp),←hr w (by simp)]
      rw [ih (b::prior) bs (by intro v hv; exact hbit v (by simp [hv]))
        (by intro v hv; exact hr v (by simp [hv]))]
private theorem clear_frame (ws : List Wire) (f : BasisState → BasisState)
    (hr : ∀ w∈ws,∀ s,f (s[w ↦ false])=(f s)[w ↦ false]) (s : BasisState) :
    fourierClear ws (f s)=f (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    rw [fourierClear,←hr w (by simp),ih (by intro v hv; exact hr v (by simp [hv]))]
    rfl
/-- An ideal transformation independent of the measured wires commutes with each Fourier branch. -/
theorem fourierBranch_mapDomain_commute (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (f : BasisState → BasisState) (hbit : ∀ w∈ws,∀ s,f s w=s w)
    (hr : ∀ w∈ws,∀ s,f (s[w ↦ false])=(f s)[w ↦ false]) (ψ : State) :
    fourierBranch dir ws prior bs (Finsupp.lmapDomain ℂ ℂ f ψ)=
      Finsupp.lmapDomain ℂ ℂ f (fourierBranch dir ws prior bs ψ) := by
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s a ψ hs ha ih =>
    have he : Finsupp.single s a=a • ket s := by simp [ket]
    simp only [map_add,he,map_smul,ih]
    congr 1
    congr 1
    have hm (t : BasisState) : Finsupp.lmapDomain ℂ ℂ f (ket t)=ket (f t) := by simp [ket]
    rw [hm,fourierBranch_ket,fourierBranch_ket,map_smul,hm,
      coeff_frame dir ws prior bs f hbit hr s,clear_frame ws f hr s]
end
end ShorECDLP.Paper2607_13816
