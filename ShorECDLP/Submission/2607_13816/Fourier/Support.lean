import ShorECDLP.Submission.«2607_13816».Fourier.Semiclassical
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem supported_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ+φ) := by
  intro s hs
  by_cases hp : ψ s=0
  · apply hφ s
    simpa [Finsupp.add_apply,hp] using hs
  · exact hψ s hp
private theorem supported_smul {V : BasisState → Prop} {ψ : State}
    (hψ : SupportedOn V ψ) (c : ℂ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])
theorem fourierBranch_supported (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (V : BasisState → Prop) (hclear : ∀ s,V s → V (fourierClear ws s))
    (ψ : State) (hψ : SupportedOn V ψ) : SupportedOn V (fourierBranch dir ws prior bs ψ) := by
  induction ψ using Finsupp.induction with
  | zero => simp
  | @single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hv : V s := hψ s (by simp [hz,hc])
    have ht : SupportedOn V ψ := by
      intro t hn
      apply hψ t
      by_cases he : t=s
      · subst t; exact (hn hz).elim
      · simpa [Ne.symm he] using hn
    have he : Finsupp.single s c=c • ket s := by simp [ket]
    rw [map_add,he,map_smul,fourierBranch_ket]
    exact supported_add (supported_smul (supported_smul
      (supportedOn_ket V _ (hclear s hv)) _) _) (ih ht)
end
end ShorECDLP.Paper2607_13816
