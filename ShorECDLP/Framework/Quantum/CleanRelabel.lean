import ShorECDLP.Framework.Quantum.Relabel
namespace ShorECDLP.Quantum
open Classical Quantum
noncomputable section
theorem relabelBasis_clean (e : Wire ≃ Wire) (S : List Wire)
    (he : ∀ w,e.symm w≠w → w∈S ∧ e.symm w∈S)
    (s : BasisState) (hs : Clean S s) : relabelBasis e s=s := by
  funext w
  change s (e.symm w)=s w
  by_cases h : e.symm w=w
  · rw [h]
  · rw [hs _ (he w h).1,hs _ (he w h).2]
theorem relabelState_clean (e : Wire ≃ Wire) (S : List Wire)
    (he : ∀ w,e.symm w≠w → w∈S ∧ e.symm w∈S)
    (ψ : State) (hψ : SupportedOn (Clean S) ψ) : relabelState e ψ=ψ := by
  induction ψ using Finsupp.induction with
  | zero => simp
  | @single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hv : Clean S s := hψ s (by simp [hz,hc])
    have ht : SupportedOn (Clean S) ψ := by
      intro t hn
      apply hψ t
      by_cases h : t=s
      · subst t; exact (hn hz).elim
      · simpa [Ne.symm h] using hn
    have hsingle : Finsupp.single s c=c • ket s := by simp [ket]
    rw [map_add,hsingle,map_smul,relabelState_ket,relabelBasis_clean e S he s hv,ih ht]
theorem branch_relabel_clean (e : Wire ≃ Wire) (S : List Wire)
    (he : ∀ w,e.symm w≠w → w∈S ∧ e.symm w∈S)
    (he' : ∀ w,e w≠w → w∈S ∧ e w∈S)
    (b : InstrumentBranch) (ψ : State)
    (hin : SupportedOn (Clean S) ψ) (hout : SupportedOn (Clean S) (b.kraus ψ)) :
    (b.relabel e).kraus ψ=b.kraus ψ := by
  change relabelState e (b.kraus (relabelState e.symm ψ))=b.kraus ψ
  rw [relabelState_clean e.symm S he' ψ hin,relabelState_clean e S he _ hout]
end
end ShorECDLP.Quantum
