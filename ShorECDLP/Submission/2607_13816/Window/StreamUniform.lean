import ShorECDLP.Submission.«2607_13816».Window.StreamScalarWord
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem hadamards_perm (ws vs : List Wire) (hp : ws.Perm vs) (ψ : State) :
    Quantum.run (ws.map Gate.H) ψ = Quantum.run (vs.map Gate.H) ψ := by
  induction hp generalizing ψ with
  | nil => rfl
  | cons w h ih => simpa only [List.map_cons,run_cons] using ih (applyGate (.H w) ψ)
  | swap a b l =>
    simp only [List.map_cons,run_cons]
    by_cases h : a=b
    · subst b; rfl
    · rw [applyGate_H_commute (.H a) b (by simpa [gateWires] using Ne.symm h)]
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ ψ).trans (ih₂ ψ)
theorem streamPreparedEntry_uniform (P Q : Point) : streamPreparedEntry P Q =
    (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) •
      phaseUniformSum ((streamScalarWires 16 1).reverse ++ (streamScalarWires 13 17).reverse)
        (scalarRootFlip zeroBasisState) := by
  rw [streamPreparedEntry,streamRawPreparation_eq]
  have hp : (List.range' 871 464 : List Wire).Perm
      ((streamScalarWires 16 1).reverse ++ (streamScalarWires 13 17).reverse) := by decide +kernel
  rw [hadamards_perm _ _ hp,phaseHadamards_uniform _ (by decide +kernel)]
  · rw [← hp.length_eq,List.length_range']
  · intro w hw
    have hm := hp.mem_iff.mpr hw
    simp only [List.mem_range'_1] at hm
    have hn : w≠836 := by dsimp only [Wire] at *; omega
    simp [scalarRootFlip,upd,hn,zeroBasisState]

end
end ShorECDLP.Paper2607_13816
