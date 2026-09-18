import ShorECDLP.Framework.Quantum.AdaptiveComposition
import ShorECDLP.Submission.«2607_13816».Window.StreamBlockClean
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq fourierContinue
theorem streamAxis_clean (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit)
    (ht : ∀ b∈tail.run,∀ ψ,SupportedOn (Clean streamAddress) ψ →
      SupportedOn (Clean streamAddress) (b.kraus ψ))
    (b : InstrumentBranch) (hb : b∈(streamAxis calls prior tail).run) (ψ : State)
    (hin : SupportedOn (Clean streamAddress) ψ) :
    SupportedOn (Clean streamAddress) (b.kraus ψ) := by
  induction calls generalizing prior b ψ with
  | nil => exact ht b hb ψ hin
  | cons call calls ih =>
    rw [streamAxis,AdaptiveCircuit.run_seq] at hb
    obtain ⟨h,hh,hm⟩ := List.mem_flatMap.mp hb
    obtain ⟨rest,hr,rfl⟩ := List.mem_map.mp hm
    rw [AdaptiveCircuit.run_seq] at hr
    obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hr
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hm
    rw [fourierContinue_run] at hf
    obtain ⟨bs,hbs,hm⟩ := List.mem_flatMap.mp hf
    obtain ⟨next,hn,rfl⟩ := List.mem_map.mp hm
    exact ih _ next hn _ (streamFourier_clean prior bs (a.kraus (h.kraus ψ)))
theorem streamAxis_singleton (call : AdaptiveCircuit) (prior : List Bool) :
    streamAxis [call] prior .done=measuredStreamBlock call prior := by
  simp only [streamAxis,fourierContinue_done,measuredStreamBlock,circuit_seq_assoc]
end
end ShorECDLP.Paper2607_13816
