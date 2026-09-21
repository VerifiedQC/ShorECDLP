import ShorECDLP.Framework.Quantum.Relabel
import ShorECDLP.Submission.«2607_13816».Fourier.Continuation
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
theorem fourierHistoryRotations_relabel (e : Wire ≃ Wire) (dir : PhaseDir) (w : Wire)
    (prior : List Bool) (k : Nat) :
    (fourierHistoryRotations dir w prior k).map (Gate.relabel e)=fourierHistoryRotations dir (e w) prior k := by
  induction prior generalizing k with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [fourierHistoryRotations,fourierFeedForward,ih,Gate.relabel]
theorem semiclassicalFourier_relabel (e : Wire ≃ Wire) (dir : PhaseDir)
    (ws : List Wire) (prior : List Bool) :
    (semiclassicalFourier dir ws prior).relabel e=semiclassicalFourier dir (ws.map e) prior := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih => simp only [semiclassicalFourier,AdaptiveCircuit.relabel,
      fourierHistoryRotations_relabel,List.map_cons,ih]
theorem fourierContinue_relabel (e : Wire ≃ Wire) (dir : PhaseDir)
    (ws : List Wire) (prior : List Bool) (next : List Bool → AdaptiveCircuit) :
    (fourierContinue dir ws prior next).relabel e=
      fourierContinue dir (ws.map e) prior (fun h => (next h).relabel e) := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih => simp only [fourierContinue,AdaptiveCircuit.relabel,
      fourierHistoryRotations_relabel,List.map_cons,ih]
end
end ShorECDLP.Paper2607_13816
