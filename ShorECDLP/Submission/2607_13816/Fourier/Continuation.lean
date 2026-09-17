import ShorECDLP.Submission.«2607_13816».Fourier.Semiclassical
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- Fourier measurement with a continuation receiving all prior outcomes in reverse order. -/
def fourierContinue (dir : PhaseDir) : List Wire → List Bool → (List Bool → AdaptiveCircuit) → AdaptiveCircuit
  | [], prior, next => next prior
  | w::ws, prior, next => .unitary (fourierHistoryRotations dir w prior 2)
      (.xMeasureReset w (fourierContinue dir ws (false::prior) next)
        (fourierContinue dir ws (true::prior) next))

theorem fourierContinue_done (dir : PhaseDir) (ws : List Wire) (prior : List Bool) :
    fourierContinue dir ws prior (fun _ => .done)=semiclassicalFourier dir ws prior := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih => simp only [fourierContinue,semiclassicalFourier,ih]

theorem fourierContinue_append (dir : PhaseDir) (xs ys : List Wire) (prior : List Bool)
    (next : List Bool → AdaptiveCircuit) :
    fourierContinue dir (xs++ys) prior next=
      fourierContinue dir xs prior (fun history => fourierContinue dir ys history next) := by
  induction xs generalizing prior with
  | nil => rfl
  | cons w ws ih => simp only [List.cons_append,fourierContinue,ih]

/-- Splitting into windows preserves the actual circuit, including cross-window feed-forward. -/
theorem semiclassicalFourier_append (dir : PhaseDir) (xs ys : List Wire) (prior : List Bool) :
    semiclassicalFourier dir (xs++ys) prior=
      fourierContinue dir xs prior (fun history => semiclassicalFourier dir ys history) := by
  rw [←fourierContinue_done, fourierContinue_append]
  simp only [fourierContinue_done]

theorem fourierContinue_run (dir : PhaseDir) (ws : List Wire) (prior : List Bool)
    (next : List Bool → AdaptiveCircuit) :
    (fourierContinue dir ws prior next).run=
      (fourierOutcomes ws.length).flatMap (fun bs =>
        ((next (bs.reverse++prior)).run.map (fun b =>
          InstrumentBranch.seq ⟨bs,fourierBranch dir ws prior bs⟩ b))) := by
  induction ws generalizing prior with
  | nil => simp [fourierContinue,fourierOutcomes,fourierBranch,InstrumentBranch.seq]
  | cons w ws ih =>
    simp only [fourierContinue,AdaptiveCircuit.run,ih,List.length_cons,fourierOutcomes,
      List.flatMap_append,List.flatMap_map,List.map_append,List.map_flatMap,List.map_map]
    congr 1 <;> apply List.flatMap_congr <;> intro bs hbs
    all_goals
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      apply List.map_congr_left
      intro b hb
      cases b
      simp [InstrumentBranch.seq,fourierBranch]
      rfl
private theorem history_support (dir : PhaseDir) (w : Wire) (prior : List Bool) (k : Nat) :
    circuitWires (fourierHistoryRotations dir w prior k) ⊆ [w] := by
  induction prior generalizing k with
  | nil => simp [fourierHistoryRotations,circuitWires]
  | cons b bs ih =>
    cases b <;> simpa [fourierHistoryRotations,fourierFeedForward,circuitWires,gateWires] using ih (k+1)

theorem fourierContinue_support (dir : PhaseDir) (ws : List Wire) (prior : List Bool)
    (next : List Bool → AdaptiveCircuit) (allocation : List Wire)
    (hw : ws ⊆ allocation) (hn : ∀ h, (next h).wires ⊆ allocation) :
    (fourierContinue dir ws prior next).wires ⊆ allocation := by
  induction ws generalizing prior with
  | nil => exact hn prior
  | cons w ws ih =>
    intro v hv
    simp only [fourierContinue,AdaptiveCircuit.wires,List.mem_append,List.mem_cons] at hv
    rcases hv with hv | rfl | hv | hv
    · have he := history_support dir w prior 2 hv
      have hvw : v=w := by simpa using he
      exact hw (by simp [hvw])
    · exact hw (by simp)
    · exact ih _ (by intro q hq; exact hw (by simp [hq])) hv
    · exact ih _ (by intro q hq; exact hw (by simp [hq])) hv

theorem fourierContinue_measurements (dir : PhaseDir) (ws : List Wire) (prior : List Bool)
    (next : List Bool → AdaptiveCircuit) (m : Nat)
    (hm : ∀ h, (next h).measurementCount=m) :
    (fourierContinue dir ws prior next).measurementCount=ws.length+m := by
  induction ws generalizing prior with
  | nil => simpa [fourierContinue] using hm prior
  | cons w ws ih => simp [fourierContinue,AdaptiveCircuit.measurementCount,ih,Nat.add_assoc,Nat.add_comm]

end
end ShorECDLP.Paper2607_13816
