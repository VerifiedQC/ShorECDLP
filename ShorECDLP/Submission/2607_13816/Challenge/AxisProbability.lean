import ShorECDLP.Submission.«2607_13816».Challenge.TaggedProbability
import ShorECDLP.Submission.«2607_13816».Challenge.WindowValidity
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

noncomputable def selectedSourceAxis (call : OddWindow → AdaptiveCircuit) :
    List OddWindow → List Bool → (List Bool → Instrument) → Instrument
  | [], prior, terminal => terminal prior
  | w :: ws, prior, terminal =>
      streamBlockContinuation (call w) prior
        (fun bits => selectedSourceAxis call ws (bits.reverse ++ prior) terminal)

noncomputable def selectedIdealAxis (Q : Point) :
    List OddWindow → List Bool → (List Bool → Instrument) → Instrument
  | [], prior, terminal => terminal prior
  | w :: ws, prior, terminal =>
      (fourierContinuationInstrument prior
        (fun bits => selectedIdealAxis Q ws (bits.reverse ++ prior) terminal)).map
        (fun b => InstrumentBranch.seq
          ⟨[], (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)).comp
            (Quantum.run (streamAddress.map Gate.H))⟩ b)

theorem selectedIdealAxis_cons_mass (Q : Point) (w : OddWindow) (ws : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) (ψ : State) :
    (selectedIdealAxis Q (w :: ws) prior terminal).bornMass ψ =
      (fourierContinuationInstrument prior
        (fun bits => selectedIdealAxis Q ws (bits.reverse ++ prior) terminal)).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
  simp only [selectedIdealAxis,Instrument.bornMass,List.map_map,Function.comp_def,
    InstrumentBranch.seq,LinearMap.comp_apply]

/-- All arithmetic records may be summed out, including before an arbitrary selected terminal event. -/
theorem selectedSourceAxis_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (call : OddWindow → AdaptiveCircuit) (ws : List OddWindow)
    (hcall : ∀ w ∈ ws, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
    (prior : List Bool) (terminal : List Bool → Instrument)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedSourceAxis call ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal).bornMass ψ := by
  induction ws generalizing prior ψ with
  | nil => rfl
  | cons w ws ih =>
    rw [selectedSourceAxis,streamBlockContinuation_mass (hcall w (by simp)) _ _ _
      (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ),selectedIdealAxis_cons_mass]
    apply fourierContinuationInstrument_mass_congr
    intro bits hbits
    apply ih (fun v hv => hcall v (List.mem_cons_of_mem w hv))
    apply batchedWindowValid_fourierBranch
    · intro v hv
      simpa only [List.mem_reverse] using hv
    · exact actualBatchedWindowState_supported Q hQ hn w _
        (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ)


theorem selectedSourceAxis_constant (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow) (prior : List Bool) (tail : AdaptiveCircuit) :
    selectedSourceAxis call ws prior (fun _ => tail.run) =
      (streamAxis (ws.map call) prior tail).run := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih =>
    simp only [selectedSourceAxis,List.map_cons,streamAxis_cons_run,
      streamBlockContinuation,ih]
end ShorECDLP.Paper2607_13816.ChallengeMigration
