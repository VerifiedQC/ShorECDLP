import ShorECDLP.Submission.«2607_13816».Challenge.ActualWindow
import ShorECDLP.Framework.Quantum.TerminalInterference
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] fourierOutcomes streamAddress

/-- A terminal instrument may depend on Fourier outcomes, but not erased arithmetic records. -/
noncomputable def fourierContinuationInstrument (prior : List Bool) (next : List Bool → Instrument) : Instrument :=
  (fourierOutcomes 16).flatMap (fun bits => (next bits).map
    (fun b => InstrumentBranch.seq ⟨bits,fourierBranch .inverse streamAddress.reverse prior bits⟩ b))

noncomputable def streamBlockContinuation (call : AdaptiveCircuit) (prior : List Bool)
    (next : List Bool → Instrument) : Instrument :=
  (streamBlockOutcomes call prior).flatMap (fun tagged => (next tagged.1).map (tagged.2.seq))

theorem streamBlockContinuation_eq (call : AdaptiveCircuit) (prior : List Bool)
    (next : List Bool → Instrument) :
    streamBlockContinuation call prior next =
      (AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).run.seq
        (call.run.seq (fourierContinuationInstrument prior next)) := by
  simp only [streamBlockContinuation,streamBlockOutcomes,AdaptiveCircuit.run_seq,
    Instrument.seq,fourierContinuationInstrument,
    show streamAddress.length=16 from by simp [streamAddress],
    List.flatMap_assoc,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro b hb
  apply List.flatMap_congr
  intro bits hbits
  apply List.map_congr_left
  intro c hc
  cases a; cases b; cases c
  simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem unitary_done_seq_bornMass (c : Circuit) (J : Instrument) (ψ : State) :
    ((AdaptiveCircuit.unitary c .done).run.seq J).bornMass ψ = J.bornMass (Quantum.run c ψ) := by
  simp only [AdaptiveCircuit.run,Instrument.seq,List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,
    List.append_nil,Instrument.bornMass,List.map_map,Function.comp_def,InstrumentBranch.seq,LinearMap.comp_apply]
  rfl

/-- Eliminate all arithmetic measurement branches before a Fourier-dependent continuation. -/
theorem streamBlockContinuation_mass {call : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop} (h : CoherentlyImplementsOn call ideal Valid)
    (prior : List Bool) (next : List Bool → Instrument) (ψ : State)
    (hs : SupportedOn Valid (Quantum.run (streamAddress.map Gate.H) ψ)) :
    (streamBlockContinuation call prior next).bornMass ψ =
      (fourierContinuationInstrument prior next).bornMass
        (ideal (Quantum.run (streamAddress.map Gate.H) ψ)) := by
  rw [streamBlockContinuation_eq]
  rw [unitary_done_seq_bornMass]
  exact h.terminalMass hs _


theorem fourierContinuationInstrument_mass (prior : List Bool)
    (next : List Bool → Instrument) (ψ : State) :
    (fourierContinuationInstrument prior next).bornMass ψ =
      ((fourierOutcomes 16).map (fun bits =>
        (next bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ))).sum := by
  simp only [fourierContinuationInstrument, Instrument.bornMass, List.map_flatMap,
    List.map_map, Function.comp_def, InstrumentBranch.seq,
    LinearMap.comp_apply]
  generalize fourierOutcomes 16 = outcomes
  induction outcomes with
  | nil => rfl
  | cons a outcomes ih => simpa only [List.flatMap_cons, List.sum_append,
      List.map_cons, List.sum_cons] using congrArg (_ + ·) ih

/-- A continuation replacement only needs equality on the reached Fourier states. -/
theorem fourierContinuationInstrument_mass_congr (prior : List Bool)
    (next next' : List Bool → Instrument) (ψ : State)
    (h : ∀ bits ∈ fourierOutcomes 16,
      (next bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ) =
      (next' bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ)) :
    (fourierContinuationInstrument prior next).bornMass ψ =
      (fourierContinuationInstrument prior next').bornMass ψ := by
  rw [fourierContinuationInstrument_mass, fourierContinuationInstrument_mass]
  congr 1
  exact List.map_congr_left h
end ShorECDLP.Paper2607_13816.ChallengeMigration
