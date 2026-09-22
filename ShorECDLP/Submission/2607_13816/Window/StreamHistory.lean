import ShorECDLP.Submission.«2607_13816».Window.StreamContinuation
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq fourierContinue
/-- A complete block with its Fourier outcomes distinguished from arithmetic outcomes.
The first component alone advances the classical Fourier history. -/
def streamBlockOutcomes (call : AdaptiveCircuit) (prior : List Bool) :
    List (List Bool × InstrumentBranch) :=
  (((AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).seq call).run).flatMap
    (fun a => (fourierOutcomes streamAddress.length).map
      (fun bs => (bs, InstrumentBranch.seq a
        ⟨bs, fourierBranch .inverse streamAddress.reverse prior bs⟩)))
/-- Forgetting the Fourier tag gives the actual block instrument, with ordering and
multiplicity intact. -/
theorem streamBlockOutcomes_run (call : AdaptiveCircuit) (prior : List Bool) :
    (streamBlockOutcomes call prior).map Prod.snd = (measuredStreamBlock call prior).run := by
  simp only [streamBlockOutcomes, measuredStreamBlock, AdaptiveCircuit.run_seq, Instrument.seq,
    semiclassicalFourier_run, List.length_reverse, List.map_flatMap, List.map_map,
    Function.comp_def]
/-- Exact continuation rule: internal arithmetic outcomes remain in the complete
transcript, but never enter the history used for Fourier feed-forward. -/
theorem streamAxis_cons_run (call : AdaptiveCircuit) (calls : List AdaptiveCircuit)
    (prior : List Bool) (tail : AdaptiveCircuit) :
    (streamAxis (call :: calls) prior tail).run =
      (streamBlockOutcomes call prior).flatMap (fun tagged =>
        (streamAxis calls (tagged.1.reverse ++ prior) tail).run.map
          (InstrumentBranch.seq tagged.2)) := by
  simp only [streamAxis, streamBlockOutcomes, AdaptiveCircuit.run_seq, Instrument.seq,
    fourierContinue_run, List.length_reverse, List.flatMap_map,
    List.flatMap_assoc, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro h hh
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro bs hbs
  apply List.map_congr_left
  intro b hb
  cases h; cases a; cases b
  simp only [InstrumentBranch.seq, List.append_assoc]
  rfl
/-- The final sixteen measurement records are exactly the Fourier outcomes;
arithmetic records preceding them cannot contaminate the next Fourier history. -/
theorem streamBlockOutcomes_history (call : AdaptiveCircuit) (prior : List Bool)
    (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ streamBlockOutcomes call prior) :
    tagged.2.history.reverse.take 16 = tagged.1.reverse := by
  obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp ht
  have hl : bs.length = 16 := by
    simpa only [streamAddress, List.length_range'] using
      (fourierOutcomes_mem streamAddress.length bs).mp hbs
  simp only [InstrumentBranch.seq, List.reverse_append]
  rw [← hl, ← List.length_reverse (as := bs), List.take_left]
/-- Compose using the actual untagged block instrument. This is the boundary at
which exact block reuse can be substituted into a history-dependent suffix. -/
theorem streamAxis_cons_block_run (call : AdaptiveCircuit) (calls : List AdaptiveCircuit)
    (prior : List Bool) (tail : AdaptiveCircuit) :
    (streamAxis (call :: calls) prior tail).run =
      (measuredStreamBlock call prior).run.flatMap (fun b =>
        (streamAxis calls (b.history.reverse.take 16 ++ prior) tail).run.map
          (InstrumentBranch.seq b)) := by
  rw [streamAxis_cons_run, ← streamBlockOutcomes_run, List.flatMap_map]
  apply List.flatMap_congr
  intro tagged ht
  rw [streamBlockOutcomes_history call prior tagged ht]
/-- Evaluated block replacement remains valid through the entire remaining axis,
including its history-dependent Fourier choices and an arbitrary tail. -/
theorem streamAxis_cons_reuse_run (call : AdaptiveCircuit) (calls : List AdaptiveCircuit)
    (prior : List Bool) (tail : AdaptiveCircuit) (k : Nat) (hk : k ≠ 0)
    (hcall : ∀ w ∈ call.wires, w < 839 ∨ w ∈ streamAddress) (ψ : State)
    (hin : SupportedOn (Clean (streamAddress ++ List.range' (windowBankStart k) 16)) ψ) :
    ((streamAxis (call :: calls) prior tail).run.map (fun b => (b.history, b.kraus ψ))) =
      (((measuredStreamBlock call prior).relabel (streamBankPerm k)).run.flatMap
        (fun b => (streamAxis calls (b.history.reverse.take 16 ++ prior) tail).run.map
          (fun next => (b.history ++ next.history, next.kraus (b.kraus ψ))))) := by
  have he := measuredStreamBlock_relabel_run call prior k hk hcall ψ hin
  have hc := congrArg (fun entries : List (List Bool × State) =>
    entries.flatMap (fun entry =>
      (streamAxis calls (entry.1.reverse.take 16 ++ prior) tail).run.map
        (fun next => (entry.1 ++ next.history, next.kraus entry.2)))) he
  rw [streamAxis_cons_block_run]
  simpa only [List.map_flatMap, List.map_map, List.flatMap_map, Function.comp_def,
    InstrumentBranch.seq, LinearMap.comp_apply] using hc.symm
end
end ShorECDLP.Paper2607_13816
