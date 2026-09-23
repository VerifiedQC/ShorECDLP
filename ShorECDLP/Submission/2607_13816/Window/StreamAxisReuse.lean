import ShorECDLP.Submission.«2607_13816».Window.StreamHistory
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- Execute each measured block on its assigned logical bank. This is an
interleaved instrument, not the simultaneously prepared logical reference state.
Only the final sixteen records of each block advance Fourier feed-forward. -/
def relocatedStreamAxis : List (Nat × AdaptiveCircuit) → List Bool → AdaptiveCircuit → Instrument
  | [], _, tail => tail.run
  | (k, call) :: calls, prior, tail =>
    ((measuredStreamBlock call prior).relabel (streamBankPerm k)).run.flatMap (fun b =>
      (relocatedStreamAxis calls (b.history.reverse.take 16 ++ prior) tail).map
        (InstrumentBranch.seq b))

/-- Entire-axis bank reuse preserves ordered histories and unnormalized states.
All assigned banks must initially be clean; they need not be pairwise distinct.
The arbitrary tail is retained without any extra condition on its behavior. -/
theorem relocatedStreamAxis_run (calls : List (Nat × AdaptiveCircuit))
    (prior : List Bool) (tail : AdaptiveCircuit)
    (hk : ∀ c ∈ calls, c.1 ≠ 0)
    (hc : ∀ c ∈ calls, ∀ w ∈ c.2.wires, w < 839 ∨ w ∈ streamAddress)
    (ψ : State) (hs : SupportedOn (Clean streamAddress) ψ)
    (hb : ∀ c ∈ calls, SupportedOn (Clean (List.range' (windowBankStart c.1) 16)) ψ) :
    (relocatedStreamAxis calls prior tail).map (fun b => (b.history, b.kraus ψ)) =
      (streamAxis (calls.map Prod.snd) prior tail).run.map (fun b => (b.history, b.kraus ψ)) := by
  induction calls generalizing prior ψ with
  | nil => rfl
  | cons c calls ih =>
    rcases c with ⟨k, call⟩
    have hk0 := hk (k, call) (by simp)
    have hc0 := hc (k, call) (by simp)
    have hin : SupportedOn (Clean (streamAddress ++ List.range' (windowBankStart k) 16)) ψ := by
      intro s h w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hs s h w hw
      · exact hb (k, call) (by simp) s h w hw
    have he := measuredStreamBlock_relabel_run call prior k hk0 hc0 ψ hin
    have hsub := congrArg (fun entries : List (List Bool × State) =>
      entries.flatMap (fun entry =>
        (relocatedStreamAxis calls (entry.1.reverse.take 16 ++ prior) tail).map
          (fun next => (entry.1 ++ next.history, next.kraus entry.2)))) he
    simp only [List.map_cons, streamAxis_cons_block_run, relocatedStreamAxis,
      List.map_flatMap, List.map_map, Function.comp_def, InstrumentBranch.seq,
      LinearMap.comp_apply]
    simp only [List.flatMap_map] at hsub
    rw [hsub]
    apply List.flatMap_congr
    intro b hmem
    have hs' := measuredStreamBlock_clean call prior b hmem ψ
    have hb' : ∀ c ∈ calls, SupportedOn (Clean (List.range' (windowBankStart c.1) 16)) (b.kraus ψ) := by
      intro c hcm
      exact measuredStreamBlock_parked_clean call prior c.1 (hk c (by simp [hcm])) hc0 b hmem ψ
        (hb c (by simp [hcm]))
    have ht := ih (b.history.reverse.take 16 ++ prior)
      (fun c hcm => hk c (by simp [hcm]))
      (fun c hcm => hc c (by simp [hcm])) (b.kraus ψ) hs' hb'
    have hh := congrArg (List.map (fun entry : List Bool × State => (b.history ++ entry.1, entry.2))) ht
    simpa only [List.map_map, Function.comp_def] using hh
end
end ShorECDLP.Paper2607_13816
