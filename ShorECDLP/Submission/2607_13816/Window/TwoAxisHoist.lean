import ShorECDLP.Submission.«2607_13816».Window.StreamHoist
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- Preparations for a separate axis commute through every unprepared branch.
The tail must avoid those banks as well. -/
theorem unpreparedStreamAxis_future_commute (calls future : List (Nat × AdaptiveCircuit))
    (prior : List Bool) (tail : AdaptiveCircuit)
    (hc : ∀ c ∈ calls, c.2.wires ⊆ streamAllocation)
    (hd : ∀ c ∈ calls, ∀ d ∈ future, d.1 ≠ c.1)
    (ht : ∀ w ∈ streamPreparationWires future, w ∉ tail.wires)
    (b : InstrumentBranch) (hb : b ∈ unpreparedStreamAxis calls prior tail) (ψ : State) :
    b.kraus (Quantum.run ((streamPreparationWires future).map Gate.H) ψ) =
      Quantum.run ((streamPreparationWires future).map Gate.H) (b.kraus ψ) := by
  induction calls generalizing prior b ψ with
  | nil => exact tail.branch_hadamards_commute _ ht b hb ψ
  | cons c calls ih =>
    obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hb
    obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hm
    change next.kraus (a.kraus (Quantum.run _ ψ)) = Quantum.run _ (next.kraus (a.kraus ψ))
    rw [parkedStreamBody_future_commute c.2 c.1 prior (hc c (by simp)) future
      (hd c (by simp)) a ha,
      ih _ (by intro d hm; exact hc d (by simp [hm]))
        (by intro d hm; exact hd d (by simp [hm])) next hn]

/-- Two axes retain independent Fourier histories. Preparing both sets of
logical banks at entry preserves all arithmetic/Fourier records in order.
The final adaptive tail is arbitrary; no preparation is moved across it. -/
theorem relocatedTwoAxis_hoist (left right : List (Nat × AdaptiveCircuit))
    (lp rp : List Bool) (tail : AdaptiveCircuit)
    (hl : (left.map Prod.fst).Nodup) (hr : (right.map Prod.fst).Nodup)
    (hd : ∀ c ∈ left, ∀ d ∈ right, d.1 ≠ c.1)
    (hcl : ∀ c ∈ left, c.2.wires ⊆ streamAllocation)
    (hcr : ∀ c ∈ right, c.2.wires ⊆ streamAllocation) (ψ : State) :
    ((relocatedStreamAxis left lp .done).seq (relocatedStreamAxis right rp tail)).map
      (fun b => (b.history, b.kraus ψ)) =
    ((unpreparedStreamAxis left lp .done).seq (unpreparedStreamAxis right rp tail)).map
      (fun b => (b.history, b.kraus (Quantum.run
        (((streamPreparationWires left) ++ streamPreparationWires right).map Gate.H) ψ))) := by
  have he := relocatedStreamAxis_hoist left lp .done hl hcl ψ
  have ht := congrArg (fun es : List (List Bool × State) => es.flatMap (fun e =>
    (relocatedStreamAxis right rp tail).map (fun b => (e.1 ++ b.history, b.kraus e.2)))) he
  simp only [List.flatMap_map] at ht
  simp only [Instrument.seq, List.map_flatMap, List.map_map, Function.comp_def,
    InstrumentBranch.seq, LinearMap.comp_apply, List.map_append, run_append]
  rw [ht]
  apply List.flatMap_congr
  intro b hb
  have hright := relocatedStreamAxis_hoist right rp tail hr hcr
    (b.kraus (Quantum.run ((streamPreparationWires left).map Gate.H) ψ))
  have h := congrArg (List.map (fun e : List Bool × State => (b.history ++ e.1, e.2))) hright
  simp only [List.map_map, Function.comp_def] at h
  have hcomm := unpreparedStreamAxis_future_commute left right lp .done hcl hd
    (by intro w hw; exact List.not_mem_nil) b hb
    (Quantum.run ((streamPreparationWires left).map Gate.H) ψ)
  rw [← hcomm] at h
  exact h
end
end ShorECDLP.Paper2607_13816
