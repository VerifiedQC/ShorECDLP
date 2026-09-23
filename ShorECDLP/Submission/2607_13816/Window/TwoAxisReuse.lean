import ShorECDLP.Submission.«2607_13816».Window.TwoAxisHoist
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- Ending the first axis does not pass its Fourier feedback into the second. -/
theorem streamAxis_tail_run (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit) :
    (streamAxis calls prior tail).run = (streamAxis calls prior .done).run.seq tail.run := by
  induction calls generalizing prior with
  | nil => simp [streamAxis, AdaptiveCircuit.run, Instrument.seq, InstrumentBranch.seq]
  | cons call calls ih =>
    rw [streamAxis_cons_block_run, streamAxis_cons_block_run]
    simp only [ih, Instrument.seq, List.flatMap_assoc, List.flatMap_map, List.map_flatMap, List.map_map]
    apply List.flatMap_congr
    intro b hb
    apply List.flatMap_congr
    intro c hc
    apply List.map_congr_left
    intro d hd
    cases b; cases c; cases d
    simp only [Function.comp_def, InstrumentBranch.seq, List.append_assoc]
    rfl

/-- Compose two physical axes with distinct logical allocations. Reuse is applied
before preparation, so its clean-bank assumptions are not imposed on Hadamard outputs. -/
theorem indexedTwoAxis_reuse (left right : List AdaptiveCircuit) (lp rp : List Bool)
    (tail : AdaptiveCircuit) (startL startR : Nat) (hL : 0 < startL) (hR : 0 < startR)
    (hl : ∀ c ∈ left, c.wires ⊆ streamAllocation)
    (hr : ∀ c ∈ right, c.wires ⊆ streamAllocation)
    (ψ : State) (hs : SupportedOn (Clean streamAddress) ψ)
    (hbL : ∀ k, startL ≤ k → k < startL + left.length → SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ)
    (hbR : ∀ k, startR ≤ k → k < startR + right.length → SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ) :
    (streamAxis left lp (streamAxis right rp tail)).run.map (fun b => (b.history, b.kraus ψ)) =
    ((relocatedStreamAxis (indexedStreamCalls startL left) lp .done).seq
      (relocatedStreamAxis (indexedStreamCalls startR right) rp tail)).map (fun b => (b.history, b.kraus ψ)) := by
  rw [streamAxis_tail_run]
  have he := indexedStreamAxis_run startL hL left lp .done hl ψ hs hbL
  have ht := congrArg (fun es : List (List Bool × State) => es.flatMap (fun e =>
    (relocatedStreamAxis (indexedStreamCalls startR right) rp tail).map
      (fun b => (e.1 ++ b.history, b.kraus e.2)))) he
  simp only [List.flatMap_map] at ht
  simp only [Instrument.seq, List.map_flatMap, List.map_map, Function.comp_def,
    InstrumentBranch.seq, LinearMap.comp_apply]
  rw [ht]
  apply List.flatMap_congr
  intro b hbm
  have hs' := streamAxis_clean left lp .done
    (by
      intro c hc φ hφ
      simp only [AdaptiveCircuit.run, List.mem_singleton] at hc
      subst c
      exact hφ)
    b hbm ψ hs
  have hbR' : ∀ k, startR ≤ k → k < startR + right.length →
      SupportedOn (Clean (List.range' (windowBankStart k) 16)) (b.kraus ψ) := by
    intro k hk hkl s hss w hw
    apply (streamAxis left lp .done).branch_frame w false _ b hbm ψ _ s hss
    · intro hmem
      have hw' := streamAxis_support left lp .done hl (by simp [AdaptiveCircuit.wires]) hmem
      simp only [streamAllocation, streamAddress, List.mem_append, List.mem_range,
        List.mem_range'_1, windowBankStart] at hw hw'
      dsimp only [Wire] at *
      omega
    · intro s hss
      exact hbR k hk hkl s hss w hw
  have hright := indexedStreamAxis_run startR hR right rp tail hr (b.kraus ψ) hs' hbR'
  have h := congrArg (List.map (fun e : List Bool × State => (b.history ++ e.1, e.2))) hright
  simpa only [List.map_map, Function.comp_def] using h.symm
/-- Prepare both disjoint logical axes at entry to the same physical two-axis
execution. The right axis starts with its own history, not the left transcript. -/
theorem indexedTwoAxis_prepared (left right : List AdaptiveCircuit) (lp rp : List Bool)
    (tail : AdaptiveCircuit) (startL startR : Nat) (hL : 0 < startL) (hR : 0 < startR)
    (hsep : startL + left.length ≤ startR)
    (hl : ∀ c ∈ left, c.wires ⊆ streamAllocation)
    (hr : ∀ c ∈ right, c.wires ⊆ streamAllocation)
    (ψ : State) (hs : SupportedOn (Clean streamAddress) ψ)
    (hbL : ∀ k, startL ≤ k → k < startL + left.length → SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ)
    (hbR : ∀ k, startR ≤ k → k < startR + right.length → SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ) :
    (streamAxis left lp (streamAxis right rp tail)).run.map (fun b => (b.history, b.kraus ψ)) =
    ((unpreparedStreamAxis (indexedStreamCalls startL left) lp .done).seq
      (unpreparedStreamAxis (indexedStreamCalls startR right) rp tail)).map
        (fun b => (b.history, b.kraus (Quantum.run
          (((streamPreparationWires (indexedStreamCalls startL left)) ++
            streamPreparationWires (indexedStreamCalls startR right)).map Gate.H) ψ))) := by
  rw [indexedTwoAxis_reuse left right lp rp tail startL startR hL hR hl hr ψ hs hbL hbR]
  apply relocatedTwoAxis_hoist
  · simp only [indexedStreamCalls, List.map_map, Function.comp_def, Prod.fst_swap, List.zipIdx_map_snd]
    exact List.nodup_range'
  · simp only [indexedStreamCalls, List.map_map, Function.comp_def, Prod.fst_swap, List.zipIdx_map_snd]
    exact List.nodup_range'
  · intro c hc d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
    have hai := List.mem_zipIdx ha
    have hbi := List.mem_zipIdx hb
    dsimp
    omega
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    apply hl a.1
    have h := List.mem_map_of_mem (f := Prod.fst) ha
    rwa [List.zipIdx_map_fst] at h
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    apply hr a.1
    have h := List.mem_map_of_mem (f := Prod.fst) ha
    rwa [List.zipIdx_map_fst] at h
end
end ShorECDLP.Paper2607_13816
