import ShorECDLP.Submission.«2607_13816».Window.StreamPreparation
import ShorECDLP.Submission.«2607_13816».Window.RawAxisReuse
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- Arithmetic and Fourier measurement at one logical bank, without preparation. -/
def parkedStreamBody (call : AdaptiveCircuit) (k : Nat) (prior : List Bool) : AdaptiveCircuit :=
  (call.seq (semiclassicalFourier .inverse streamAddress.reverse prior)).relabel (streamBankPerm k)
/-- The entire axis with preparation removed; adaptive histories are unchanged. -/
def unpreparedStreamAxis : List (Nat × AdaptiveCircuit) → List Bool → AdaptiveCircuit → Instrument
  | [], _, tail => tail.run
  | (k, call) :: calls, prior, tail =>
    (parkedStreamBody call k prior).run.flatMap (fun b =>
      (unpreparedStreamAxis calls (b.history.reverse.take 16 ++ prior) tail).map (InstrumentBranch.seq b))
/-- All logical banks, in execution order. -/
def streamPreparationWires (calls : List (Nat × AdaptiveCircuit)) : List Wire :=
  calls.flatMap (fun c => List.range' (windowBankStart c.1) 16)

theorem measuredStreamBlock_split (call : AdaptiveCircuit) (k : Nat) (prior : List Bool) :
    (measuredStreamBlock call prior).relabel (streamBankPerm k) =
      .unitary ((List.range' (windowBankStart k) 16).map Gate.H) (parkedStreamBody call k prior) := by
  have hh : (streamAddress.map Gate.H).map (Gate.relabel (streamBankPerm k)) =
      (List.range' (windowBankStart k) 16).map Gate.H := by
    rw [← streamBankPerm_full k, List.map_map, List.map_map]
    rfl
  simp only [measuredStreamBlock, AdaptiveCircuit.seq, AdaptiveCircuit.relabel, parkedStreamBody, hh]

private theorem body_support (call : AdaptiveCircuit) (prior : List Bool)
    (hc : call.wires ⊆ streamAllocation) :
    (call.seq (semiclassicalFourier .inverse streamAddress.reverse prior)).wires ⊆ streamAllocation := by
  have hm : (measuredStreamBlock call prior).wires ⊆ streamAllocation := by
    rw [← streamAxis_singleton call prior]
    apply streamAxis_support
    · intro c h
      simp only [List.mem_singleton] at h
      subst c
      exact hc
    · simp only [AdaptiveCircuit.wires, List.nil_subset]
  intro w hw
  apply hm
  simp only [measuredStreamBlock, modularWires_seq] at *
  rcases hw with hw | hw
  · exact Or.inl (Or.inr hw)
  · exact Or.inr hw

/-- Future preparations commute across the current arithmetic/Fourier body. -/
theorem parkedStreamBody_future_commute (call : AdaptiveCircuit) (k : Nat) (prior : List Bool)
    (hc : call.wires ⊆ streamAllocation) (calls : List (Nat × AdaptiveCircuit))
    (hk : ∀ c ∈ calls, c.1 ≠ k) (b : InstrumentBranch)
    (hb : b ∈ (parkedStreamBody call k prior).run) (ψ : State) :
    b.kraus (Quantum.run ((streamPreparationWires calls).map Gate.H) ψ) =
      Quantum.run ((streamPreparationWires calls).map Gate.H) (b.kraus ψ) := by
  apply AdaptiveCircuit.branch_hadamards_commute _ _ _ b hb ψ
  intro w hw
  obtain ⟨c, hc', hw⟩ := List.mem_flatMap.mp hw
  exact streamRelabel_bank_disjoint _ (body_support call prior hc) k c.1 (hk c hc') w hw

/-- Move every preparation in an axis to its entry, retaining every branch in
order. Distinct banks are essential here, unlike clean-boundary bank reuse.
The input and the adaptive tail are arbitrary. -/
theorem relocatedStreamAxis_hoist (calls : List (Nat × AdaptiveCircuit))
    (prior : List Bool) (tail : AdaptiveCircuit)
    (hd : (calls.map Prod.fst).Nodup)
    (hc : ∀ c ∈ calls, c.2.wires ⊆ streamAllocation) (ψ : State) :
    (relocatedStreamAxis calls prior tail).map (fun b => (b.history, b.kraus ψ)) =
    (unpreparedStreamAxis calls prior tail).map
      (fun b => (b.history, b.kraus (Quantum.run ((streamPreparationWires calls).map Gate.H) ψ))) := by
  induction calls generalizing prior ψ with
  | nil => rfl
  | cons c calls ih =>
    rcases c with ⟨k, call⟩
    have hds : k ∉ calls.map Prod.fst ∧ (calls.map Prod.fst).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using hd
    have hks : ∀ c ∈ calls, c.1 ≠ k := by
      intro c hm he
      apply hds.1
      rw [← he]
      exact List.mem_map_of_mem hm
    have hcc := hc (k, call) (by simp)
    simp only [relocatedStreamAxis, measuredStreamBlock_split, AdaptiveCircuit.run,
      List.map_flatMap, List.flatMap_map, List.map_map, unpreparedStreamAxis,
      streamPreparationWires, List.flatMap_cons, List.map_append, run_append]
    apply List.flatMap_congr
    intro b hb
    have ht := ih (b.history.reverse.take 16 ++ prior) hds.2
      (fun c hm => hc c (by simp [hm]))
      (b.kraus (Quantum.run ((List.range' (windowBankStart k) 16).map Gate.H) ψ))
    have he := congrArg (List.map (fun e : List Bool × State => (b.history ++ e.1, e.2))) ht
    simp only [List.map_map, Function.comp_def] at he
    have hcomm := parkedStreamBody_future_commute call k prior hcc calls hks b hb
      (Quantum.run ((List.range' (windowBankStart k) 16).map Gate.H) ψ)
    rw [← hcomm] at he
    simpa only [streamPreparationWires, List.map_flatMap] using he
/-- Reused physical-bank execution equals an axis whose distinct logical banks
are all prepared at entry. Initial cleanliness is needed only for bank reuse;
hoisting itself holds on arbitrary states. The tail remains the same program. -/
theorem indexedStreamAxis_prepared (start : Nat) (hstart : 0 < start)
    (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit)
    (hc : ∀ c ∈ calls, c.wires ⊆ streamAllocation)
    (ψ : State) (hs : SupportedOn (Clean streamAddress) ψ)
    (hb : ∀ k, start ≤ k → k < start + calls.length →
      SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ) :
    (streamAxis calls prior tail).run.map (fun b => (b.history, b.kraus ψ)) =
    (unpreparedStreamAxis (indexedStreamCalls start calls) prior tail).map
      (fun b => (b.history, b.kraus
        (Quantum.run ((streamPreparationWires (indexedStreamCalls start calls)).map Gate.H) ψ))) := by
  rw [← indexedStreamAxis_run start hstart calls prior tail hc ψ hs hb]
  apply relocatedStreamAxis_hoist
  · simp only [indexedStreamCalls, List.map_map, Function.comp_def, Prod.fst_swap,
      List.zipIdx_map_snd]
    exact List.nodup_range'
  · intro c hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    apply hc a.1
    have h := List.mem_map_of_mem (f := Prod.fst) ha
    rwa [List.zipIdx_map_fst] at h
end
end ShorECDLP.Paper2607_13816
