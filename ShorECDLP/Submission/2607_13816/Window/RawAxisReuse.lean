import ShorECDLP.Submission.«2607_13816».Window.StreamAxisReuse
import ShorECDLP.Submission.«2607_13816».Window.RawStream
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Assign consecutive nonzero logical banks, retaining the actual call order. -/
def indexedStreamCalls (start : Nat) (calls : List AdaptiveCircuit) : List (Nat × AdaptiveCircuit) :=
  (calls.zipIdx start).map Prod.swap

theorem indexedStreamCalls_calls (start : Nat) (calls : List AdaptiveCircuit) :
    (indexedStreamCalls start calls).map Prod.snd = calls := by
  simpa only [indexedStreamCalls, List.map_map, Function.comp_def, Prod.snd_swap] using
    (List.zipIdx_map_fst start calls)

theorem indexedStreamAxis_run (start : Nat) (hstart : 0 < start)
    (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit)
    (hc : ∀ c ∈ calls, c.wires ⊆ streamAllocation)
    (ψ : State) (hs : SupportedOn (Clean streamAddress) ψ)
    (hb : ∀ k, start ≤ k → k < start + calls.length →
      SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ) :
    (relocatedStreamAxis (indexedStreamCalls start calls) prior tail).map
      (fun b => (b.history, b.kraus ψ)) =
    (streamAxis calls prior tail).run.map (fun b => (b.history, b.kraus ψ)) := by
  conv_rhs => rw [← indexedStreamCalls_calls start calls]
  apply relocatedStreamAxis_run
  · intro c hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    have hi := List.mem_zipIdx ha
    dsimp at *
    omega
  · intro c hm w hw
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    have hx : a.1 ∈ calls := by
      have hh := List.mem_map_of_mem (f := Prod.fst) ha
      rwa [List.zipIdx_map_fst] at hh
    have h := hc a.1 hx hw
    simpa only [streamAllocation, List.mem_append, List.mem_range] using h
  · exact hs
  · intro c hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    have hi := List.mem_zipIdx ha
    apply hb a.2 <;> omega

/-- All sixteen left-axis blocks, including the actual direct point lookup,
may be moved to banks 1..16; the complete right-axis tail stays unchanged. -/
theorem streamRawLeftAxis_relocated (P Q : Point) (prior : List Bool) (tail : AdaptiveCircuit)
    (ψ : State) (hs : SupportedOn (Clean streamAddress) ψ)
    (hb : ∀ k, 1 ≤ k → k < 17 → SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ) :
    (relocatedStreamAxis (indexedStreamCalls 1 (streamRawLeftCalls P Q)) prior tail).map
      (fun b => (b.history, b.kraus ψ)) =
    (streamAxis (streamRawLeftCalls P Q) prior tail).run.map (fun b => (b.history, b.kraus ψ)) := by
  refine indexedStreamAxis_run 1 (by decide) _ prior tail ?_ ψ hs ?_
  · intro c hc
    simp only [streamRawLeftCalls, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨j, hj, rfl⟩
    · exact streamPointLookup_support _
    · exact streamRawCall_support _ _
  · simpa only [streamRawLeftCalls, List.length_cons, List.length_map,
      List.length_reverse, List.length_range] using hb

/-- The thirteen right-axis blocks use banks 17..29 and their own Fourier history. -/
theorem streamRawRightAxis_relocated (Q : Point) (prior : List Bool) (tail : AdaptiveCircuit)
    (ψ : State) (hs : SupportedOn (Clean streamAddress) ψ)
    (hb : ∀ k, 17 ≤ k → k < 30 → SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ) :
    (relocatedStreamAxis (indexedStreamCalls 17 (streamRawRightCalls Q)) prior tail).map
      (fun b => (b.history, b.kraus ψ)) =
    (streamAxis (streamRawRightCalls Q) prior tail).run.map (fun b => (b.history, b.kraus ψ)) := by
  refine indexedStreamAxis_run 17 (by decide) _ prior tail ?_ ψ hs ?_
  · intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact streamRawCall_support _ _
  · simpa only [streamRawRightCalls, List.length_map, List.length_reverse, List.length_range] using hb
end
end ShorECDLP.Paper2607_13816
