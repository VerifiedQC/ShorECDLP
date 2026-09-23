import ShorECDLP.Framework.Quantum.AdaptiveHadamard
import ShorECDLP.Submission.«2607_13816».Window.StreamAxisReuse
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- A relocated streaming operation does not touch any different logical bank. -/
theorem streamRelabel_bank_disjoint (a : AdaptiveCircuit)
    (ha : a.wires ⊆ streamAllocation) (k j : Nat) (hjk : j ≠ k) :
    ∀ w ∈ List.range' (windowBankStart j) 16, w ∉ (a.relabel (streamBankPerm k)).wires := by
  intro w hw hm
  rw [AdaptiveCircuit.relabel_wires] at hm
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
  have hs := ha hv
  simp only [streamAllocation, List.mem_append, List.mem_range] at hs
  rcases hs with hs | hs
  · rw [streamBankPerm_core k v hs] at hw
    simp only [List.mem_range'_1, windowBankStart] at hw
    dsimp only [Wire] at *
    omega
  · simp only [streamAddress, List.mem_range'_1] at hs
    dsimp only [Wire] at *
    have hi : v - 855 < 16 := by dsimp only [Wire]; omega
    have he : v = 855 + (v - 855) := by dsimp only [Wire]; omega
    rw [he, streamBankPerm_address k (v-855) hi] at hw
    simp only [List.mem_range'_1, windowBankStart] at hw
    dsimp only [Wire] at *
    omega

/-- Prepare a future bank before the current complete measured block. The
identity preserves arithmetic outcomes, Fourier outcomes and an arbitrary tail;
it needs no clean-state or independence hypothesis on the input state. -/
theorem streamBlock_prepare_future (call : AdaptiveCircuit) (prior : List Bool)
    (hc : call.wires ⊆ streamAllocation) (k j : Nat) (hjk : j ≠ k)
    (tail : AdaptiveCircuit) (ψ : State) :
    (((measuredStreamBlock call prior).relabel (streamBankPerm k)).seq
      (.unitary ((List.range' (windowBankStart j) 16).map Gate.H) tail)).run.map
        (fun b => (b.history, b.kraus ψ)) =
    ((AdaptiveCircuit.unitary ((List.range' (windowBankStart j) 16).map Gate.H)
      ((measuredStreamBlock call prior).relabel (streamBankPerm k))).seq tail).run.map
        (fun b => (b.history, b.kraus ψ)) := by
  apply AdaptiveCircuit.prepare_hadamards_run
  apply streamRelabel_bank_disjoint _ _ k j hjk
  rw [← streamAxis_singleton call prior]
  apply streamAxis_support
  · intro c hm
    simp only [List.mem_singleton] at hm
    subst c
    exact hc
  · simp only [AdaptiveCircuit.wires, List.nil_subset]
/-- Preparation of a still-unused bank commutes through an entire relocated
axis, including each outcome-dependent Fourier continuation. The tail must
also avoid that bank; choosing `done` gives a prefix commutation rule. -/
theorem relocatedStreamAxis_future_commute (calls : List (Nat × AdaptiveCircuit))
    (prior : List Bool) (tail : AdaptiveCircuit) (j : Nat)
    (hj : ∀ c ∈ calls, j ≠ c.1)
    (hc : ∀ c ∈ calls, c.2.wires ⊆ streamAllocation)
    (ht : ∀ w ∈ List.range' (windowBankStart j) 16, w ∉ tail.wires)
    (b : InstrumentBranch) (hb : b ∈ relocatedStreamAxis calls prior tail) (ψ : State) :
    b.kraus (Quantum.run ((List.range' (windowBankStart j) 16).map Gate.H) ψ) =
      Quantum.run ((List.range' (windowBankStart j) 16).map Gate.H) (b.kraus ψ) := by
  induction calls generalizing prior b ψ with
  | nil => exact tail.branch_hadamards_commute _ ht b hb ψ
  | cons c calls ih =>
    obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hb
    obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hm
    have hs : (measuredStreamBlock c.2 prior).wires ⊆ streamAllocation := by
      rw [← streamAxis_singleton c.2 prior]
      apply streamAxis_support
      · intro d hd
        simp only [List.mem_singleton] at hd
        subst d
        exact hc c (by simp)
      · simp only [AdaptiveCircuit.wires, List.nil_subset]
    have hw := streamRelabel_bank_disjoint _ hs c.1 j (hj c (by simp))
    change next.kraus (a.kraus (Quantum.run _ ψ)) = Quantum.run _ (next.kraus (a.kraus ψ))
    rw [AdaptiveCircuit.branch_hadamards_commute _ _ hw a ha,
      ih _ (by intro d hd; exact hj d (by simp [hd]))
        (by intro d hd; exact hc d (by simp [hd])) next hn]
end
end ShorECDLP.Paper2607_13816
