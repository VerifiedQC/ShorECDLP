import ShorECDLP.Framework.Quantum.AdaptiveDisjoint
import ShorECDLP.Submission.«2607_13816».Window.RawTwoAxis
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem branch_rotations_commute (a : AdaptiveCircuit) (w : Wire)
    (hw : w ∉ a.wires) (b : InstrumentBranch) (hb : b ∈ a.run)
    (dir : PhaseDir) (prior : List Bool) (k : Nat) (ψ : State) :
    b.kraus (Quantum.run (fourierHistoryRotations dir w prior k) ψ) =
      Quantum.run (fourierHistoryRotations dir w prior k) (b.kraus ψ) := by
  induction prior generalizing k ψ with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | false => simpa only [fourierHistoryRotations, fourierFeedForward, List.nil_append] using ih (k+1) ψ
    | true =>
      simp only [fourierHistoryRotations, fourierFeedForward, if_true, List.singleton_append, run_cons]
      rw [ih, a.branch_P_commute w dir k hw b hb]

/-- Disjoint actual arithmetic commutes with each Fourier outcome, including
phase feedback and reset. No validity or product-state assumption is needed. -/
theorem adaptiveBranch_fourier_commute (a : AdaptiveCircuit) (dir : PhaseDir)
    (ws : List Wire) (prior bs : List Bool) (hw : ∀ w ∈ ws, w ∉ a.wires)
    (b : InstrumentBranch) (hb : b ∈ a.run) (ψ : State) :
    b.kraus (fourierBranch dir ws prior bs ψ) =
      fourierBranch dir ws prior bs (b.kraus ψ) := by
  induction ws generalizing prior bs ψ with
  | nil => cases bs <;> simp [fourierBranch]
  | cons w ws ih =>
    cases bs with
    | nil => simp [fourierBranch]
    | cons x xs =>
      simp only [fourierBranch, LinearMap.comp_apply]
      rw [ih (x::prior) xs (by intro v hv; exact hw v (by simp [hv])),
        a.branch_reset_commute w x (hw w (by simp)) b hb,
        branch_rotations_commute a w (hw w (by simp)) b hb]

/-- Arithmetic at one parked bank commutes with Fourier measurement at any
other bank, retaining each fixed arithmetic and Fourier outcome separately. -/
theorem streamArithmetic_fourier_commute (call : AdaptiveCircuit)
    (hc : call.wires ⊆ streamAllocation) (k j : Nat) (hjk : j ≠ k)
    (dir : PhaseDir) (prior bs : List Bool)
    (b : InstrumentBranch) (hb : b ∈ (call.relabel (streamBankPerm k)).run) (ψ : State) :
    b.kraus (fourierBranch dir (List.range' (windowBankStart j) 16).reverse prior bs ψ) =
      fourierBranch dir (List.range' (windowBankStart j) 16).reverse prior bs (b.kraus ψ) := by
  apply adaptiveBranch_fourier_commute _ dir _ prior bs _ b hb
  intro w hw
  exact streamRelabel_bank_disjoint call hc k j hjk w (List.mem_reverse.mp hw)

/-- A whole remaining axis commutes branchwise with an earlier disjoint
Fourier block. Its own adaptive history and the arbitrary disjoint tail remain
unchanged; this does not discard or aggregate any arithmetic outcome. -/
theorem unpreparedStreamAxis_fourier_commute (calls : List (Nat × AdaptiveCircuit))
    (prior : List Bool) (tail : AdaptiveCircuit) (j : Nat)
    (hc : ∀ c ∈ calls, c.2.wires ⊆ streamAllocation)
    (hj : ∀ c ∈ calls, j ≠ c.1)
    (ht : ∀ w ∈ List.range' (windowBankStart j) 16, w ∉ tail.wires)
    (dir : PhaseDir) (earlier bs : List Bool)
    (b : InstrumentBranch) (hb : b ∈ unpreparedStreamAxis calls prior tail) (ψ : State) :
    b.kraus (fourierBranch dir (List.range' (windowBankStart j) 16).reverse earlier bs ψ) =
      fourierBranch dir (List.range' (windowBankStart j) 16).reverse earlier bs (b.kraus ψ) := by
  induction calls generalizing prior b ψ with
  | nil =>
    apply adaptiveBranch_fourier_commute tail dir _ earlier bs _ b hb
    intro w hw
    exact ht w (List.mem_reverse.mp hw)
  | cons c calls ih =>
    obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hb
    obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hm
    have hs := streamBody_support c.2 prior (hc c (by simp))
    change next.kraus (a.kraus (fourierBranch _ _ _ _ ψ)) =
      fourierBranch _ _ _ _ (next.kraus (a.kraus ψ))
    rw [streamArithmetic_fourier_commute _ hs c.1 j (hj c (by simp)) dir earlier bs a ha,
      ih _ (by intro d hd; exact hc d (by simp [hd]))
        (by intro d hd; exact hj d (by simp [hd])) next hn]
end
end ShorECDLP.Paper2607_13816
