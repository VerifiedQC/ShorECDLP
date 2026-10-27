import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».Challenge.GidneyAdd
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The branch tree retains every measurement outcome, including zero-mass branches. -/
theorem adaptive_run_nonempty (a : AdaptiveCircuit) : ∃ b, b ∈ a.run := by
  induction a with
  | done => exact ⟨_, List.mem_singleton_self _⟩
  | unitary gs a ih =>
    obtain ⟨b,hb⟩ := ih
    exact ⟨_, List.mem_map_of_mem hb⟩
  | xMeasureReset w a b iha ihb =>
    obtain ⟨c,hc⟩ := iha
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hc)⟩

/-- Uniform actual branch record lengths determine the syntactic measurement count. -/
theorem measurementCount_of_uniform_run (a : AdaptiveCircuit) (k : Nat)
    (h : ∀ b ∈ a.run, b.history.length = k) : a.measurementCount = k := by
  induction a generalizing k with
  | done => exact h ⟨[],LinearMap.id⟩ (List.mem_singleton_self _)
  | unitary gs a ih =>
    apply ih
    intro b hb
    have hh := h _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
    exact hh
  | xMeasureReset w a b iha ihb =>
    have ha : ∀ c ∈ a.run, c.history.length + 1 = k := by
      intro c hc
      exact h _ (List.mem_append_left _ (List.mem_map_of_mem hc))
    have hb : ∀ c ∈ b.run, c.history.length + 1 = k := by
      intro c hc
      exact h _ (List.mem_append_right _ (List.mem_map_of_mem hc))
    have hk : 0 < k := by
      obtain ⟨c,hc⟩ := adaptive_run_nonempty a
      have := ha c hc
      omega
    have hca := iha (k-1) (by intro c hc; have := ha c hc; omega)
    have hcb := ihb (k-1) (by intro c hc; have := hb c hc; omega)
    simp only [AdaptiveCircuit.measurementCount,hca,hcb,max_self]
    omega

/-- Transfer measurement counts through a proved execution binding, without
unfolding the compiled circuit or enumerating its branches. -/
theorem compiled_count_of_run {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (a : AdaptiveCircuit)
    (h : compiledRun p read history = a.run) : p.1 = a.measurementCount := by
  apply Eq.symm
  apply measurementCount_of_uniform_run
  intro b hb
  rw [← h] at hb
  have hh := straight_history_length p.2 read history b hb
  simpa using hh
end ShorECDLP.Paper2607_13816.ChallengeMigration
