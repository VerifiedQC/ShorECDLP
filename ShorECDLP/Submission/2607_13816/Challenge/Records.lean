import ShorECDLP.Submission.«2607_13816».Challenge.Reset
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem straight_history_length {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (b : InstrumentBranch) (hb : b ∈ (p.instantiate read history).run) :
    b.history.length = e - s := by
  induction p generalizing b with
  | done =>
    simp only [Straight.instantiate, AdaptiveCircuit.run, List.mem_singleton] at hb
    subst b
    simp
  | gate g p ih =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact ih history a ha
  | recordGate i v g p ih =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact ih history a ha
  | measure w p ih =>
    rcases List.mem_append.mp hb with hb | hb
    all_goals
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      have hh := ih _ a ha
      have hm := p.cursor_mono
      change a.history.length + 1 = _
      omega
theorem fixedReset_history_length (n start : Nat) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((fixedReset n start).instantiate read history).run) :
    b.history.length = 854 := by
  have h := straight_history_length (fixedReset n start) read history b hb
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration
