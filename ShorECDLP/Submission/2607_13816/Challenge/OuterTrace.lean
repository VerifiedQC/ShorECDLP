import ShorECDLP.Submission.«2607_13816».Challenge.Fourier

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- Splitting an actual straight-line branch preserves both the Kraus map and
its chronological history, including the history supplied to the suffix. -/
theorem straight_append_branch {n s m e : Nat} (p : Straight n s m) (q : Straight n m e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.append q).instantiate read history).run) :
    ∃ (mid : Fin m → Bool) (a c : InstrumentBranch),
      a ∈ (p.instantiate read history).run ∧ c ∈ (q.instantiate read mid).run ∧
      List.ofFn mid = List.ofFn history ++ a.history ∧ b = a.seq c := by
  induction p generalizing b with
  | done =>
    refine ⟨history, ⟨[], LinearMap.id⟩, b, by simp [Straight.instantiate, AdaptiveCircuit.run], hb, by simp, ?_⟩
    cases b
    simp [InstrumentBranch.seq]
  | gate g p ih =>
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨mid, a, c, ha, hc, hm, rfl⟩ := ih q history d hd
    refine ⟨mid, ⟨a.history, a.kraus.comp (Quantum.run (g.instantiate read))⟩, c,
      List.mem_map.mpr ⟨a, ha, rfl⟩, hc, hm, ?_⟩
    rfl
  | recordGate i v g p ih =>
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨mid, a, c, ha, hc, hm, rfl⟩ := ih q history d hd
    refine ⟨mid, ⟨a.history, a.kraus.comp (Quantum.run (if history i = v then [g] else []))⟩, c,
      List.mem_map.mpr ⟨a, ha, rfl⟩, hc, hm, ?_⟩
    rfl
  | measure w p ih =>
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      obtain ⟨mid, a, c, ha, hc, hm, rfl⟩ := ih q _ d hd
      refine ⟨mid, ⟨false :: a.history, a.kraus.comp (xResetKraus w false)⟩, c,
        List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩), hc, ?_, rfl⟩
      rw [List.ofFn_succ'] at hm
      simpa only [Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append,
        List.append_assoc, List.singleton_append] using hm
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      obtain ⟨mid, a, c, ha, hc, hm, rfl⟩ := ih q _ d hd
      refine ⟨mid, ⟨true :: a.history, a.kraus.comp (xResetKraus w true)⟩, c,
        List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩), hc, ?_, rfl⟩
      rw [List.ofFn_succ'] at hm
      simpa only [Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append,
        List.append_assoc, List.singleton_append] using hm

end ShorECDLP.Paper2607_13816.ChallengeMigration
