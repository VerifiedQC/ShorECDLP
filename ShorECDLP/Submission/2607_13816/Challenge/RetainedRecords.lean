import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWorkspace
import ShorECDLP.Framework.Quantum.AdaptiveMeasurement
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def HistoryAgrees {base cursor : Nat} (old : Fin base → Bool) (new : Fin cursor → Bool) : Prop :=
  ∀ i (hi : i < base) (hj : i < cursor), new ⟨i,hj⟩ = old ⟨i,hi⟩

theorem historyAgrees_extend {base cursor : Nat} (old : Fin base → Bool)
    (new : Fin cursor → Bool) (hbc : base ≤ cursor) (h : HistoryAgrees old new) (v : Bool) :
    HistoryAgrees old (Fin.lastCases v new) := by
  intro i hi hj
  have hc : i < cursor := lt_of_lt_of_le hi hbc
  change (Fin.lastCases v new : Fin (cursor+1) → Bool) (Fin.castSucc (⟨i,hc⟩ : Fin cursor)) = old ⟨i,hi⟩
  exact (Fin.lastCases_castSucc (motive := fun _ => Bool) (last := v) (cast := new) ⟨i,hc⟩).trans (h i hi hc)

theorem append_run_prior {n base a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (old : Fin base → Bool) (read : ConstantBit n → Bool) (history : Fin a → Bool)
    (target : AdaptiveCircuit) (hba : base ≤ a) (ha : HistoryAgrees old history)
    (hq : ∀ h, HistoryAgrees old h → (q.instantiate read h).run = target.run) :
    ((p.append q).instantiate read history).run =
      ((p.instantiate read history).seq target).run := by
  induction p with
  | done => exact hq history ha
  | gate g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq,
      AdaptiveCircuit.run, ih q history hba ha hq]
  | recordGate i v g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq,
      AdaptiveCircuit.run, ih q history hba ha hq]
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq, AdaptiveCircuit.run]
    rw [ih q _ (by omega) (historyAgrees_extend old history hba ha false) hq,
      ih q _ (by omega) (historyAgrees_extend old history hba ha true) hq]

theorem append_tCount_prior {n base a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (old : Fin base → Bool) (read : ConstantBit n → Bool) (history : Fin a → Bool)
    (target : AdaptiveCircuit) (hba : base ≤ a) (ha : HistoryAgrees old history)
    (hq : ∀ h, HistoryAgrees old h → (q.instantiate read h).tCount = target.tCount) :
    ((p.append q).instantiate read history).tCount =
      ((p.instantiate read history).seq target).tCount := by
  induction p with
  | done => exact hq history ha
  | gate g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq,
      AdaptiveCircuit.tCount, ih q history hba ha hq]
  | recordGate i v g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq,
      AdaptiveCircuit.tCount, ih q history hba ha hq]
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq, AdaptiveCircuit.tCount]
    rw [ih q _ (by omega) (historyAgrees_extend old history hba ha false) hq,
      ih q _ (by omega) (historyAgrees_extend old history hba ha true) hq]


def collectProgram (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count)) :
    List Wire → (start : Nat) → List (Fin start) → (count : Nat) × Straight n start (start+count)
  | [], start, prior => next start prior
  | w::ws, start, prior =>
    let tail := collectProgram n next ws (start+1) (prior.map Fin.castSucc ++ [Fin.last start])
    ⟨1+tail.1, castFinish (by omega) (.measure w tail.2)⟩

theorem collectProgram_run (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (source : List Bool → AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hn : ∀ cursor prior history, compiledRun (next cursor prior) read history = (source (prior.map history)).run)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    compiledRun (collectProgram n next ws start prior) read history =
      (measureResetThen ws (fun outcomes => source (prior.map history ++ outcomes))).run := by
  induction ws generalizing start with
  | nil => simpa only [collectProgram, measureResetThen, List.append_nil] using hn start prior history
  | cons w ws ih =>
    simp only [collectProgram, compiledRun, castFinish_instantiate, Straight.instantiate,
      AdaptiveCircuit.run, measureResetThen]
    have hf := ih (start+1) (prior.map Fin.castSucc ++ [Fin.last start]) (Fin.lastCases false history)
    have ht := ih (start+1) (prior.map Fin.castSucc ++ [Fin.last start]) (Fin.lastCases true history)
    simp only [compiledRun] at hf ht
    rw [hf, ht]
    simp [List.map_append, List.map_map, Function.comp_def, List.append_assoc]

theorem collectProgram_tCount (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (source : List Bool → AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hn : ∀ cursor prior history, compiledTCount (next cursor prior) read history = (source (prior.map history)).tCount)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    compiledTCount (collectProgram n next ws start prior) read history =
      (measureResetThen ws (fun outcomes => source (prior.map history ++ outcomes))).tCount := by
  induction ws generalizing start with
  | nil => simpa only [collectProgram, measureResetThen, List.append_nil] using hn start prior history
  | cons w ws ih =>
    simp only [collectProgram, compiledTCount, castFinish_instantiate, Straight.instantiate,
      AdaptiveCircuit.tCount, measureResetThen]
    have hf := ih (start+1) (prior.map Fin.castSucc ++ [Fin.last start]) (Fin.lastCases false history)
    have ht := ih (start+1) (prior.map Fin.castSucc ++ [Fin.last start]) (Fin.lastCases true history)
    simp only [compiledTCount] at hf ht
    rw [hf, ht]
    simp [List.map_append, List.map_map, Function.comp_def, List.append_assoc]


def appendRetaining {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (prior : List (Fin start)) : (count : Nat) × Straight n start (start+count) :=
  appendCompiled p (next (start+p.1) (prior.map (Fin.castLE (Nat.le_add_right start p.1))))

theorem appendRetaining_run {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (prior : List (Fin start)) (before : AdaptiveCircuit) (after : List Bool → AdaptiveCircuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledRun p read history = before.run)
    (hn : ∀ cursor indices h, compiledRun (next cursor indices) read h = (after (indices.map h)).run) :
    compiledRun (appendRetaining p next prior) read history = (before.seq (after (prior.map history))).run := by
  unfold appendRetaining appendCompiled compiledRun
  rw [castFinish_instantiate]
  rw [append_run_prior p.2 _ history read history (after (prior.map history)) (Nat.le_refl _) (by intro i hi hj; rfl)]
  · change (p.2.instantiate read history).run = before.run at hp
    rw [AdaptiveCircuit.run_seq, hp, ← AdaptiveCircuit.run_seq]
  · intro h hagree
    change compiledRun (next _ _) read h = _
    rw [hn]
    congr 2
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    exact hagree i.val i.isLt (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right start p.1))
theorem appendRetaining_tCount {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (prior : List (Fin start)) (before : AdaptiveCircuit) (after : List Bool → AdaptiveCircuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledTCount p read history = before.tCount)
    (hn : ∀ cursor indices h, compiledTCount (next cursor indices) read h = (after (indices.map h)).tCount) :
    compiledTCount (appendRetaining p next prior) read history = (before.seq (after (prior.map history))).tCount := by
  unfold appendRetaining appendCompiled compiledTCount
  rw [castFinish_instantiate]
  rw [append_tCount_prior p.2 _ history read history (after (prior.map history)) (Nat.le_refl _) (by intro i hi hj; rfl)]
  · change (p.2.instantiate read history).tCount = before.tCount at hp
    rw [adaptive_tCount_seq, hp, ← adaptive_tCount_seq]
  · intro h hagree
    change compiledTCount (next _ _) read h = _
    rw [hn]
    congr 2
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    exact hagree i.val i.isLt (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right start p.1))

end ShorECDLP.Paper2607_13816.ChallengeMigration
