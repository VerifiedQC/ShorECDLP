import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».Fourier.Continuation

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The fixed indices are newest first; only individual recorded bits control gates. -/
def feedbackProgram {n s e : Nat} (dir : PhaseDir) (w : Wire) :
    List (Fin s) → Nat → Straight n s e → Straight n s e
  | [], _, next => next
  | i :: is, k, next => .recordGate i true (.P dir k w)
      (feedbackProgram dir w is (k+1) next)

theorem feedbackProgram_run {n s e : Nat} (dir : PhaseDir) (w : Wire)
    (indices : List (Fin s)) (k : Nat) (next : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((feedbackProgram dir w indices k next).instantiate read history).run =
      (.unitary (fourierHistoryRotations dir w (indices.map history) k)
        (next.instantiate read history) : AdaptiveCircuit).run := by
  induction indices generalizing k with
  | nil =>
    simp only [feedbackProgram, List.map_nil, fourierHistoryRotations, AdaptiveCircuit.run]
    symm
    apply List.map_id'
  | cons i is ih =>
    simp only [feedbackProgram, Straight.instantiate, AdaptiveCircuit.run, ih,
      List.map_cons, fourierHistoryRotations, fourierFeedForward]
    cases history i <;> simp [List.map_map]
    all_goals
      intro a ha
      cases a
      rfl

/-- Compile a Fourier bank without submitting any branch-generating callback. -/
def fourierProgram (n : Nat) (dir : PhaseDir) :
    (ws : List Wire) → (start : Nat) → List (Fin start) →
      Straight n start (start + ws.length)
  | [], _, _ => .done
  | w :: ws, start, prior => castFinish (by simp [Nat.add_comm, Nat.add_left_comm])
      (feedbackProgram dir w prior 2 (.measure w
        (fourierProgram n dir ws (start+1) (Fin.last start :: prior.map Fin.castSucc))))

theorem fourierProgram_run (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    ((fourierProgram n dir ws start prior).instantiate read history).run =
      (semiclassicalFourier dir ws (prior.map history)).run := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [fourierProgram, castFinish_instantiate, feedbackProgram_run,
      Straight.instantiate, AdaptiveCircuit.run, semiclassicalFourier]
    rw [ih, ih]
    simp [List.map_map, Function.comp_def]

theorem feedbackProgram_slots {n s e : Nat} (dir : PhaseDir) (w : Wire)
    (indices : List (Fin s)) (k : Nat) (next : Straight n s e) :
    (feedbackProgram dir w indices k next).gateSlots = indices.length + next.gateSlots := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih => simp [feedbackProgram, Straight.gateSlots, ih]; omega

def fourierSlots : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, prior => prior + fourierSlots k (prior+1)

theorem fourierProgram_slots (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    (fourierProgram n dir ws start prior).gateSlots = fourierSlots ws.length prior.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp [fourierProgram, feedbackProgram_slots, Straight.gateSlots, ih, fourierSlots]

/-- Each emitted bit string is the original Fourier outcome, with the identical Kraus map. -/
theorem fourierProgram_branch (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((fourierProgram n dir ws start prior).instantiate read history).run) :
    b.history.length = ws.length ∧ b.kraus = fourierBranch dir ws (prior.map history) b.history := by
  rw [fourierProgram_run, semiclassicalFourier_run] at hb
  obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp hb
  exact ⟨(fourierOutcomes_mem _ _).mp hbs, rfl⟩

/-- Chronological records place this bank's actual Fourier bits directly after its prefix. -/
theorem fourierProgram_record_at (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((fourierProgram n dir ws start prior).instantiate read history).run)
    (before suffix : List Bool) (hlen : before.length = start) (i : Fin ws.length) :
    (before ++ b.history ++ suffix)[start + i.val]? = b.history[i.val]? := by
  have bl := (fourierProgram_branch n dir ws start prior read history b hb).1
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.add_sub_cancel_left]
  exact List.getElem?_append_left (by omega)

theorem feedbackProgram_wellFormed {n s e : Nat} (dir : PhaseDir) (w : Wire)
    (indices : List (Fin s)) (k : Nat) (next : Straight n s e) (hn : next.WellFormed) :
    (feedbackProgram dir w indices k next).WellFormed := by
  induction indices generalizing k with
  | nil => exact hn
  | cons i is ih => exact ⟨trivial, ih _⟩

@[simp] theorem castFinish_wellFormed {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    (castFinish h p).WellFormed = p.WellFormed := by subst f; rfl

theorem fourierProgram_wellFormed (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    (fourierProgram n dir ws start prior).WellFormed := by
  induction ws generalizing start with
  | nil => trivial
  | cons w ws ih =>
    simp only [fourierProgram, castFinish_wellFormed]
    apply feedbackProgram_wellFormed
    exact ih _ _

end ShorECDLP.Paper2607_13816.ChallengeMigration
