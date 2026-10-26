import ShorECDLP.Submission.«2607_13816».Challenge.ModularNegate
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

abbrev FixedSegment (n : Nat) := (start : Nat) → (count : Nat) × Straight n start (start+count)

def sequenceProgram (n : Nat) : List (FixedSegment n) → (start : Nat) →
    (count : Nat) × Straight n start (start+count)
  | [], _ => ⟨0, .done⟩
  | seg::rest, start => appendCompiled (seg start) (sequenceProgram n rest (start+(seg start).1))

def sequenceCircuit : List AdaptiveCircuit → AdaptiveCircuit
  | [] => .done
  | p::ps => p.seq (sequenceCircuit ps)

theorem sequenceProgram_run (n : Nat) (ps : List (FixedSegment n)) (sources : List AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (h : List.Forall₂ (fun p source => ∀ start history, compiledRun (p start) read history = source.run) ps sources)
    (start : Nat) (history : Fin start → Bool) :
    compiledRun (sequenceProgram n ps start) read history = (sequenceCircuit sources).run := by
  induction h generalizing start with
  | nil => rfl
  | cons hp hs ih =>
    unfold sequenceProgram sequenceCircuit
    apply appendCompiled_run_eq
    · exact hp start history
    · intro h
      exact ih _ h

theorem sequenceProgram_tCount (n : Nat) (ps : List (FixedSegment n)) (sources : List AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (h : List.Forall₂ (fun p source => ∀ start history, compiledTCount (p start) read history = source.tCount) ps sources)
    (start : Nat) (history : Fin start → Bool) :
    compiledTCount (sequenceProgram n ps start) read history = (sequenceCircuit sources).tCount := by
  induction h generalizing start with
  | nil => rfl
  | cons hp hs ih =>
    unfold sequenceProgram sequenceCircuit
    apply appendCompiled_tCount_eq
    · exact hp start history
    · intro h
      exact ih _ h
end ShorECDLP.Paper2607_13816.ChallengeMigration
