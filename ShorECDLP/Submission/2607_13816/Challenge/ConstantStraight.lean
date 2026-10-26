import ShorECDLP.Submission.«2607_13816».Challenge.GidneyAdd
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantControl

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def constantTemplateGate {n : Nat} (q : Wire) : TemplateGate n → TemplateGate n
  | .literal g => .literal (constantControlGate q g)
  | .whenBit i v g => .whenBit i v (constantControlGate q g)

theorem constantTemplateGate_instantiate {n : Nat} (q : Wire) (g : TemplateGate n)
    (read : ConstantBit n → Bool) :
    (constantTemplateGate q g).instantiate read = (g.instantiate read).map (constantControlGate q) := by
  cases g with
  | literal g => rfl
  | whenBit i v g => simp [constantTemplateGate, TemplateGate.instantiate]; split <;> rfl

def constantStraight {n s e : Nat} (q : Wire) : Straight n s e → Straight n s e
  | .done => .done
  | .gate g next => .gate (constantTemplateGate q g) (constantStraight q next)
  | .recordGate i v g next => .recordGate i v (constantControlGate q g) (constantStraight q next)
  | .measure w next => .measure w (constantStraight q next)

theorem constantStraight_instantiate {n s e : Nat} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (constantStraight q p).instantiate read history = constantControlProgram q (p.instantiate read history) := by
  induction p with
  | done => rfl
  | gate g next ih => simp [constantStraight, Straight.instantiate, constantControlProgram,
      constantTemplateGate_instantiate, ih]
  | recordGate i v g next ih =>
    simp only [constantStraight, Straight.instantiate, constantControlProgram, ih]
    split <;> rfl
  | measure w next ih => simp [constantStraight, Straight.instantiate, constantControlProgram, ih]

theorem constantStraight_tCount {n s e : Nat} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((constantStraight q p).instantiate read history).tCount = (p.instantiate read history).tCount := by
  rw [constantStraight_instantiate, constantControlProgram_tCount]

theorem constantStraight_slots {n s e : Nat} (q : Wire) (p : Straight n s e) :
    (constantStraight q p).gateSlots = p.gateSlots := by
  induction p <;> simp_all [constantStraight, Straight.gateSlots]

theorem constantStraight_append {n a b c : Nat} (q : Wire) (p : Straight n a b) (r : Straight n b c) :
    constantStraight q (p.append r) = (constantStraight q p).append (constantStraight q r) := by
  induction p <;> simp_all [constantStraight, Straight.append]

theorem constantStraight_literal {n s e : Nat} (q : Wire) (gs : Circuit) (next : Straight n s e) :
    constantStraight q ((literalProgram gs).append next) =
      (literalProgram (gs.map (constantControlGate q))).append (constantStraight q next) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simpa only [literalProgram, List.map_cons, gateProgram, Straight.append,
      constantStraight, constantTemplateGate] using congrArg (Straight.gate (.literal (constantControlGate q g))) ih

theorem constantStraight_recordGates {n s e : Nat} (q : Wire) (i : Fin s) (gs : Circuit) (next : Straight n s e) :
    constantStraight q (recordGates i gs next) =
      recordGates i (gs.map (constantControlGate q)) (constantStraight q next) := by
  induction gs <;> simp_all [recordGates, constantStraight]

theorem constantStraight_correction {n s e : Nat} (q : Wire) (ws : List Wire)
    (indices : List (Fin s)) (next : Straight n s e) :
    constantStraight q (registerCorrectionProgram ws indices next) =
      registerCorrectionProgram ws indices (constantStraight q next) := by
  induction ws generalizing indices with
  | nil => rfl
  | cons w ws ih =>
    cases indices with
    | nil => rfl
    | cons i is => simp [registerCorrectionProgram, constantStraight_recordGates, ih,
        pauliZ, constantControlGate]

theorem constant_registerZ (q : Wire) (ws : List Wire) (outcomes : List Bool) :
    (registerZCorrection ws outcomes).map (constantControlGate q) = registerZCorrection ws outcomes := by
  induction ws generalizing outcomes with
  | nil => rfl
  | cons w ws ih =>
    cases outcomes with
    | nil => rfl
    | cons b bs => cases b <;> simp [registerZCorrection, pauliZ, constantControlGate, ih]

theorem constantStraight_castFinish {n s e f : Nat} (q : Wire) (h : e = f) (p : Straight n s e) :
    constantStraight q (castFinish h p) = castFinish h (constantStraight q p) := by
  subst f
  rfl

theorem constantStraight_deferred_run (q : Wire) (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((constantStraight q (deferredCorrectionProgram n targets cleanup cells start prior)).instantiate read history).run =
      (constantControlProgram q (deferredCorrectionCircuit targets cleanup cells (prior.map history))).run := by
  induction cells generalizing start with
  | nil =>
    simp only [deferredCorrectionProgram, constantStraight_correction, constantStraight_literal,
      constantStraight, registerCorrectionProgram_run, literalProgram_append_run,
      deferredCorrectionCircuit, constantControlProgram, List.map_append, constant_registerZ,
      AdaptiveCircuit.run, List.map_map]
    congr 1
    funext b
    cases b with
    | mk h k =>
      change InstrumentBranch.mk h (((k.comp _).comp _).comp _) = InstrumentBranch.mk h (k.comp _)
      simp only [Quantum.run_append_map, LinearMap.comp_assoc]
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    simp only [deferredCorrectionProgram, constantStraight_castFinish, castFinish_instantiate,
      constantStraight_literal, literalProgram_append_run, constantStraight, Straight.instantiate,
      deferredCorrectionCircuit, constantControlProgram, AdaptiveCircuit.run, ih]
    simp [List.map_append, List.map_map, Function.comp_def]

end ShorECDLP.Paper2607_13816.ChallengeMigration
