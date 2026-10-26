import ShorECDLP.Submission.«2607_13816».Challenge.ModularNegate
import ShorECDLP.Framework.Quantum.Relabel
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
noncomputable section

def relabelTemplateGate {n : Nat} (e : Wire ≃ Wire) : TemplateGate n → TemplateGate n
  | .literal g => .literal (g.relabel e)
  | .whenBit ref v g => .whenBit ref v (g.relabel e)

theorem relabelTemplateGate_instantiate {n : Nat} (e : Wire ≃ Wire) (g : TemplateGate n)
    (read : ConstantBit n → Bool) :
    (relabelTemplateGate e g).instantiate read = (g.instantiate read).map (Gate.relabel e) := by
  cases g with
  | literal g => rfl
  | whenBit ref v g => simp only [relabelTemplateGate, TemplateGate.instantiate]; split <;> rfl

def relabelStraight {n s t : Nat} (e : Wire ≃ Wire) : Straight n s t → Straight n s t
  | .done => .done
  | .gate g next => .gate (relabelTemplateGate e g) (relabelStraight e next)
  | .recordGate i v g next => .recordGate i v (g.relabel e) (relabelStraight e next)
  | .measure w next => .measure (e w) (relabelStraight e next)

theorem relabelStraight_instantiate {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((relabelStraight e p).instantiate read history) = (p.instantiate read history).relabel e := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [relabelStraight, Straight.instantiate, relabelTemplateGate_instantiate,
      AdaptiveCircuit.relabel, ih]
  | recordGate i v g p ih =>
    simp only [relabelStraight, Straight.instantiate, AdaptiveCircuit.relabel, ih]
    split <;> rfl
  | measure w p ih => simp only [relabelStraight, Straight.instantiate, AdaptiveCircuit.relabel, ih]

def relabelCompiled {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) :
    (count : Nat) × Straight n start (start+count) := ⟨p.1, relabelStraight e p.2⟩

theorem relabelCompiled_run {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) (target : AdaptiveCircuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledRun p read history = target.run) :
    compiledRun (relabelCompiled e p) read history = (target.relabel e).run := by
  simp only [relabelCompiled, compiledRun, relabelStraight_instantiate, AdaptiveCircuit.run_relabel]
  exact congrArg (List.map (InstrumentBranch.relabel e)) hp

theorem relabelCompiled_tCount {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) (target : AdaptiveCircuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledTCount p read history = target.tCount) :
    compiledTCount (relabelCompiled e p) read history = (target.relabel e).tCount := by
  simpa only [relabelCompiled, compiledTCount, relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount] using hp
end
end ShorECDLP.Paper2607_13816.ChallengeMigration
