import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def reindexBit {n m : Nat} (f : Fin n → Fin m) (bit : ConstantBit n) : ConstantBit m :=
  ⟨f bit.point, bit.field, bit.bit⟩
def reindexGate {n m : Nat} (f : Fin n → Fin m) : TemplateGate n → TemplateGate m
  | .literal g => .literal g
  | .whenBit bit v g => .whenBit (reindexBit f bit) v g

theorem reindexGate_instantiate {n m : Nat} (f : Fin n → Fin m) (g : TemplateGate n)
    (read : ConstantBit m → Bool) :
    (reindexGate f g).instantiate read = g.instantiate (read ∘ reindexBit f) := by
  cases g <;> rfl

def reindexStraight {n m s e : Nat} (f : Fin n → Fin m) : Straight n s e → Straight m s e
  | .done => .done
  | .gate g next => .gate (reindexGate f g) (reindexStraight f next)
  | .recordGate i v g next => .recordGate i v g (reindexStraight f next)
  | .measure w next => .measure w (reindexStraight f next)

theorem reindexStraight_instantiate {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e)
    (read : ConstantBit m → Bool) (history : Fin s → Bool) :
    (reindexStraight f p).instantiate read history = p.instantiate (read ∘ reindexBit f) history := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [reindexStraight, Straight.instantiate, reindexGate_instantiate, ih]
  | recordGate i v g p ih => simp only [reindexStraight, Straight.instantiate, ih]
  | measure w p ih => simp only [reindexStraight, Straight.instantiate, ih]

theorem reindexStraight_gateSlots {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    (reindexStraight f p).gateSlots = p.gateSlots := by
  induction p <;> simp_all only [reindexStraight, Straight.gateSlots]

theorem readConstant_reindex {n m : Nat} (f : Fin n → Fin m) (a : Fin n → PointCoeff)
    (b : Fin m → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (h : ∀ i, b (f i) = a i) :
    readConstant b Q ∘ reindexBit f = readConstant a Q := by
  funext bit
  simp only [Function.comp_def, readConstant, reindexBit, h]

def reindexCompiled {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    (count : Nat) × Straight m start (start+count) := ⟨p.1, reindexStraight f p.2⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration
