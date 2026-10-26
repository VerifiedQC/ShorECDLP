import ShorECDLP.Challenge.Template

namespace ShorECDLP.Challenge
open Quantum Secp256k1

/-- First-order straight-line program indexed by its starting and ending
measurement cursors. A record control is statically a Fin of the current cursor.
There are no branch subtrees, jumps, or submitted callbacks. -/
inductive Straight (n : Nat) : Nat → Nat → Type
  | done {cursor : Nat} : Straight n cursor cursor
  | gate {start finish : Nat} (gate : TemplateGate n) (next : Straight n start finish) :
      Straight n start finish
  | recordGate {start finish : Nat} (record : Fin start) (value : Bool) (gate : Gate)
      (next : Straight n start finish) : Straight n start finish
  | measure {start finish : Nat} (wire : Wire) (next : Straight n (start+1) finish) :
      Straight n start finish

def Straight.append {n a b c : Nat} : Straight n a b → Straight n b c → Straight n a c
  | .done, q => q
  | .gate g next, q => .gate g (next.append q)
  | .recordGate i v g next, q => .recordGate i v g (next.append q)
  | .measure w next, q => .measure w (next.append q)

/-- Protected evaluator only. The two expanded measurement branches use exactly
the same submitted suffix, differing solely in the appended record bit. -/
def Straight.instantiate {n s e : Nat} (read : ConstantBit n → Bool)
    (history : Fin s → Bool) : Straight n s e → AdaptiveCircuit
  | .done => .done
  | .gate g next => .unitary (g.instantiate read) (next.instantiate read history)
  | .recordGate i v g next => .unitary (if history i=v then [g] else [])
      (next.instantiate read history)
  | .measure w next => .xMeasureReset w
      (next.instantiate read (Fin.lastCases false history))
      (next.instantiate read (Fin.lastCases true history))

def Straight.gateSlots {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate _ next => 1+next.gateSlots
  | .recordGate _ _ _ next => 1+next.gateSlots
  | .measure _ next => next.gateSlots

def Straight.WellFormed {n s e : Nat} : Straight n s e → Prop
  | .done => True
  | .gate g next => g.WellFormed ∧ next.WellFormed
  | .recordGate _ _ g next => g.WellFormed ∧ next.WellFormed
  | .measure _ next => next.WellFormed

theorem Straight.cursor_mono {n s e : Nat} (p : Straight n s e) : s ≤ e := by
  induction p with
  | done => rfl
  | gate g p ih => exact ih
  | recordGate i v g p ih => exact ih
  | measure w p ih => omega

theorem Straight.instantiate_wellFormed {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (h : p.WellFormed) : (p.instantiate read history).WellFormed := by
  induction p with
  | done => trivial
  | gate g p ih => exact ⟨g.instantiate_wellFormed read h.1, ih history h.2⟩
  | recordGate i v g p ih =>
    refine ⟨?_, ih history h.2⟩
    simp only [CircuitWellFormed]
    split
    · simpa using h.1
    · simp
  | measure w p ih => exact ⟨ih _ h, ih _ h⟩

/-- Static records: every branch produces the same number of measurements. -/
theorem Straight.measurementCount {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).measurementCount = e-s := by
  induction p with
  | done => simp [Straight.instantiate, AdaptiveCircuit.measurementCount]
  | gate g p ih => exact ih history
  | recordGate i v g p ih => exact ih history
  | measure w p ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.measurementCount, ih, max_self]
    have hm := p.cursor_mono
    omega

/-- Actual primitive gates on the worst measurement path; every gate counts. -/
def allGateCount : AdaptiveCircuit → Nat
  | .done => 0
  | .unitary gs next => gs.length + allGateCount next
  | .xMeasureReset _ a b => max (allGateCount a) (allGateCount b)

theorem templateGate_length {n : Nat} (g : TemplateGate n)
    (read : ConstantBit n → Bool) : (g.instantiate read).length ≤ 1 := by
  cases g with
  | literal g => simp [TemplateGate.instantiate]
  | whenBit r v g => simp only [TemplateGate.instantiate]; split <;> simp

theorem Straight.allGateCount_le {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    allGateCount (p.instantiate read history) ≤ p.gateSlots := by
  induction p with
  | done => exact Nat.le_refl 0
  | gate g p ih =>
    simp only [Straight.instantiate, allGateCount, Straight.gateSlots]
    have h := templateGate_length g read
    have hnext := ih history
    omega
  | recordGate i v g p ih =>
    simp only [Straight.instantiate, allGateCount, Straight.gateSlots]
    have hnext := ih history
    split <;> simp only [List.length_singleton, List.length_nil] <;> omega
  | measure w p ih =>
    exact max_le (ih _) (ih _)

theorem Straight.gateSlots_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    (p.append q).gateSlots = p.gateSlots + q.gateSlots := by
  induction p with
  | done => simp [Straight.append, Straight.gateSlots]
  | gate g p ih => simp [Straight.append, Straight.gateSlots, ih, Nat.add_assoc]
  | recordGate i v g p ih => simp [Straight.append, Straight.gateSlots, ih, Nat.add_assoc]
  | measure w p ih => exact ih q

structure StraightEntry where
  coefficients : List PointCoeff
  finalCursor : Nat
  program : Straight coefficients.length 0 finalCursor

noncomputable def StraightEntry.instantiate (e : StraightEntry) (Q : Point) : AdaptiveCircuit :=
  e.program.instantiate (readConstant e.coefficients.get Q) Fin.elim0
end ShorECDLP.Challenge
