import ShorECDLP.Challenge.Resources
import ShorECDLP.Math.BitcoinPrimes

namespace ShorECDLP.Challenge
open Quantum Secp256k1

/-- Fixed coefficients, not a function of the problem instance.
Canonical residues bound scalar multiplication inputs. -/
structure PointCoeff where
  a : Fin order
  b : Fin order
  deriving DecidableEq

inductive PointField where
  | x | y | infinity | negX | negY | tripleX
  | exceptionalZeroX | exceptionalZeroY | negDoubleX
  | exceptionalNegX | exceptionalNegY
  | exceptionalNegDoubleX | exceptionalNegDoubleY
  | doubleX | doubleY | doubleInfinity
  deriving DecidableEq, Repr

/-- Reference to one of the protected table fields. -/
structure ConstantBit (tableSize : Nat) where
  point : Fin tableSize
  field : PointField
  bit : Fin 256
  deriving DecidableEq

/-- Fixed primitive gates, optionally enabled by exactly one constant bit.
No submitted callback receives Q or the table. -/
inductive TemplateGate (tableSize : Nat) where
  | literal (gate : Gate)
  | whenBit (ref : ConstantBit tableSize) (value : Bool) (gate : Gate)

/-- Closed data. Only measurement outcomes select continuations. -/
inductive Template (tableSize : Nat) where
  | done
  | unitary (gates : List (TemplateGate tableSize)) (next : Template tableSize)
  | xMeasureReset (wire : Wire) (onFalse onTrue : Template tableSize)

def TemplateGate.instantiate {n : Nat} (read : ConstantBit n → Bool) :
    TemplateGate n → Circuit
  | .literal g => [g]
  | .whenBit ref value g => if read ref = value then [g] else []

def Template.instantiate {n : Nat} (read : ConstantBit n → Bool) :
    Template n → AdaptiveCircuit
  | .done => .done
  | .unitary gates next => .unitary (gates.flatMap (TemplateGate.instantiate read))
      (next.instantiate read)
  | .xMeasureReset w a b => .xMeasureReset w (a.instantiate read) (b.instantiate read)

def Template.seq {n : Nat} : Template n → Template n → Template n
  | .done, b => b
  | .unitary gs next, b => .unitary gs (next.seq b)
  | .xMeasureReset w a b, c => .xMeasureReset w (a.seq c) (b.seq c)

theorem Template.instantiate_seq {n : Nat} (read : ConstantBit n → Bool)
    (a b : Template n) :
    (a.seq b).instantiate read = (a.instantiate read).seq (b.instantiate read) := by
  induction a with
  | done => rfl
  | unitary gs next ih => simp [Template.seq, Template.instantiate, AdaptiveCircuit.seq, ih]
  | xMeasureReset w a b ia ib =>
    simp [Template.seq, Template.instantiate, AdaptiveCircuit.seq, ia, ib]

def TemplateGate.WellFormed {n : Nat} : TemplateGate n → Prop
  | .literal g => g.WellFormed
  | .whenBit _ _ g => g.WellFormed

def Template.WellFormed {n : Nat} : Template n → Prop
  | .done => True
  | .unitary gs next => (∀ g ∈ gs, g.WellFormed) ∧ next.WellFormed
  | .xMeasureReset _ a b => a.WellFormed ∧ b.WellFormed

theorem TemplateGate.instantiate_wellFormed {n : Nat} (read : ConstantBit n → Bool)
    (g : TemplateGate n) (h : g.WellFormed) :
    CircuitWellFormed (g.instantiate read) := by
  cases g with
  | literal g => simpa [TemplateGate.instantiate, CircuitWellFormed] using h
  | whenBit r v g =>
    simp only [TemplateGate.instantiate]
    split
    · simpa [CircuitWellFormed] using h
    · simp [CircuitWellFormed]

theorem Template.instantiate_wellFormed {n : Nat} (read : ConstantBit n → Bool)
    (t : Template n) (h : t.WellFormed) : (t.instantiate read).WellFormed := by
  induction t with
  | done => trivial
  | unitary gs next ih =>
    refine ⟨?_, ih h.2⟩
    intro g hg
    obtain ⟨slot, hs, hg⟩ := List.mem_flatMap.mp hg
    exact TemplateGate.instantiate_wellFormed read slot (h.1 slot hs) g hg
  | xMeasureReset w a b ia ib => exact ⟨ia h.1, ib h.2⟩

/-- Protected point construction; no submitted point-valued callback. -/
noncomputable def constantPoint (Q : Point) (c : PointCoeff) : Point :=
  c.a.val • G + c.b.val • Q

def pointCoordinates : Point → Bool × (Fp × Fp)
  | .zero => (true, 0, 0)
  | .some (x := x) (y := y) _ => (false, x, y)

/-- The source coordinate permutation replaces a zero denominator by one.
This is deliberately different from taking the inverse of zero. -/
def exceptionalDenominator (z : Fp) : Fp := if z = 0 then 1 else z

/-- Fixed rational coordinate map for one public table point (x,y).
All arguments are evaluator-owned coordinates, never entrant callbacks. -/
def exceptionalImage (x y r s : Fp) : Fp × Fp :=
  let u := (s - y) / exceptionalDenominator (r - x)
  let w := r + 2*x - u^2
  (x - w, u * exceptionalDenominator w - y)

/-- Canonical coordinates of twice the same protected table point. -/
noncomputable def doubledCoordinates (P : Point) : Bool × (Fp × Fp) :=
  pointCoordinates (P + P)

noncomputable def fieldValue (P : Point) : PointField → Nat
  | .x => (pointCoordinates P).2.1.val
  | .y => (pointCoordinates P).2.2.val
  | .infinity => if (pointCoordinates P).1 then 1 else 0
  | .negX => (-(pointCoordinates P).2.1).val
  | .negY => (-(pointCoordinates P).2.2).val
  | .tripleX => (3 * (pointCoordinates P).2.1).val
  | .exceptionalZeroX =>
      (exceptionalImage (pointCoordinates P).2.1 (pointCoordinates P).2.2 0 0).1.val
  | .exceptionalZeroY =>
      (exceptionalImage (pointCoordinates P).2.1 (pointCoordinates P).2.2 0 0).2.val
  | .negDoubleX => (-2 * (pointCoordinates P).2.1).val
  | .exceptionalNegX =>
      (exceptionalImage (pointCoordinates P).2.1 (pointCoordinates P).2.2
        (pointCoordinates P).2.1 (-(pointCoordinates P).2.2)).1.val
  | .exceptionalNegY =>
      (exceptionalImage (pointCoordinates P).2.1 (pointCoordinates P).2.2
        (pointCoordinates P).2.1 (-(pointCoordinates P).2.2)).2.val
  | .exceptionalNegDoubleX =>
      (exceptionalImage (pointCoordinates P).2.1 (pointCoordinates P).2.2
        (doubledCoordinates P).2.1 (-(doubledCoordinates P).2.2)).1.val
  | .exceptionalNegDoubleY =>
      (exceptionalImage (pointCoordinates P).2.1 (pointCoordinates P).2.2
        (doubledCoordinates P).2.1 (-(doubledCoordinates P).2.2)).2.val
  | .doubleX => (doubledCoordinates P).2.1.val
  | .doubleY => (doubledCoordinates P).2.2.val
  | .doubleInfinity => if (doubledCoordinates P).1 then 1 else 0

noncomputable def readConstant {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (ref : ConstantBit n) : Bool :=
  (fieldValue (constantPoint Q (coeffs ref.point)) ref.field).testBit ref.bit.val

/-- Submission data. Ingestion must freeze this as Q-independent data; no
decoder or resource-counter callback is accepted in this structure. -/
structure Entry where
  coefficients : List PointCoeff
  template : Template coefficients.length

noncomputable def Entry.program (e : Entry) (Q : Point) : AdaptiveCircuit :=
  e.template.instantiate (readConstant e.coefficients.get Q)

theorem Entry.program_wellFormed (e : Entry) (h : e.template.WellFormed) (Q : Point) :
    (e.program Q).WellFormed :=
  Template.instantiate_wellFormed _ _ h

noncomputable def Entry.resources (e : Entry) (Q : Point) : Resources :=
  ShorECDLP.Challenge.resources (e.program Q)
end ShorECDLP.Challenge
