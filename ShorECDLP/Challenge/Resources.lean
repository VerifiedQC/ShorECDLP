import ShorECDLP.Framework.Quantum.Adaptive

namespace ShorECDLP.Challenge
open Quantum

/-- Protected syntactic CCX count. A diagnostic, not the challenge's sole score. -/
def toffoliCount : AdaptiveCircuit → Nat
  | .done => 0
  | .unitary gs next =>
      (gs.map (fun g => match g with | .CCX _ _ _ => 1 | _ => 0)).sum + toffoliCount next
  | .xMeasureReset _ a b => max (toffoliCount a) (toffoliCount b)

/-- Non-Clifford primitive count, with arbitrary dyadic rotations k≥3 charged.
This is diagnostic; it does not model rotation synthesis precision. -/
def nonCliffordCount : AdaptiveCircuit → Nat
  | .done => 0
  | .unitary gs next =>
      (gs.map (fun g => match g with
        | .CCX _ _ _ => 1
        | .P _ k _ => if 3 ≤ k then 1 else 0
        | _ => 0)).sum + nonCliffordCount next
  | .xMeasureReset _ a b => max (nonCliffordCount a) (nonCliffordCount b)

/-- All metrics are computed from the same interpreted primitive circuit.
T is the existing abstract T model, not a synthesized fault-tolerant estimate. -/
structure Resources where
  qubits : Nat
  tModel : Nat
  measurements : Nat
  toffoli : Nat
  nonClifford : Nat
  deriving DecidableEq, Repr

def resources (a : AdaptiveCircuit) : Resources :=
  ⟨a.qubitCount, a.tCount, a.measurementCount, toffoliCount a, nonCliffordCount a⟩

def Resources.score (r : Resources) : Nat := r.tModel

example : (resources (.unitary [.CCX 0 1 2] .done)).toffoli = 1 := rfl
example : (resources (.unitary [.P .forward 3 0] .done)).tModel = 1 := rfl
example : (resources (.xMeasureReset 0
    (.unitary [.CCX 0 1 2] .done) .done)).measurements = 1 := rfl
end ShorECDLP.Challenge
