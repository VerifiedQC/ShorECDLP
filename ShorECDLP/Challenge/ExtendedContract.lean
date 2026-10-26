import ShorECDLP.Challenge.Contract

namespace ShorECDLP.Challenge
open Quantum Secp256k1

/-- Additional diagnostic upper bounds, checked on the same instantiated circuit.
Non-Clifford counts CCX and dyadic phase primitives of order k ≥ 3. It is not
an arbitrary-rotation synthesis cost. -/
structure ExtendedBounds where
  toffoli : Nat
  nonClifford : Nat

/-- Optional extension; the existing Certificate and its fields are unchanged. -/
structure ExtendedCertificate (limits : Limits) (layout : DecodeLayout)
    (e : StraightEntry) (bounds : Bounds) (extra : ExtendedBounds) : Prop where
  certificate : Certificate limits layout e bounds
  diagnostics : ∀ Q : Point,
    (resources (e.instantiate Q)).toffoli ≤ extra.toffoli ∧
    (resources (e.instantiate Q)).nonClifford ≤ extra.nonClifford

private theorem list_toffoli_cost (gs : Circuit) :
    7 * (gs.map (fun g => match g with | .CCX _ _ _ => 1 | _ => 0)).sum ≤ tCount gs := by
  induction gs with
  | nil => simp [tCount]
  | cons g gs ih => cases g <;> simp_all [List.map_cons, List.sum_cons, tCount_cons, tCost] <;> omega

/-- Worst-path CCX count is bounded by one seventh of the protected T model. -/
theorem toffoliCount_mul_seven_le (a : AdaptiveCircuit) :
    7 * toffoliCount a ≤ a.tCount := by
  induction a with
  | done => simp [toffoliCount, AdaptiveCircuit.tCount]
  | unitary gs next ih =>
    have hg := list_toffoli_cost gs
    simpa only [toffoliCount, AdaptiveCircuit.tCount, Nat.mul_add] using Nat.add_le_add hg ih
  | xMeasureReset w a b ha hb =>
    simp only [toffoliCount, AdaptiveCircuit.tCount]
    omega

private theorem list_nonClifford_length (gs : Circuit) :
    (gs.map (fun g => match g with
      | .CCX _ _ _ => 1
      | .P _ k _ => if 3 ≤ k then 1 else 0
      | _ => 0)).sum ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    cases g <;> simp_all [List.map_cons, List.sum_cons] <;> first | omega | (split <;> omega)

/-- Every counted non-Clifford primitive is an actual gate, on the same path. -/
theorem nonCliffordCount_le_allGateCount (a : AdaptiveCircuit) :
    nonCliffordCount a ≤ allGateCount a := by
  induction a with
  | done => simp [nonCliffordCount, allGateCount]
  | unitary gs next ih =>
    have hg := list_nonClifford_length gs
    exact Nat.add_le_add hg ih
  | xMeasureReset w a b ha hb =>
    simp only [nonCliffordCount, allGateCount]
    omega

/-- A reusable conservative extension from existing protected resource bounds.
The bounds are diagnostics, not assertions of exact primitive counts. -/
theorem Certificate.extend {limits : Limits} {layout : DecodeLayout}
    {e : StraightEntry} {bounds : Bounds} (h : Certificate limits layout e bounds) :
    ExtendedCertificate limits layout e bounds
      ⟨bounds.tModel / 7, limits.gateSlots⟩ := by
  refine ⟨h, ?_⟩
  intro Q
  constructor
  · have ht := toffoliCount_mul_seven_le (e.instantiate Q)
    have hb := (h.resources Q).2.1
    change (e.instantiate Q).tCount ≤ bounds.tModel at hb
    change toffoliCount (e.instantiate Q) ≤ bounds.tModel / 7
    omega
  · have hn := nonCliffordCount_le_allGateCount (e.instantiate Q)
    have hs := e.program.allGateCount_le (readConstant e.coefficients.get Q) (Fin.elim0)
    exact hn.trans (hs.trans h.gateBudget)

end ShorECDLP.Challenge
