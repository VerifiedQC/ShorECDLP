import ShorECDLP.Submission.«2607_13816».Arithmetic.PrimitiveResources
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- A gatewise cost identity is preserved by fixed-control lowering on every branch. -/
theorem primitiveCost_constantControl (cost : Gate → Nat) (q : Wire)
    (hc : ∀ g, cost (constantControlGate q g)=cost g) (a : AdaptiveCircuit) :
    gidneyGateCount cost (constantControlProgram q a)=gidneyGateCount cost a := by
  induction a with
  | done => rfl
  | unitary g a ih =>
    simp only [constantControlProgram,gidneyGateCount,List.map_map,Function.comp_def,hc,ih]
  | xMeasureReset w a b iha ihb =>
    simp only [constantControlProgram,gidneyGateCount,iha,ihb]

private theorem constantControl_cost_le (cost left right : Gate → Nat) (q : Wire)
    (hc : ∀ g, cost (constantControlGate q g) ≤ left g+right g) (a : AdaptiveCircuit) :
    gidneyGateCount cost (constantControlProgram q a) ≤ gidneyGateCount left a+gidneyGateCount right a := by
  have hg (g : Circuit) : ((g.map (constantControlGate q)).map cost).sum ≤
      (g.map left).sum+(g.map right).sum := by
    induction g with
    | nil => rfl
    | cons g gs ih =>
      have hh := hc g
      simp only [List.map_cons,List.sum_cons]
      omega
  induction a with
  | done => rfl
  | unitary g a ih =>
    have hh := hg g
    simp only [constantControlProgram,gidneyGateCount]
    omega
  | xMeasureReset w a b iha ihb =>
    simp only [constantControlProgram,gidneyGateCount]
    omega

/-- Fixed-control lowering can transfer CNOT cost into X cost without increasing CNOTs. -/
theorem primitiveResources_constantControl_bounds (q : Wire) (a : AdaptiveCircuit) :
    (primitiveResources (constantControlProgram q a)).x ≤ (primitiveResources a).x+(primitiveResources a).cnot ∧
    (primitiveResources (constantControlProgram q a)).cnot ≤ (primitiveResources a).cnot := by
  have hx := constantControl_cost_le primitiveXCost primitiveXCost
    (fun g => match g with | .CX _ _ => 1 | _ => 0) q
    (by
      intro g
      cases g with
      | CX c t => by_cases hc : c=q <;> simp [constantControlGate,hc,primitiveXCost]
      | _ => simp [constantControlGate,primitiveXCost]) a
  have hc := constantControl_cost_le (fun g => match g with | .CX _ _ => 1 | _ => 0)
    (fun g => match g with | .CX _ _ => 1 | _ => 0) (fun _ => 0) q
    (by
      intro g
      cases g with
      | CX c t => by_cases hc : c=q <;> simp [constantControlGate,hc]
      | _ => simp [constantControlGate]) a
  have hz (b : AdaptiveCircuit) : gidneyGateCount (fun _ => 0) b=0 := by
    induction b with
    | done => rfl
    | unitary g b ih => simp [gidneyGateCount,ih]
    | xMeasureReset w b c ihb ihc => simp [gidneyGateCount,ihb,ihc]
  rw [hz,Nat.add_zero] at hc
  exact ⟨hx,hc⟩

/-- Removing a constant control preserves H, Toffoli, phase and measurement counts. -/
theorem primitiveResources_constantControl_preserved (q : Wire) (a : AdaptiveCircuit) :
    (primitiveResources (constantControlProgram q a)).h=(primitiveResources a).h ∧
    (primitiveResources (constantControlProgram q a)).toffoli=(primitiveResources a).toffoli ∧
    (primitiveResources (constantControlProgram q a)).phase=(primitiveResources a).phase ∧
    (primitiveResources (constantControlProgram q a)).measurements=(primitiveResources a).measurements := by
  have hh := primitiveCost_constantControl primitiveHCost q
    (by
      intro g
      cases g with
      | CX c t => by_cases hc : c=q <;> simp [constantControlGate,hc,primitiveHCost]
      | _ => rfl) a
  have ht := primitiveCost_constantControl (fun g => match g with | .CCX _ _ _ => 1 | _ => 0) q
    (by
      intro g
      cases g with
      | CX c t => by_cases hc : c=q <;> simp [constantControlGate,hc]
      | _ => rfl) a
  have hp := primitiveCost_constantControl primitivePhaseCost q
    (by
      intro g
      cases g with
      | CX c t => by_cases hc : c=q <;> simp [constantControlGate,hc,primitivePhaseCost]
      | _ => rfl) a
  exact ⟨hh,ht,hp,constantControlProgram_measurements q a⟩
end ShorECDLP.Paper2607_13816
