import ShorECDLP.Submission.«2607_13816».EEA.ControlPrimitiveCounts
import ShorECDLP.Framework.Quantum.AdaptiveMeasurement
import ShorECDLP.Framework.Quantum.Relabel
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Wire relabeling preserves each primitive count on the actual adaptive tree. -/
theorem primitiveResources_relabel (e : Wire ≃ Wire) (a : AdaptiveCircuit) :
    primitiveResources (a.relabel e)=primitiveResources a := by
  have hc (cost : Gate → Nat) (h : ∀ g, cost (g.relabel e)=cost g) :
      ∀ a, gidneyGateCount cost (a.relabel e)=gidneyGateCount cost a := by
    intro a
    induction a with
    | done => rfl
    | unitary g a ih =>
      simp only [AdaptiveCircuit.relabel,gidneyGateCount,ih,List.map_map,Function.comp_def,h]
    | xMeasureReset w a b iha ihb =>
      simp only [AdaptiveCircuit.relabel,gidneyGateCount,iha,ihb]
  have hx := hc primitiveXCost (by intro g; cases g <;> rfl) a
  have hh := hc primitiveHCost (by intro g; cases g <;> rfl) a
  have hp := hc primitivePhaseCost (by intro g; cases g <;> rfl) a
  have hcx := hc (fun g => match g with | .CX _ _ => 1 | _ => 0) (by intro g; cases g <;> rfl) a
  have hccx := hc (fun g => match g with | .CCX _ _ _ => 1 | _ => 0) (by intro g; cases g <;> rfl) a
  change gidneyCnotCount (a.relabel e)=gidneyCnotCount a at hcx
  change gidneyToffoliCount (a.relabel e)=gidneyToffoliCount a at hccx
  simp only [primitiveResources,hx,hh,hp,hcx,hccx,
    AdaptiveCircuit.relabel_measurementCount]
/-- Each selected logical Z is the actual H-X-H Clifford stream. -/
theorem registerZCorrection_primitive (targets : List Wire) (outcomes : List Bool)
    (hl : targets.length=outcomes.length) :
    primitiveResources (.unitary (registerZCorrection targets outcomes) .done)=
      (⟨outcomes.count true,2*outcomes.count true,0,0,0,0⟩ : PrimitiveResources) := by
  induction targets generalizing outcomes with
  | nil =>
    have ho : outcomes=[] := by simpa using hl.symm
    subst outcomes
    rfl
  | cons w ws ih =>
    cases outcomes with
    | nil => simp at hl
    | cons b bs =>
      have hlen : ws.length=bs.length := by simpa using hl
      cases b with
      | false => simpa only [registerZCorrection, Bool.false_eq_true, ↓reduceIte, List.nil_append,
          List.count_cons, ↓reduceIte, Nat.add_zero] using ih bs hlen
      | true =>
        change primitiveResources (.unitary (pauliZ w ++ registerZCorrection ws bs) .done)=_
        rw [primitiveResources_unitary_append,ih bs hlen]
        have hp : primitiveResources (.unitary (pauliZ w) .done)=(⟨1,2,0,0,0,0⟩ : PrimitiveResources) := rfl
        rw [hp]
        simp [PrimitiveResources.add,Nat.mul_add,Nat.add_comm]
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Reset all targets and then bound every history-dependent continuation. -/
theorem measureResetThen_primitive_bounds (targets : List Wire) (next : List Bool → AdaptiveCircuit)
    (bound : PrimitiveResources)
    (h : ∀ bs, bs.length=targets.length →
      let v := primitiveResources (next bs)
      v.x≤bound.x ∧ v.h≤bound.h ∧ v.cnot≤bound.cnot ∧ v.toffoli≤bound.toffoli ∧
        v.phase=0 ∧ v.measurements≤bound.measurements) :
    let v := primitiveResources (measureResetThen targets next)
    v.x≤bound.x ∧ v.h≤bound.h ∧ v.cnot≤bound.cnot ∧ v.toffoli≤bound.toffoli ∧
      v.phase=0 ∧ v.measurements≤targets.length+bound.measurements := by
  induction targets generalizing next with
  | nil => simpa only [measureResetThen,List.length_nil,Nat.zero_add] using h [] rfl
  | cons w ws ih =>
    have h0 := ih (fun bs => next (false::bs)) (by intro bs hb; exact h _ (by simp [hb]))
    have h1 := ih (fun bs => next (true::bs)) (by intro bs hb; exact h _ (by simp [hb]))
    dsimp only at h0 h1 ⊢
    rw [measureResetThen,primitiveResources_branch]
    simp only [PrimitiveResources.branch,List.length_cons]
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
end ShorECDLP.Paper2607_13816
