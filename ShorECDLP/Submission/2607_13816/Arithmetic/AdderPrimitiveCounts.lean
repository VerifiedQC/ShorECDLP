import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledAdd
import ShorECDLP.Submission.«2607_13816».Arithmetic.PrimitiveTransforms
namespace ShorECDLP.Paper2607_13816
/-- A full primitive budget for arbitrary 256-bit constant patterns. -/
theorem controlledGidneyAddConst256_primitive_bounds
    (input dirty : List Wire) (constant : List Bool) (q c r t : Wire)
    (hi : input.length=256) (hd : dirty.length=255) (hk : constant.length=256) :
    let v := primitiveResources (controlledGidneyAddConst input dirty constant q c r t)
    v.x ≤ 1022 ∧ v.h ≤ 1020 ∧ v.cnot ≤ 3825 ∧ v.toffoli ≤ 764 ∧
      v.phase=0 ∧ v.measurements ≤ 255 := by
  cases input with
  | nil => simp at hi
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        have hi' : input.length=255 := by simpa using hi
        have hd' : dirty.length=254 := by simpa using hd
        have hki : input.length=constant.length := by simp_all
        have hdi : input.length=dirty.length+1 := by omega
        have hx := controlledGidneyAddConst_XH_le a d q c r t k input dirty constant hki hdi
        have hc := controlledGidneyAddConst_cnot_le a d q c r t k input dirty constant hki hdi
        have hp := controlledGidneyAddConst_phase_zero a d q c r t k input dirty constant hki hdi
        by_cases hz : (k :: constant).all (fun b => !b)=true
        · simp [controlledGidneyAddConst,hz,primitiveResources,gidneyCnotCount,gidneyToffoliCount,
            gidneyGateCount,Quantum.AdaptiveCircuit.measurementCount]
        have ht := controlledGidneyAddConst_toffoli_nonzero a d q c r t k input dirty constant hki hdi hz
        have hm := controlledGidneyAddConst_measurementCount (a :: input) (d :: dirty)
          (k :: constant) q c r t (by simp [hki]) (by simp [hdi])
        dsimp only [primitiveResources] at hx hp ⊢
        simp only [hi'] at hx hc ht
        simp only [hz,Bool.false_eq_true,if_false,List.length_cons,hd'] at hm
        exact ⟨hx.1,hx.2,hc,ht.le,hp,hm.le⟩

end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- A primitive budget after lowering the external control to one. -/
theorem controlledGidneyAddConst256_lowered_bounds
    (input dirty : List Wire) (constant : List Bool) (q c r t : Wire)
    (hi : input.length=256) (hd : dirty.length=255) (hk : constant.length=256) :
    let v := primitiveResources (constantControlProgram q
      (controlledGidneyAddConst input dirty constant q c r t))
    v.x ≤ 4847 ∧ v.h ≤ 1020 ∧ v.cnot ≤ 3825 ∧ v.toffoli ≤ 764 ∧
      v.phase=0 ∧ v.measurements ≤ 255 := by
  have hb := controlledGidneyAddConst256_primitive_bounds input dirty constant q c r t hi hd hk
  have hx := primitiveResources_constantControl_bounds q
    (controlledGidneyAddConst input dirty constant q c r t)
  have hp := primitiveResources_constantControl_preserved q
    (controlledGidneyAddConst input dirty constant q c r t)
  dsimp only at hb ⊢
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- The unconditional 256-bit adder inherits the lowered circuit's primitive budget. -/
theorem gidneyAddConst256_primitive_bounds
    (input dirty : List Wire) (constant : List Bool) (c r t : Wire)
    (hi : input.length=256) (hd : dirty.length=255) (hk : constant.length=256) :
    let v := primitiveResources (gidneyAddConst input dirty constant c r t)
    v.x ≤ 4847 ∧ v.h ≤ 1020 ∧ v.cnot ≤ 3825 ∧ v.toffoli ≤ 764 ∧
      v.phase=0 ∧ v.measurements ≤ 255 := by
  unfold gidneyAddConst
  exact controlledGidneyAddConst256_lowered_bounds input dirty constant _ c r t hi hd hk
end ShorECDLP.Paper2607_13816
