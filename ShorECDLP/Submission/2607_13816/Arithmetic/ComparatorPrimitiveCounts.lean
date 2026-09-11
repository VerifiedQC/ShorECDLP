import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantCompare
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledLT
import ShorECDLP.Submission.«2607_13816».Arithmetic.PrimitiveTransforms
namespace ShorECDLP.Paper2607_13816
/-- All six primitive budgets for a 256-bit carry comparison. -/
theorem controlledGidneyCompareCarry256_primitive_bounds (input dirty : List Wire)
    (constant : List Bool) (q c r t f : Wire)
    (hi : input.length=256) (hd : dirty.length=256) (hk : constant.length=256) :
    let v := primitiveResources (controlledGidneyCompareCarry input dirty constant q c r t f)
    v.x≤512 ∧ v.h≤1024 ∧ v.cnot≤3839 ∧ v.toffoli≤767 ∧ v.phase=0 ∧ v.measurements≤256 := by
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
        have hki : input.length=constant.length := by simp_all
        have hdi : input.length=dirty.length := by simp_all
        have hx := controlledGidneyCompareCarry_XH_le a d q c r t f input dirty k constant hki hdi
        have hc := controlledGidneyCompareCarry_cnot_le a d q c r t f input dirty k constant hki hdi
        have hp := controlledGidneyCompareCarry_phase_zero a d q c r t f input dirty k constant hki hdi
        have hm := controlledGidneyCompareCarry_metrics a d q c r t f input dirty k constant hki hdi
        dsimp only [primitiveResources] at hx hp ⊢
        simp only [hi'] at hx hc hm
        exact ⟨hx.1,hx.2,hc,hm.1.le,hp,hm.2.2.le⟩

/-- Threshold shortcuts preserve the carry core's primitive budget. -/
theorem controlledGidneyCompareGE256_primitive_bounds (input dirty : List Wire)
    (threshold : Nat) (q c r t f : Wire) (hi : input.length=256) (hd : dirty.length=256) :
    let v := primitiveResources (controlledGidneyCompareGE input dirty threshold q c r t f)
    v.x≤512 ∧ v.h≤1024 ∧ v.cnot≤3839 ∧ v.toffoli≤767 ∧ v.phase=0 ∧ v.measurements≤256 := by
  unfold controlledGidneyCompareGE
  split
  · simp [primitiveResources,primitiveXCost,primitiveHCost,primitivePhaseCost,
      gidneyCnotCount,gidneyToffoliCount,gidneyGateCount,Quantum.AdaptiveCircuit.measurementCount]
  split
  · simp [primitiveResources,gidneyCnotCount,gidneyToffoliCount,gidneyGateCount,
      Quantum.AdaptiveCircuit.measurementCount]
  · exact controlledGidneyCompareCarry256_primitive_bounds input dirty _ q c r t f hi hd (by simp [hi])

end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- The less-than wrapper adds at most its one flag CNOT. -/
theorem controlledGidneyCompareLT256_primitive_bounds (input dirty : List Wire)
    (threshold : Nat) (q c r t f : Wire) (hi : input.length=256) (hd : dirty.length=256) :
    let v := primitiveResources (controlledGidneyCompareLT input dirty threshold q c r t f)
    v.x≤512 ∧ v.h≤1024 ∧ v.cnot≤3840 ∧ v.toffoli≤767 ∧ v.phase=0 ∧ v.measurements≤256 := by
  unfold controlledGidneyCompareLT
  split
  · simp [primitiveResources,gidneyCnotCount,gidneyToffoliCount,gidneyGateCount,
      Quantum.AdaptiveCircuit.measurementCount]
  split
  · simp [primitiveResources,primitiveXCost,primitiveHCost,primitivePhaseCost,
      gidneyCnotCount,gidneyToffoliCount,gidneyGateCount,Quantum.AdaptiveCircuit.measurementCount]
  · have hh := controlledGidneyCompareGE256_primitive_bounds input dirty threshold q c r t f hi hd
    dsimp only [primitiveResources,gidneyCnotCount,gidneyToffoliCount] at hh ⊢
    simp only [gidneyGateCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      primitiveXCost,primitiveHCost,primitivePhaseCost,Nat.zero_add,Nat.add_zero,
      Quantum.AdaptiveCircuit.measurementCount]
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- The uncontrolled threshold comparator is budgeted after virtual-control elimination. -/
theorem gidneyCompareGE256_primitive_bounds (input dirty : List Wire)
    (threshold : Nat) (c r t f : Wire) (hi : input.length=256) (hd : dirty.length=256) :
    let v := primitiveResources (gidneyCompareGE input dirty threshold c r t f)
    v.x≤4351 ∧ v.h≤1024 ∧ v.cnot≤3839 ∧ v.toffoli≤767 ∧ v.phase=0 ∧ v.measurements≤256 := by
  have bound (q : Wire) :
      let v := primitiveResources (constantControlProgram q
        (controlledGidneyCompareGE input dirty threshold q c r t f))
      v.x≤4351 ∧ v.h≤1024 ∧ v.cnot≤3839 ∧ v.toffoli≤767 ∧ v.phase=0 ∧ v.measurements≤256 := by
    have hh := controlledGidneyCompareGE256_primitive_bounds input dirty threshold q c r t f hi hd
    have hb := primitiveResources_constantControl_bounds q
      (controlledGidneyCompareGE input dirty threshold q c r t f)
    have hp := primitiveResources_constantControl_preserved q
      (controlledGidneyCompareGE input dirty threshold q c r t f)
    dsimp only at hh ⊢
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
  unfold gidneyCompareGE
  exact bound _

/-- The uncontrolled LT wrapper contributes at most one extra X gate. -/
theorem gidneyCompareLT256_primitive_bounds (input dirty : List Wire)
    (threshold : Nat) (c r t f : Wire) (hi : input.length=256) (hd : dirty.length=256) :
    let v := primitiveResources (gidneyCompareLT input dirty threshold c r t f)
    v.x≤4352 ∧ v.h≤1024 ∧ v.cnot≤3839 ∧ v.toffoli≤767 ∧ v.phase=0 ∧ v.measurements≤256 := by
  unfold gidneyCompareLT
  split
  · simp [primitiveResources,gidneyCnotCount,gidneyToffoliCount,gidneyGateCount,
      Quantum.AdaptiveCircuit.measurementCount]
  split
  · simp [primitiveResources,primitiveXCost,primitiveHCost,primitivePhaseCost,
      gidneyCnotCount,gidneyToffoliCount,gidneyGateCount,Quantum.AdaptiveCircuit.measurementCount]
  · have hh := gidneyCompareGE256_primitive_bounds input dirty threshold c r t f hi hd
    dsimp only [primitiveResources,gidneyCnotCount,gidneyToffoliCount] at hh ⊢
    simp only [gidneyGateCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      primitiveXCost,primitiveHCost,primitivePhaseCost,Nat.zero_add,Nat.add_zero,
      Quantum.AdaptiveCircuit.measurementCount]
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- The exact controlled 256-bit GE vector includes both threshold shortcuts. -/
theorem controlledGidneyCompareGE256_primitive_exact (input dirty : List Wire) (p : Nat)
    (q c r t f : Wire) (hi : input.length=256) (hd : dirty.length=256) :
    let bits := (List.range 256).map (Nat.testBit (2^256-p))
    let extra := 7*(bits.headD false).toNat+9*constantBitWeight bits.tail
    primitiveResources (controlledGidneyCompareGE input dirty p q c r t f)=
      if p=0 then (⟨0,0,1,0,0,0⟩ : PrimitiveResources)
      else if 2^256≤p then ⟨0,0,0,0,0,0⟩ else ⟨512,1024,1537+extra,767,0,256⟩ := by
  dsimp only
  by_cases hz : p=0
  · rw [if_pos hz]
    simp only [controlledGidneyCompareGE,if_pos hz]
    rfl
  by_cases hb : 2^256≤p
  · rw [if_neg hz,if_pos hb]
    simp only [controlledGidneyCompareGE,if_neg hz,hi,if_pos hb]
    rfl
  rw [if_neg hz,if_neg hb]
  cases input with
  | nil => simp at hi
  | cons a input =>
    have hi' : input.length=255 := by simpa using hi
    have h := controlledGidneyCompareGE_primitive_exact a input dirty p q c r t f (by omega) (by omega) (by simpa only [List.length_cons,hi',Nat.reduceAdd] using Nat.lt_of_not_ge hb)
    simpa only [List.length_cons,hi',Nat.reduceAdd,Nat.reduceMul,Nat.add_assoc] using h
/-- The actual unconditional 256-bit GE comparator has an exact vector for every threshold. -/
theorem gidneyCompareGE256_primitive_exact (input dirty : List Wire) (p : Nat)
    (c r t f : Wire) (hi : input.length=256) (hd : dirty.length=256) :
    let bits := (List.range 256).map (Nat.testBit (2^256-p))
    let extra := 7*(bits.headD false).toNat+9*constantBitWeight bits.tail
    primitiveResources (gidneyCompareGE input dirty p c r t f)=
      if p=0 then (⟨1,0,0,0,0,0⟩ : PrimitiveResources)
      else if 2^256≤p then ⟨0,0,0,0,0,0⟩ else ⟨512+extra,1024,1537,767,0,256⟩ := by
  dsimp only
  by_cases hz : p=0
  · rw [if_pos hz]
    simp only [gidneyCompareGE,controlledGidneyCompareGE,if_pos hz]
    simp only [constantControlProgram,List.map_cons,List.map_nil,constantControlGate]
    rfl
  by_cases hb : 2^256≤p
  · rw [if_neg hz,if_pos hb]
    simp only [gidneyCompareGE,controlledGidneyCompareGE,if_neg hz,hi,if_pos hb]
    rfl
  rw [if_neg hz,if_neg hb]
  cases input with
  | nil => simp at hi
  | cons a input =>
    have hi' : input.length=255 := by simpa using hi
    have h := gidneyCompareGE_primitive_exact a input dirty p c r t f (by omega) (by omega) (by simpa only [List.length_cons,hi',Nat.reduceAdd] using Nat.lt_of_not_ge hb)
    simpa only [List.length_cons,hi',Nat.reduceAdd,Nat.reduceMul,Nat.add_assoc] using h
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- Exact controlled LT counts preserve its distinct zero and out-of-range shortcuts. -/
theorem controlledGidneyCompareLT256_primitive_exact (input dirty : List Wire) (p : Nat)
    (q c r t f : Wire) (hi : input.length=256) (hd : dirty.length=256) :
    let bits := (List.range 256).map (Nat.testBit (2^256-p))
    let extra := 7*(bits.headD false).toNat+9*constantBitWeight bits.tail
    primitiveResources (controlledGidneyCompareLT input dirty p q c r t f)=
      if p=0 then (⟨0,0,0,0,0,0⟩ : PrimitiveResources)
      else if 2^256≤p then ⟨0,0,1,0,0,0⟩ else ⟨512,1024,1538+extra,767,0,256⟩ := by
  dsimp only
  by_cases hz : p=0
  · rw [if_pos hz]
    simp only [controlledGidneyCompareLT,if_pos hz]
    rfl
  by_cases hb : 2^256≤p
  · rw [if_neg hz,if_pos hb]
    simp only [controlledGidneyCompareLT,if_neg hz,hi,if_pos hb]
    rfl
  rw [if_neg hz,if_neg hb]
  simp only [controlledGidneyCompareLT,if_neg hz,hi,if_neg hb]
  change primitiveResources ((Quantum.AdaptiveCircuit.unitary [.CX q f] .done).seq
    (controlledGidneyCompareGE input dirty p q c r t f))=_
  rw [primitiveResources_seq,controlledGidneyCompareGE256_primitive_exact input dirty p q c r t f hi hd]
  simp only [if_neg hz,if_neg hb]
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
    primitiveXCost,primitiveHCost,primitivePhaseCost,Quantum.AdaptiveCircuit.measurementCount]
  omega
/-- Exact unconditional LT counts include the single final flag complement. -/
theorem gidneyCompareLT256_primitive_exact (input dirty : List Wire) (p : Nat)
    (c r t f : Wire) (hi : input.length=256) (hd : dirty.length=256) :
    let bits := (List.range 256).map (Nat.testBit (2^256-p))
    let extra := 7*(bits.headD false).toNat+9*constantBitWeight bits.tail
    primitiveResources (gidneyCompareLT input dirty p c r t f)=
      if p=0 then (⟨0,0,0,0,0,0⟩ : PrimitiveResources)
      else if 2^256≤p then ⟨1,0,0,0,0,0⟩ else ⟨513+extra,1024,1537,767,0,256⟩ := by
  dsimp only
  by_cases hz : p=0
  · rw [if_pos hz]
    simp only [gidneyCompareLT,if_pos hz]
    rfl
  by_cases hb : 2^256≤p
  · rw [if_neg hz,if_pos hb]
    simp only [gidneyCompareLT,if_neg hz,hi,if_pos hb]
    rfl
  rw [if_neg hz,if_neg hb]
  simp only [gidneyCompareLT,if_neg hz,hi,if_neg hb]
  change primitiveResources ((Quantum.AdaptiveCircuit.unitary [.X f] .done).seq
    (gidneyCompareGE input dirty p c r t f))=_
  rw [primitiveResources_seq,gidneyCompareGE256_primitive_exact input dirty p c r t f hi hd]
  simp only [if_neg hz,if_neg hb]
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
    primitiveXCost,primitiveHCost,primitivePhaseCost,Quantum.AdaptiveCircuit.measurementCount]
  omega
end ShorECDLP.Paper2607_13816
