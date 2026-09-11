import ShorECDLP.Submission.«2607_13816».Arithmetic.PrimitiveResources
import ShorECDLP.Submission.«2607_13816».Arithmetic.Halving
namespace ShorECDLP.Paper2607_13816
open Quantum

theorem primitiveHCost_of_HPFree (g : Circuit) (hg : Classical.HPFree g) :
    (g.map primitiveHCost).sum = 0 := by
  induction g with
  | nil => rfl
  | cons a g ih =>
    have ha := hg a (by simp)
    have ht : Classical.HPFree g := by intro b hb; exact hg b (by simp [hb])
    cases a <;> simp_all [Classical.IsClassicalGate,primitiveHCost]

theorem primitiveResources_unitary_HPFree (g : Circuit) (next : AdaptiveCircuit)
    (hg : Classical.HPFree g) :
    primitiveResources (.unitary g next) =
      (⟨eeaXCount g,0,eeaCnotCount g,eeaToffoliCount g,0,0⟩ : PrimitiveResources).add
        (primitiveResources next) := by
  have hh := primitiveHCost_of_HPFree g hg
  have hp := primitivePhaseCost_of_HPFree g hg
  simp only [primitiveResources,PrimitiveResources.add,gidneyCnotCount,gidneyToffoliCount,
    gidneyGateCount,AdaptiveCircuit.measurementCount,hh,hp,Nat.zero_add]
  rfl

/-- Adjoint changes order and phase signs, but none of the six primitive counts. -/
theorem primitiveResources_unitary_adjoint (g : Circuit) (next : AdaptiveCircuit) :
    primitiveResources (.unitary g.adjoint next)=primitiveResources (.unitary g next) := by
  have hcost (cost : Gate → Nat) (hc : ∀ a, cost a.adjoint=cost a) :
      (g.adjoint.map cost).sum=(g.map cost).sum := by
    change ((g.reverse.map Gate.adjoint).map cost).sum = _
    simp only [List.map_map,Function.comp_def,hc,List.map_reverse,List.sum_reverse]
  have hx := hcost primitiveXCost (by intro a; cases a <;> rfl)
  have hh := hcost primitiveHCost (by intro a; cases a <;> rfl)
  have hp := hcost primitivePhaseCost (by intro a; cases a <;> rfl)
  have hc := hcost (fun a => match a with | .CX _ _ => 1 | _ => 0)
    (by intro a; cases a <;> rfl)
  have ht := hcost (fun a => match a with | .CCX _ _ _ => 1 | _ => 0)
    (by intro a; cases a <;> rfl)
  simp only [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
    AdaptiveCircuit.measurementCount,hx,hh,hp]
  congr 1
  · exact congrArg (fun n => n + _) hc
  · exact congrArg (fun n => n + _) ht

theorem controlledAddCarry_xCount (bs as : List Wire) (q c f : Wire) :
    eeaXCount (controlledAddCarry bs as q c f)=0 := by
  induction bs generalizing as with
  | nil => cases as <;> simp [controlledAddCarry,eeaXCount]
  | cons b bs ih =>
    cases as with
    | nil => rfl
    | cons a as =>
      rw [controlledAddCarry,eeaXCount_append,eeaXCount_append,ih]
      rfl

theorem controlledAddCarry256_primitive (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) (next : AdaptiveCircuit) :
    primitiveResources (.unitary (controlledAddCarry bs as q c f) next) =
      (⟨0,0,1024,769,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  rw [primitiveResources_unitary_HPFree _ _ (controlledAddCarry_HPFree bs as q c f),
    controlledAddCarry_xCount,controlledAddCarry_cnotCount _ _ _ _ _ (hb.trans ha.symm),
    controlledAddCarry_toffoliCount _ _ _ _ _ (hb.trans ha.symm),hb]

theorem controlledSubCarry256_primitive (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) (next : AdaptiveCircuit) :
    primitiveResources (.unitary (controlledSubCarry bs as q c f) next) =
      (⟨0,0,1024,769,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  rw [primitiveResources_unitary_HPFree _ _ (controlledSubCarry_HPFree bs as q c f)]
  simp only [controlledSubCarry,eeaXCount_adjoint,eeaCnotCount_adjoint,eeaToffoliCount_adjoint,
    controlledAddCarry_xCount,controlledAddCarry_cnotCount _ _ _ _ _ (hb.trans ha.symm),
    controlledAddCarry_toffoliCount _ _ _ _ _ (hb.trans ha.symm),hb]

theorem controlledCompareLT256_primitive (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) (next : AdaptiveCircuit) :
    primitiveResources (.unitary (controlledCompareLT bs as q c f) next) =
      (⟨516,0,1024,513,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  rw [primitiveResources_unitary_HPFree _ _ (controlledCompareLT_HPFree bs as q c f)]
  cases bs with
  | nil => simp at hb
  | cons b bs =>
    have h := controlledCompareLT_counts b bs as q c f (hb.trans ha.symm)
    simp only [List.length_cons] at hb
    rw [h.1,h.2.1,h.2.2.1,hb]

private theorem doublingRotate_xCount (acc : List Wire) : eeaXCount (doublingRotate acc)=0 := by
  induction acc with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      rw [doublingRotate,eeaXCount_append,ih]
      rfl

theorem doublingShift_xCount (acc : List Wire) (f : Wire) : eeaXCount (doublingShift acc f)=0 := by
  cases acc with
  | nil => rfl
  | cons a rest =>
    rw [doublingShift,eeaXCount_append,eeaXCount_append,doublingRotate_xCount]
    rfl

theorem doublingShift256_primitive (acc : List Wire) (f : Wire)
    (ha : acc.length=256) (next : AdaptiveCircuit) :
    primitiveResources (.unitary (doublingShift acc f) next) =
      (⟨0,0,767,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  rw [primitiveResources_unitary_HPFree _ _ (doublingShift_HPFree acc f),doublingShift_xCount]
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have h := doublingShift_counts a f rest
    rw [h.1,h.2.1]
    have hr : rest.length=255 := by simpa using ha
    rw [hr]
end ShorECDLP.Paper2607_13816
