import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyCarry
namespace ShorECDLP.Paper2607_13816
open Quantum

theorem modularGateCount_seq (cost : Gate → Nat) (a b : Quantum.AdaptiveCircuit) :
    gidneyGateCount cost (a.seq b) = gidneyGateCount cost a + gidneyGateCount cost b := by
  induction a with
  | done => simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount]
  | unitary gates next ih => simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount,ih,Nat.add_assoc]
  | xMeasureReset w l r ihl ihr =>
      simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount,ihl,ihr,max_add_add_right]

theorem modularMeasurements_seq (a b : Quantum.AdaptiveCircuit) :
    (a.seq b).measurementCount = a.measurementCount + b.measurementCount := by
  induction a with
  | done => simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.measurementCount]
  | unitary gates next ih => exact ih
  | xMeasureReset w l r ihl ihr =>
      simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.measurementCount,ihl,ihr,
        max_add_add_right,Nat.add_assoc]

/-- Primitive counts of the lowered adaptive circuit, componentwise worst case.
Logical table lookups and classical correction events need separate source-level
accounting; they are not inferred from these primitive gate counts. -/
structure PrimitiveResources where
  x : Nat
  h : Nat
  cnot : Nat
  toffoli : Nat
  phase : Nat
  measurements : Nat
  deriving DecidableEq, Repr

def PrimitiveResources.add (a b : PrimitiveResources) : PrimitiveResources :=
  ⟨a.x+b.x,a.h+b.h,a.cnot+b.cnot,a.toffoli+b.toffoli,a.phase+b.phase,a.measurements+b.measurements⟩
def PrimitiveResources.branch (a b : PrimitiveResources) : PrimitiveResources :=
  ⟨max a.x b.x,max a.h b.h,max a.cnot b.cnot,max a.toffoli b.toffoli,max a.phase b.phase,
    1+max a.measurements b.measurements⟩

def primitiveXCost : Gate → Nat | .X _ => 1 | _ => 0
def primitiveHCost : Gate → Nat | .H _ => 1 | _ => 0
def primitivePhaseCost : Gate → Nat | .P _ _ _ => 1 | _ => 0
/-- Classical reversible gates introduce no dyadic phase rotations. -/
theorem primitivePhaseCost_of_HPFree (g : Circuit) (hg : Classical.HPFree g) :
    (g.map primitivePhaseCost).sum = 0 := by
  induction g with
  | nil => rfl
  | cons a g ih =>
    have ha := hg a (by simp)
    have ht : Classical.HPFree g := by intro b hb; exact hg b (by simp [hb])
    cases a <;> simp_all [Classical.IsClassicalGate,primitivePhaseCost]

def primitiveResources (a : AdaptiveCircuit) : PrimitiveResources :=
  ⟨gidneyGateCount primitiveXCost a,gidneyGateCount primitiveHCost a,gidneyCnotCount a,
    gidneyToffoliCount a,gidneyGateCount primitivePhaseCost a,a.measurementCount⟩

theorem primitiveResources_seq (a b : AdaptiveCircuit) :
    primitiveResources (a.seq b)=(primitiveResources a).add (primitiveResources b) := by
  simp only [primitiveResources,PrimitiveResources.add,gidneyCnotCount,gidneyToffoliCount,
    modularGateCount_seq,modularMeasurements_seq]
theorem primitiveResources_branch (w : Wire) (a b : AdaptiveCircuit) :
    primitiveResources (.xMeasureReset w a b)=(primitiveResources a).branch (primitiveResources b) := by
  rfl
private def ccxCost : Gate → Nat | .CCX _ _ _ => 1 | _ => 0
private theorem unitary_T (g : Circuit) :
    tCount g=7*(g.map ccxCost).sum+(g.map primitivePhaseCost).sum := by
  induction g with
  | nil => rfl
  | cons a g ih =>
    change (g.map tCost).sum=7*(g.map ccxCost).sum+(g.map primitivePhaseCost).sum at ih
    cases a <;> simp [tCount,tCost,ccxCost,primitivePhaseCost,ih] <;> omega
/-- Converting independent component maxima to T gives an upper bound in general. -/
theorem primitiveResources_T_le (a : AdaptiveCircuit) :
    a.tCount≤7*(primitiveResources a).toffoli+(primitiveResources a).phase := by
  change a.tCount≤7*gidneyGateCount ccxCost a+gidneyGateCount primitivePhaseCost a
  induction a with
  | done => simp [AdaptiveCircuit.tCount,gidneyGateCount]
  | unitary g a ih =>
    simp only [AdaptiveCircuit.tCount,gidneyGateCount,unitary_T]
    omega
  | xMeasureReset w a b iha ihb =>
    simp only [AdaptiveCircuit.tCount,gidneyGateCount]
    omega
/-- With no phase rotations, the current seven-T Toffoli synthesis is exact. -/
theorem primitiveResources_T_of_no_phase (a : AdaptiveCircuit)
    (hp : (primitiveResources a).phase=0) : a.tCount=7*(primitiveResources a).toffoli := by
  change gidneyGateCount primitivePhaseCost a=0 at hp
  change a.tCount=7*gidneyGateCount ccxCost a
  induction a with
  | done => rfl
  | unitary g a ih =>
    simp only [gidneyGateCount] at hp
    have hg : (g.map primitivePhaseCost).sum=0 := by omega
    have ha : gidneyGateCount primitivePhaseCost a=0 := by omega
    simp only [AdaptiveCircuit.tCount,gidneyGateCount,unitary_T,hg,ih ha]
    omega
  | xMeasureReset w a b iha ihb =>
    simp only [gidneyGateCount] at hp
    have ha : gidneyGateCount primitivePhaseCost a=0 := by omega
    have hb : gidneyGateCount primitivePhaseCost b=0 := by omega
    simp only [AdaptiveCircuit.tCount,gidneyGateCount,iha ha,ihb hb]
    omega
end ShorECDLP.Paper2607_13816
