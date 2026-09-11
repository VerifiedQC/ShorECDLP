import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.SelectorPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.StepControl
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem zeroMaskFrom_control_xCount (r : List Wire) (v k : Nat) :
    eeaXCount (zeroMaskFrom r v k)=zeroBitCount v k r.length := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [zeroMaskFrom,eeaXCount_append,ih,List.length_cons,zeroBitCount]
    split <;> rfl

theorem mcxVChain_control_xCount (r : List Wire) (target : Wire) (scratch : List Wire) :
    eeaXCount (mcxVChain r target scratch)=(if r.length=0 then 1 else 0) := by
  cases r with
  | nil => rfl
  | cons a rs =>
    cases rs with
    | nil => rfl
    | cons b rs =>
      exact mcxVChain_stepControl_xCount_of_two_le _ _ _ (by simp)

theorem computeControl_primitive (r : List Wire) (v : Nat) (target : Wire) (scratch : List Wire)
    (hs : r.length-2≤scratch.length) :
    primitiveResources (.unitary (computeControl r v target scratch) .done)=
      (⟨2*zeroBitCount v 0 r.length+(if r.length=0 then 1 else 0),0,
        mcxVChainCnotCost r.length,mcxVChainToffoliCost r.length,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (computeControl_HPFree _ _ _ _),
    computeControl_xCount,computeControl_cnotCount,computeControl_toffoliCount _ _ _ _ hs,
    mcxVChain_control_xCount]
  simp only [zeroMask,zeroMaskFrom_control_xCount,primitiveResources,PrimitiveResources.add]
  rfl

theorem rControlNonterminal_primitive (cs : List Wire) (v : Nat) (control : Wire)
    (r : List Wire) (zeroFlag : Wire) (scratch : List Wire)
    (hr : r.length-2≤scratch.length) (hc : cs.length+1-2≤scratch.length) :
    primitiveResources (.unitary (rControlNonterminal cs v control r zeroFlag scratch) .done)=
      (⟨2*(if r.length=0 then 1 else 0)+2*zeroBitCount (v%2^cs.length) 0 (cs.length+1),0,
        2*mcxVChainCnotCost r.length+mcxVChainCnotCost (cs.length+1),
        2*mcxVChainToffoliCost r.length+mcxVChainToffoliCost (cs.length+1),0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (rControlNonterminal_HPFree _ _ _ _ _ _),
    rControlNonterminal_cnotCount,rControlNonterminal_toffoliCount _ _ _ _ _ _ hr hc]
  have hx : eeaXCount (rControlNonterminal cs v control r zeroFlag scratch)=
      2*(if r.length=0 then 1 else 0)+2*zeroBitCount (v%2^cs.length) 0 (cs.length+1) := by
    simp only [rControlNonterminal,eeaXCount_append,computeControl_xCount,
      mcxVChain_control_xCount,zeroMask,zeroMaskFrom_control_xCount,List.length_append,List.length_singleton]
    split <;> split <;> omega
  rw [hx]
  simp only [primitiveResources,PrimitiveResources.add]
  rfl

/-- Concatenated coherent stages add their complete primitive vectors. -/
theorem primitiveResources_unitary_append (a b : Circuit) :
    primitiveResources (.unitary (a++b) .done)=
      (primitiveResources (.unitary a .done)).add (primitiveResources (.unitary b .done)) := by
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,AdaptiveCircuit.measurementCount,List.map_append,List.sum_append]

end ShorECDLP.Paper2607_13816
