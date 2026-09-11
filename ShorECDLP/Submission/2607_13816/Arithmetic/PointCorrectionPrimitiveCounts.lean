import ShorECDLP.Submission.«2607_13816».Arithmetic.PointPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCorrectionResources
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem sandwich_primitive (a b : Circuit) :
    primitiveResources (.unitary ((a++b)++a) .done)=
      ((primitiveResources (.unitary a .done)).add (primitiveResources (.unitary b .done))).add
      (primitiveResources (.unitary a .done)) := by
  simp only [primitiveResources_unitary_append]
theorem toggleEqConstUnderControl_primitive (q : Wire) (r : List Wire) (v : Nat)
    (a f : Wire) (s : List Wire) (hs : r.length-2≤s.length) :
    primitiveResources (.unitary (toggleEqConstUnderControl q r v a f s) .done)=
      (⟨4*zeroBitCount v 0 r.length+2*(if r.length=0 then 1 else 0),0,
        2*mcxVChainCnotCost r.length,2*mcxVChainToffoliCost r.length+1,0,0⟩ : PrimitiveResources) := by
  rw [toggleEqConstUnderControl,sandwich_primitive,computeEqConst_primitive _ _ _ _ hs]
  have hg : primitiveResources (.unitary [Gate.CCX q f a] .done)=
      (⟨0,0,0,1,0,0⟩ : PrimitiveResources) := rfl
  rw [hg]
  by_cases hz : r.length=0
  · simp [PrimitiveResources.add,hz]; omega
  · simp [PrimitiveResources.add,hz]; omega

theorem twoRegisterControlledFlip_primitive (q t f g : Wire) (A B : List Wire)
    (a b : Nat) (scratch : List Wire) (hA : A.length-2≤scratch.length)
    (hB : B.length-2≤scratch.length) (hAn : A.length≠0) (hBn : B.length≠0) :
    primitiveResources (.unitary (twoRegisterControlledFlip q t f g A B a b scratch) .done)=
      (⟨8*zeroBitCount a 0 A.length+4*zeroBitCount b 0 B.length,0,
        4*mcxVChainCnotCost A.length+2*mcxVChainCnotCost B.length,
        4*mcxVChainToffoliCost A.length+2*mcxVChainToffoliCost B.length+3,0,0⟩ : PrimitiveResources) := by
  rw [twoRegisterControlledFlip,sandwich_primitive,
    toggleEqConstUnderControl_primitive _ _ _ _ _ _ hA,
    toggleEqConstUnderControl_primitive _ _ _ _ _ _ hB]
  simp only [hAn,hBn,if_false,PrimitiveResources.add]
  congr 1 <;> omega
/-- The physical edge uses exactly the masks of the two target-deleted banks. -/
theorem pointCorrectionEdge_primitive (t : Wire) (a b : Nat) :
    primitiveResources (.unitary (pointCorrectionEdge t a b) .done)=
      (⟨8*zeroBitCount a 0 (pointCorrectionX.erase t).length+
        4*zeroBitCount b 0 (pointCorrectionYInf.erase t).length,0,0,
        4*(2*(pointCorrectionX.erase t).length-3)+
        2*(2*(pointCorrectionYInf.erase t).length-3)+3,0,0⟩ : PrimitiveResources) := by
  have hAl : (pointCorrectionX.erase t).length≤256 := by
    simpa [pointCorrectionX] using (List.length_erase_le (a:=t) (l:=pointCorrectionX))
  have hBl : (pointCorrectionYInf.erase t).length≤257 := by
    simpa [pointCorrectionYInf] using (List.length_erase_le (a:=t) (l:=pointCorrectionYInf))
  have hAn : 255≤(pointCorrectionX.erase t).length := by
    by_cases h : t∈pointCorrectionX
    · rw [List.length_erase_of_mem h]; simp [pointCorrectionX]
    · rw [List.erase_of_not_mem h]; simp [pointCorrectionX]
  have hBn : 256≤(pointCorrectionYInf.erase t).length := by
    by_cases h : t∈pointCorrectionYInf
    · rw [List.length_erase_of_mem h]; simp [pointCorrectionYInf]
    · rw [List.erase_of_not_mem h]; simp [pointCorrectionYInf]
  rw [pointCorrectionEdge,twoRegisterControlledFlip_primitive _ _ _ _ _ _ _ _ _
    (by simp only [pointCorrectionScratch,List.length_range']; omega)
    (by simp only [pointCorrectionScratch,List.length_range']; omega)
    (by omega) (by omega)]
  have ht (n : Nat) (hn : 2≤n) : mcxVChainToffoliCost n=2*n-3 := by
    match n with
    | 0 => omega
    | 1 => omega
    | n+2 => simp only [mcxVChainToffoliCost]; omega
  rw [ht _ (by omega),ht _ (by omega)]
  simp [mcxVChainCnotCost,show (pointCorrectionX.erase t).length≠1 by omega,
    show (pointCorrectionYInf.erase t).length≠1 by omega]

private theorem zeroBitCount_le (v k n : Nat) : zeroBitCount v k n≤n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [zeroBitCount]
    have h := ih (k+1)
    split <;> omega
theorem pointCorrectionEdge_primitive_bounds (t : Wire) (a b : Nat) :
    let v := primitiveResources (.unitary (pointCorrectionEdge t a b) .done)
    v.x≤3076 ∧ v.h=0 ∧ v.cnot=0 ∧ v.toffoli≤3061 ∧ v.phase=0 ∧ v.measurements=0 := by
  rw [pointCorrectionEdge_primitive]
  have hAl : (pointCorrectionX.erase t).length≤256 := by
    simpa [pointCorrectionX] using (List.length_erase_le (a:=t) (l:=pointCorrectionX))
  have hBl : (pointCorrectionYInf.erase t).length≤257 := by
    simpa [pointCorrectionYInf] using (List.length_erase_le (a:=t) (l:=pointCorrectionYInf))
  have ha := zeroBitCount_le a 0 (pointCorrectionX.erase t).length
  have hb := zeroBitCount_le b 0 (pointCorrectionYInf.erase t).length
  exact ⟨by dsimp; omega,rfl,rfl,by dsimp; omega,rfl,rfl⟩
theorem pointWordProgram_primitive_bounds (ps : List (List Bool × List Bool)) :
    let v := primitiveResources (.unitary (pointWordProgram ps) .done)
    v.x≤3076*ps.length ∧ v.h=0 ∧ v.cnot=0 ∧ v.toffoli≤3061*ps.length ∧
      v.phase=0 ∧ v.measurements=0 := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have he := pointCorrectionEdge_primitive_bounds
      (pointLogicalWires.getD (firstDifferentBit p.1 p.2) 0)
      (boolWordToNat (wireValues (pointCorrectionX.erase (pointLogicalWires.getD (firstDifferentBit p.1 p.2) 0)) (wordPattern pointLogicalWires p.1)))
      (boolWordToNat (wireValues (pointCorrectionYInf.erase (pointLogicalWires.getD (firstDifferentBit p.1 p.2) 0)) (wordPattern pointLogicalWires p.1)))
    rw [pointWordProgram,primitiveResources_unitary_append]
    simp only [pointWordEdge,pointPatternEdge]
    dsimp only [PrimitiveResources.add,List.length_cons] at *
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

theorem pointCorrectionCircuit_primitive_bounds {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    let n := (pointCorrectionWordEdges hC).length
    let v := primitiveResources (.unitary (pointCorrectionCircuit hC) .done)
    v.x≤3076*n ∧ v.h=0 ∧ v.cnot=0 ∧ v.toffoli≤3061*n ∧ v.phase=0 ∧ v.measurements=0 :=
  pointWordProgram_primitive_bounds _

private theorem totalPoint_primitive_sum (a b : PrimitiveResources) (n : Nat)
    (ha : a.x≤100961378 ∧ a.h≤50639660 ∧ a.cnot≤156187745 ∧ a.toffoli≤79278324 ∧ a.phase=0 ∧ a.measurements≤23217835)
    (hb : b.x≤3076*n ∧ b.h=0 ∧ b.cnot=0 ∧ b.toffoli≤3061*n ∧ b.phase=0 ∧ b.measurements=0) :
    let v := a.add b
    v.x≤100961378+3076*n ∧ v.h≤50639660 ∧ v.cnot≤156187745 ∧
      v.toffoli≤79278324+3061*n ∧ v.phase=0 ∧ v.measurements≤23217835 := by
  dsimp only [PrimitiveResources.add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
attribute [local irreducible] primitiveResources fig14CoordinateProgram pointCorrectionCircuit
/-- The complete point circuit includes every physical exceptional correction edge. -/
theorem totalPointProgram_primitive_bounds {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    let n := (pointCorrectionWordEdges hC).length
    let v := primitiveResources (totalPointProgram hC)
    v.x≤100961378+3076*n ∧ v.h≤50639660 ∧ v.cnot≤156187745 ∧
      v.toffoli≤79278324+3061*n ∧ v.phase=0 ∧ v.measurements≤23217835 := by
  rw [totalPointProgram,primitiveResources_seq]
  exact totalPoint_primitive_sum _ _ _ (fig14CoordinateProgram_primitive_bounds _ _)
    (pointCorrectionCircuit_primitive_bounds hC)
end ShorECDLP.Paper2607_13816
