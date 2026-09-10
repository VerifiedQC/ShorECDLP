import ShorECDLP.Submission.«2607_13816».Arithmetic.PointTotal
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Exact cost depends only on which of the two comparison banks contains the target. -/
theorem pointCorrectionEdge_T (t : Wire) (a b : Nat)
    (ht : t ∈ pointLogicalWires) :
    ShorECDLP.tCount (pointCorrectionEdge t a b)=if t ∈ pointCorrectionX then 21371 else 21399 := by
  have hn := List.nodup_append.mp pointLogicalWires_nodup
  have hAl : (pointCorrectionX.erase t).length≤256 := by
    simpa [pointCorrectionX] using (List.length_erase_le (a:=t) (l:=pointCorrectionX))
  have hBl : (pointCorrectionYInf.erase t).length≤257 := by
    simpa [pointCorrectionYInf] using (List.length_erase_le (a:=t) (l:=pointCorrectionYInf))
  have hA : (pointCorrectionX.erase t).length-2≤pointCorrectionScratch.length := by
    simp only [pointCorrectionScratch,List.length_range']; omega
  have hB : (pointCorrectionYInf.erase t).length-2≤pointCorrectionScratch.length := by
    simp only [pointCorrectionScratch,List.length_range']; omega
  rw [pointCorrectionEdge,twoRegisterControlledFlip_tCount _ _ _ _ _ _ _ _ _ hA hB]
  by_cases hx : t ∈ pointCorrectionX
  · have hy : t ∉ pointCorrectionYInf := fun h => hn.2.2 t hx t h rfl
    rw [if_pos hx,List.erase_of_not_mem hy,List.length_erase_of_mem hx]
    simp [pointCorrectionX,pointCorrectionYInf,mcxVChainToffoliCost]
  · have hy : t ∈ pointCorrectionYInf := (List.mem_append.mp ht).resolve_left hx
    rw [if_neg hx,List.erase_of_not_mem hx,List.length_erase_of_mem hy]
    simp [pointCorrectionX,pointCorrectionYInf,mcxVChainToffoliCost]
/-- Count the adjacent edges whose target lies in the X coordinate bank. -/
def pointXEdgeCount (ps : List (List Bool × List Bool)) : Nat :=
  ps.countP (fun p => decide (pointLogicalWires.getD (firstDifferentBit p.1 p.2) 0 ∈ pointCorrectionX))

theorem pointWordEdge_T (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513) :
    ShorECDLP.tCount (pointWordEdge a b)=
      if pointLogicalWires.getD (firstDifferentBit a b) 0 ∈ pointCorrectionX then 21371 else 21399 := by
  have h := adjacent_word_patterns pointLogicalWires a b pointLogicalWires_nodup (by simpa using hl) ha
  have ht : pointLogicalWires.getD (firstDifferentBit a b) 0 ∈ pointLogicalWires := by
    rw [List.getD_eq_getElem _ _ h.1]
    exact List.getElem_mem _
  exact pointCorrectionEdge_T _ _ _ ht

/-- Exact ordered-program T cost, without expanding its gate list. -/
theorem pointWordProgram_T (ps : List (List Bool × List Bool))
    (hv : ∀ p ∈ ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513) :
    ShorECDLP.tCount (pointWordProgram ps)=
      21371*pointXEdgeCount ps+21399*(ps.length-pointXEdgeCount ps) := by
  induction ps with
  | nil => simp [pointWordProgram,pointXEdgeCount,ShorECDLP.tCount]
  | cons p ps ih =>
    have hp := hv p (by simp)
    have ht := ih (fun q hq => hv q (by simp [hq]))
    have hle : pointXEdgeCount ps ≤ ps.length := List.countP_le_length
    rw [pointWordProgram,tCount_append,pointWordEdge_T p.1 p.2 hp.1 hp.2,ht]
    simp only [pointXEdgeCount,List.countP_cons,List.length_cons]
    split <;> simp_all [pointXEdgeCount] <;> omega

theorem pointCorrectionCircuit_T {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    ShorECDLP.tCount (pointCorrectionCircuit hC)=
      21371*pointXEdgeCount (pointCorrectionWordEdges hC)+
      21399*((pointCorrectionWordEdges hC).length-pointXEdgeCount (pointCorrectionWordEdges hC)) :=
  pointWordProgram_T _ (pointCorrectionWordEdges_adjacent hC)
end ShorECDLP.Paper2607_13816
