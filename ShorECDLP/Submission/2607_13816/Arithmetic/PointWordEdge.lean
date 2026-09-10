import ShorECDLP.Submission.«2607_13816».Arithmetic.BitTransposition
import ShorECDLP.Submission.«2607_13816».Arithmetic.WordPattern
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointEdge
namespace ShorECDLP.Paper2607_13816
open Classical
def pointLogicalWires : List Wire := pointCorrectionX++pointCorrectionYInf
theorem pointLogicalWires_nodup : pointLogicalWires.Nodup := by decide +kernel
@[simp] theorem pointLogicalWires_length : pointLogicalWires.length=513 := by
  simp [pointLogicalWires,pointCorrectionX,pointCorrectionYInf]
private theorem two_group_matches (A B : List Wire) (t : Wire) (pattern s : BasisState)
    (hA : A.Nodup) (hB : B.Nodup) :
    (registerMatches (A.erase t) (boolWordToNat (wireValues (A.erase t) pattern)) s &&
      registerMatches (B.erase t) (boolWordToNat (wireValues (B.erase t) pattern)) s)=
      decide (∀ w ∈ A++B, w≠t → s w=pattern w) := by
  rw [registerMatches_pattern,registerMatches_pattern]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq,hA.mem_erase_iff,hB.mem_erase_iff,List.mem_append]
  aesop
/-- Constants are extracted after deleting the target wire, preserving the
compressed register order used by the physical equality selectors. -/
def pointPatternEdge (t : Wire) (pattern : BasisState) : Circuit :=
  pointCorrectionEdge t
    (boolWordToNat (wireValues (pointCorrectionX.erase t) pattern))
    (boolWordToNat (wireValues (pointCorrectionYInf.erase t) pattern))
theorem pointPatternEdge_word (t : Wire) (pa pb s : BasisState)
    (ht : t ∈ pointLogicalWires) (hbit : pa t≠pb t)
    (hother : ∀ w ∈ pointLogicalWires, w≠t → pa w=pb w)
    (hc : Clean (558::559::pointCorrectionScratch) s) (hq : s 836=true) :
    wireValues pointLogicalWires (run (pointPatternEdge t pa) s)=
      Equiv.swap (wireValues pointLogicalWires pa) (wireValues pointLogicalWires pb)
        (wireValues pointLogicalWires s) := by
  rw [pointPatternEdge,pointCorrectionEdge_correct t _ _ s ht hc,hq,Bool.true_and]
  have hn := List.nodup_append.mp pointLogicalWires_nodup
  rw [two_group_matches pointCorrectionX pointCorrectionYInf t pa s hn.1 hn.2.1]
  exact maskedBitFlip_word_swap pointLogicalWires t pa pb s ht hbit hother
/-- A physical circuit for an adjacent pair of complete point words. -/
def pointWordEdge (a b : List Bool) : Circuit :=
  pointPatternEdge (pointLogicalWires.getD (firstDifferentBit a b) 0) (wordPattern pointLogicalWires a)
theorem pointWordEdge_correct (a b : List Bool) (ha : WordsAdjacent a b)
    (hl : a.length=513) (s : BasisState)
    (hc : Clean (558::559::pointCorrectionScratch) s) (hq : s 836=true) :
    wireValues pointLogicalWires (run (pointWordEdge a b) s)=
      Equiv.swap a b (wireValues pointLogicalWires s) := by
  have hlen : a.length=pointLogicalWires.length := by simpa using hl
  have h := adjacent_word_patterns pointLogicalWires a b pointLogicalWires_nodup hlen ha
  have ht : pointLogicalWires.getD (firstDifferentBit a b) 0 ∈ pointLogicalWires := by
    rw [List.getD_eq_getElem _ _ h.1]
    exact List.getElem_mem _
  have hb : b.length=pointLogicalWires.length := by
    obtain ⟨pre,tail,x,y,hxy,rfl,rfl⟩ := ha
    simpa using hlen
  have hh := pointPatternEdge_word _ (wordPattern pointLogicalWires a) (wordPattern pointLogicalWires b)
    s ht h.2.1 h.2.2 hc hq
  rw [wordPattern_read _ a pointLogicalWires_nodup hlen,wordPattern_read _ b pointLogicalWires_nodup hb] at hh
  exact hh
private theorem edgeTarget_mem (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513) :
    pointLogicalWires.getD (firstDifferentBit a b) 0 ∈ pointLogicalWires := by
  have h := adjacent_word_patterns pointLogicalWires a b pointLogicalWires_nodup (by simpa using hl) ha
  rw [List.getD_eq_getElem _ _ h.1]
  exact List.getElem_mem _
/-- All external wires, including the control and clean work, are preserved. -/
theorem pointWordEdge_frame (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) :
    ∀ w, w ∉ pointLogicalWires → run (pointWordEdge a b) s w=s w := by
  have ht := edgeTarget_mem a b ha hl
  rw [pointWordEdge,pointPatternEdge,pointCorrectionEdge_correct _ _ _ s ht hc]
  intro w hw
  have hne : w≠pointLogicalWires.getD (firstDifferentBit a b) 0 := by intro h; exact hw (h ▸ ht)
  exact upd_other s _ _ hne
private theorem correctionClean_outside (w : Wire) (hw : w ∈ 558::559::pointCorrectionScratch) :
    w ∉ pointLogicalWires := by
  simp only [pointCorrectionScratch,List.mem_cons,List.mem_range'_1] at hw
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,List.mem_range'_1]
  simp only [Wire] at hw ⊢
  omega
private theorem correctionControl_outside : 836 ∉ pointLogicalWires := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,List.mem_range'_1]
  decide

theorem pointWordEdge_clean (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) :
    Clean (558::559::pointCorrectionScratch) (run (pointWordEdge a b) s) := by
  intro w hw
  rw [pointWordEdge_frame a b ha hl s hc w (correctionClean_outside w hw)]
  exact hc w hw
theorem pointWordEdge_control (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) :
    run (pointWordEdge a b) s 836=s 836 :=
  pointWordEdge_frame a b ha hl s hc 836 correctionControl_outside
theorem pointWordEdge_disabled (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) (hq : s 836=false) :
    run (pointWordEdge a b) s=s := by
  rw [pointWordEdge,pointPatternEdge,pointCorrectionEdge_correct _ _ _ s (edgeTarget_mem a b ha hl) hc,hq]
  simp only [Bool.false_and,Bool.xor_false]
  funext w
  by_cases hw : w=pointLogicalWires.getD (firstDifferentBit a b) 0
  · simp only [upd,hw,ite_self]
  · simp only [upd,if_neg hw]
theorem pointWordEdge_tCount (a b : List Bool) : ShorECDLP.tCount (pointWordEdge a b)≤21553 :=
  pointCorrectionEdge_tCount_le _ _ _
theorem pointWordEdge_usesOnly (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513) :
    PaperCircuitUsesOnly (List.range 839) (pointWordEdge a b) :=
  pointCorrectionEdge_usesOnly _ _ _ (edgeTarget_mem a b ha hl)
theorem pointWordEdge_qubitCount (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513) :
    ShorECDLP.qubitCount (pointWordEdge a b)≤839 :=
  pointCorrectionEdge_qubitCount _ _ _ (edgeTarget_mem a b ha hl)
theorem pointWordEdge_HPFree (a b : List Bool) : HPFree (pointWordEdge a b) :=
  pointCorrectionEdge_HPFree _ _ _
theorem pointWordEdge_wellFormed (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513) :
    CircuitWellFormed (pointWordEdge a b) :=
  pointCorrectionEdge_wellFormed _ _ _ (edgeTarget_mem a b ha hl)
end ShorECDLP.Paper2607_13816
