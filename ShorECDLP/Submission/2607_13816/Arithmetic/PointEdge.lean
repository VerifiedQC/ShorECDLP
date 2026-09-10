import ShorECDLP.Submission.«2607_13816».Arithmetic.TwoRegisterFlip
namespace ShorECDLP.Paper2607_13816
open Classical
def pointCorrectionX : List Wire := List.range' 263 256
def pointCorrectionYInf : List Wire := List.range' 580 256 ++ [838]
def pointCorrectionScratch : List Wire := List.range' 7 255
private theorem correctionX_nodup : pointCorrectionX.Nodup := List.nodup_range' 1 (by decide)
private theorem correctionYInf_nodup : pointCorrectionYInf.Nodup := by
  have hn := (List.nodup_range' (s:=580) (n:=256) 1 (by decide))
  simp only [pointCorrectionYInf,List.nodup_append,hn,List.nodup_cons,List.not_mem_nil,List.nodup_nil,true_and]
  simp only [List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  refine ⟨⟨by simp, trivial⟩,?_⟩
  intro a ha b hb
  simp only [Wire] at ha hb ⊢
  omega
private theorem edge_layout (t : Wire) (ht : t ∈ pointCorrectionX++pointCorrectionYInf) :
    EqControlLayout 836 (pointCorrectionX.erase t) 558 559 pointCorrectionScratch ∧
    EqControlLayout 558 (pointCorrectionYInf.erase t) t 559 pointCorrectionScratch := by
  have htval : (263≤t ∧ t<519) ∨ (580≤t ∧ t<836) ∨ t=838 := by
    simp only [pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at ht
    omega
  have hAX : (pointCorrectionX.erase t).Nodup := List.Nodup.erase t correctionX_nodup
  have hBY : (pointCorrectionYInf.erase t).Nodup := List.Nodup.erase t correctionYInf_nodup
  have hAl : (pointCorrectionX.erase t).length≤256 := by
    simpa [pointCorrectionX] using (List.length_erase_le (a:=t) (l:=pointCorrectionX))
  have hBl : (pointCorrectionYInf.erase t).length≤257 := by
    simpa [pointCorrectionYInf] using (List.length_erase_le (a:=t) (l:=pointCorrectionYInf))
  have hmemA (w : Wire) (hw : w ∈ pointCorrectionX.erase t) : 263≤w ∧ w<519 := by
    have hh := List.mem_of_mem_erase hw
    simp only [pointCorrectionX,List.mem_range'_1] at hh
    omega
  have hmemB (w : Wire) (hw : w ∈ pointCorrectionYInf.erase t) : (580≤w ∧ w<836) ∨ w=838 := by
    have hh := List.mem_of_mem_erase hw
    simp only [pointCorrectionYInf,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hh
    omega
  have htarget : t ∉ pointCorrectionYInf.erase t := correctionYInf_nodup.not_mem_erase
  constructor
  · refine ⟨by simp [pointCorrectionScratch]; omega,?_⟩
    simp only [List.nodup_cons,List.mem_cons,not_or,List.nodup_append,hAX,pointCorrectionScratch,List.mem_range'_1]
    have hn := (List.nodup_range' (s:=7) (n:=255) 1 (by decide))
    grind
  · refine ⟨by simp [pointCorrectionScratch]; omega,?_⟩
    simp only [List.nodup_cons,List.mem_cons,not_or,List.nodup_append,hBY,pointCorrectionScratch,List.mem_range'_1]
    have hn := (List.nodup_range' (s:=7) (n:=255) 1 (by decide))
    grind
/-- Physical single-bit edge selector for the 513-bit point encoding. -/
def pointCorrectionEdge (t : Wire) (a b : Nat) : Circuit :=
  twoRegisterControlledFlip 836 t 558 559 (pointCorrectionX.erase t)
    (pointCorrectionYInf.erase t) a b pointCorrectionScratch

theorem pointCorrectionEdge_correct (t : Wire) (a b : Nat) (s : BasisState)
    (ht : t ∈ pointCorrectionX++pointCorrectionYInf)
    (hc : Clean (558::559::pointCorrectionScratch) s) :
    run (pointCorrectionEdge t a b) s=s[t ↦ Bool.xor (s t)
      ((s 836 && registerMatches (pointCorrectionX.erase t) a s) &&
        registerMatches (pointCorrectionYInf.erase t) b s)] := by
  have h := edge_layout t ht
  have htq : t≠836 := by
    simp only [pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,List.mem_range'_1] at ht
    simp only [Wire] at ht ⊢
    omega
  exact run_twoRegisterControlledFlip 836 t 558 559 _ _ a b _ s h.1 h.2
    correctionX_nodup.not_mem_erase htq hc

theorem pointCorrectionEdge_HPFree (t : Wire) (a b : Nat) : HPFree (pointCorrectionEdge t a b) :=
  twoRegisterControlledFlip_HPFree _ _ _ _ _ _ _ _ _
theorem pointCorrectionEdge_wellFormed (t : Wire) (a b : Nat)
    (ht : t ∈ pointCorrectionX++pointCorrectionYInf) : CircuitWellFormed (pointCorrectionEdge t a b) :=
  twoRegisterControlledFlip_wellFormed _ _ _ _ _ _ _ _ _ (edge_layout t ht).1 (edge_layout t ht).2
private theorem mcxCost_le (n bound : Nat) (hn : n≤bound) : mcxVChainToffoliCost n≤2*bound := by
  match n with
  | 0 => simp [mcxVChainToffoliCost]
  | 1 => simp [mcxVChainToffoliCost]
  | n+2 => simp only [mcxVChainToffoliCost]; omega
/-- Uniform gate budget for every edge, including the infinity-bit edge. -/
theorem pointCorrectionEdge_tCount_le (t : Wire) (a b : Nat) :
    ShorECDLP.tCount (pointCorrectionEdge t a b)≤21553 := by
  have hAl : (pointCorrectionX.erase t).length≤256 := by
    simpa [pointCorrectionX] using (List.length_erase_le (a:=t) (l:=pointCorrectionX))
  have hBl : (pointCorrectionYInf.erase t).length≤257 := by
    simpa [pointCorrectionYInf] using (List.length_erase_le (a:=t) (l:=pointCorrectionYInf))
  have hA : (pointCorrectionX.erase t).length-2≤pointCorrectionScratch.length := by
    simp only [pointCorrectionScratch,List.length_range']; omega
  have hB : (pointCorrectionYInf.erase t).length-2≤pointCorrectionScratch.length := by
    simp only [pointCorrectionScratch,List.length_range']; omega
  rw [pointCorrectionEdge,twoRegisterControlledFlip_tCount _ _ _ _ _ _ _ _ _ hA hB]
  have ha := mcxCost_le _ 256 hAl
  have hb := mcxCost_le _ 257 hBl
  omega
/-- Every wire touched by this edge is below 839. -/
theorem pointCorrectionEdge_usesOnly (t : Wire) (a b : Nat)
    (ht : t ∈ pointCorrectionX++pointCorrectionYInf) :
    PaperCircuitUsesOnly (List.range 839) (pointCorrectionEdge t a b) := by
  apply (twoRegisterControlledFlip_usesOnly 836 t 558 559 _ _ a b pointCorrectionScratch).mono
  intro w hw
  have htbound : t<839 := by
    simp only [pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,List.mem_range'_1] at ht
    simp only [Wire] at ht ⊢
    omega
  simp only [List.mem_cons,List.mem_append,or_assoc] at hw
  rcases hw with h | h | h | h | h | h | h
  · subst w; exact List.mem_range.mpr (by decide)
  · subst w; exact List.mem_range.mpr htbound
  · subst w; exact List.mem_range.mpr (by decide)
  · subst w; exact List.mem_range.mpr (by decide)
  · have hh := List.mem_of_mem_erase h
    simp only [pointCorrectionX,List.mem_range'_1] at hh
    apply List.mem_range.mpr
    simp only [Wire] at *
    omega
  · have hh := List.mem_of_mem_erase h
    simp only [pointCorrectionYInf,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hh
    apply List.mem_range.mpr
    simp only [Wire] at *
    omega
  · simp only [pointCorrectionScratch,List.mem_range'_1] at h
    apply List.mem_range.mpr
    simp only [Wire] at *
    omega
theorem pointCorrectionEdge_qubitCount (t : Wire) (a b : Nat)
    (ht : t ∈ pointCorrectionX++pointCorrectionYInf) : ShorECDLP.qubitCount (pointCorrectionEdge t a b)≤839 := by
  have hs : (circuitWires (pointCorrectionEdge t a b)).dedup.toFinset ⊆ (List.range 839).toFinset := by
    intro w hw
    have hh : w ∈ circuitWires (pointCorrectionEdge t a b) := by simpa using hw
    obtain ⟨gate,hgate,hwgate⟩ := List.mem_flatMap.mp hh
    exact List.mem_toFinset.mpr (pointCorrectionEdge_usesOnly t a b ht gate hgate w hwgate)
  have hh := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range)] at hh
  simpa only [ShorECDLP.qubitCount,List.length_range] using hh
/-- Exact ket action; linearity extends this equality to superpositions of clean inputs. -/
theorem pointCorrectionEdge_ket (t : Wire) (a b : Nat) (s : BasisState)
    (ht : t ∈ pointCorrectionX++pointCorrectionYInf)
    (hc : Clean (558::559::pointCorrectionScratch) s) :
    Quantum.run (pointCorrectionEdge t a b) (Quantum.ket s)=Quantum.ket
      (s[t ↦ Bool.xor (s t) ((s 836 && registerMatches (pointCorrectionX.erase t) a s) &&
        registerMatches (pointCorrectionYInf.erase t) b s)]) := by
  rw [Quantum.run_ket_agrees_classical _ s (pointCorrectionEdge_HPFree t a b),
    pointCorrectionEdge_correct t a b s ht hc]
end ShorECDLP.Paper2607_13816
