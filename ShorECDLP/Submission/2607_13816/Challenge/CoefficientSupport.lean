import ShorECDLP.Submission.«2607_13816».Challenge.EEACoreSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem coefficientFirstProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) (support : List Wire)
    (hc : control ∈ support) (ha : r.accumulator k K ∈ support) (ht : r.targetAt target k label ∈ support)
    (had : r.addendAt target k label ∈ support) (hcarry : r.carry k K ∈ support)
    (hs : r.cellScratch k K ∈ support) :
    straightWires (coefficientFirstProgram n start r k K mode target label control).2 ⊆ support := by
  have hb := rippleFirstProgram_support n start mode _ _ _ _ _ support ha ht had hcarry hs
  simp only [coefficientFirstProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,hc,ha]

theorem coefficientSecondProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) (support : List Wire)
    (hc : control ∈ support) (ha : r.accumulator k K ∈ support) (ht : r.targetAt target k label ∈ support)
    (had : r.addendAt target k label ∈ support) (hcarry : r.carry k K ∈ support)
    (hs : r.cellScratch k K ∈ support) :
    straightWires (coefficientSecondProgram n start r k K mode target label control).2 ⊆ support := by
  have hb := rippleSecondProgram_support n start mode _ _ _ _ _ support ha ht had hcarry hs
  simp only [coefficientSecondProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,hc,ha]

theorem coefficientProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) (support : List Wire)
    (hc : r.control ∈ support) (ha : r.accumulator k K ∈ support)
    (hcarry : r.carry k K ∈ support) (hs : r.cellScratch k K ∈ support)
    (hindex : (coefficientPrefixTree r k K).indexWires ⊆ support)
    (hpath : r.path k K ⊆ support)
    (ht : ∀ l ∈ (coefficientPrefixTree r k K).labels, r.targetAt target k l ∈ support)
    (had : ∀ l ∈ (coefficientPrefixTree r k K).labels, r.addendAt target k l ∈ support)
    (hsgn : circuitWires (coefficientPrefixSignCircuit r k K signUpdate) ⊆ support) :
    straightWires (coefficientProgram n start r k K mode signUpdate target).2 ⊆ support := by
  have hfirst cursor := unaryProgram_support n .inc
    (fun label control cursor => coefficientFirstProgram n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) cursor support
    (fun l hl q cursor hq => coefficientFirstProgram_support n cursor r k K mode target l q support hq ha (ht l hl) (had l hl) hcarry hs)
    hindex hc hpath
  have hsecond cursor := unaryProgram_support n .dec
    (fun label control cursor => coefficientSecondProgram n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) cursor support
    (fun l hl q cursor hq => coefficientSecondProgram_support n cursor r k K mode target l q support hq ha (ht l hl) (had l hl) hcarry hs)
    hindex hc hpath
  have hx : circuitWires [.CX r.control (r.accumulator k K)] ⊆ support := by simp [circuitWires,gateWires,hc,ha]
  simp only [coefficientProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hfirst _,hsgn,hsecond _,hx⟩

private theorem getD_support {xs support : List Wire} (i : Nat) (fallback : Wire)
    (hxs : xs ⊆ support) (hf : fallback ∈ support) : xs.getD i fallback ∈ support := by
  by_cases h : i < xs.length
  · rw [List.getD_eq_getElem xs fallback h]
    exact hxs (List.getElem_mem h)
  · rw [List.getD_eq_default xs fallback (by omega)]
    exact hf

theorem coefficientProgram_support_layout (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : CoefficientPrefixLayout r k K) :
    straightWires (coefficientProgram n start r k K mode signUpdate target).2 ⊆ r.allWires := by
  have hscratch : r.scratch ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hsget (i : Nat) (hi : i < r.scratch.length) : r.scratch.getD i 0 ∈ r.allWires := by
    rw [List.getD_eq_getElem r.scratch 0 hi]
    exact hscratch (List.getElem_mem hi)
  have hcarry : r.carry k K ∈ r.allWires := hsget _ (by rw [hl.scratch_length]; omega)
  have hw1 : r.work1 ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hw2 : r.work2 ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hfirst1 : r.work1.getD 0 0 ∈ r.allWires := by
    have hp : 0 < r.work1.length := by rw [hl.work1_length]; omega
    rw [List.getD_eq_getElem r.work1 0 hp]
    exact hw1 (List.getElem_mem hp)
  have hfirst2 : r.work2.getD 0 0 ∈ r.allWires := by
    have hp : 0 < r.work2.length := by rw [hl.work2_length]; omega
    rw [List.getD_eq_getElem r.work2 0 hp]
    exact hw2 (List.getElem_mem hp)
  have hwork1 l : r.work1At k l ∈ r.allWires := getD_support _ _ hw1 hfirst1
  have hwork2 l : r.work2At k l ∈ r.allWires := getD_support _ _ hw2 hfirst2
  apply coefficientProgram_support
  · simp [CoefficientPrefixRegisters.allWires]
  · exact hsget _ (by rw [hl.scratch_length]; omega)
  · exact hcarry
  · exact hsget _ (by rw [hl.scratch_length]; omega)
  · intro w hw
    have hmem := quotientSwapTree_indexWires_mem_lengthQ (r.routing k K) hl.k_le_K
      (by simpa [CoefficientPrefixRegisters.routing] using hl.index_width) w hw
    have hb : w ∈ r.boundary := hmem
    simp [CoefficientPrefixRegisters.allWires,hb]
  · intro w hw
    exact hscratch (List.mem_of_mem_take hw)
  · intro l _
    cases target
    · exact hwork1 l
    · exact hwork2 l
  · intro l _
    cases target
    · exact hwork2 l
    · exact hwork1 l
  · have hsign : r.sign ∈ r.allWires := by simp [CoefficientPrefixRegisters.allWires]
    cases signUpdate <;> simp [coefficientPrefixSignCircuit,circuitWires,gateWires,hcarry,hsign]

theorem coefficientInverseProgram_support_layout (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : CoefficientPrefixLayout r k K) :
    straightWires (coefficientInverseProgram n start r k K mode signUpdate target).2 ⊆ r.allWires := by
  exact coefficientProgram_support_layout n start r k K mode.inverse signUpdate target hl
end ShorECDLP.Paper2607_13816.ChallengeMigration
