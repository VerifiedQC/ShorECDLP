import ShorECDLP.Submission.«2607_13816».Challenge.MultiplicationSupport

import ShorECDLP.Submission.«2607_13816».Challenge.EEACoreSupport
import ShorECDLP.Submission.«2607_13816».Challenge.LengthRefresh
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem zeroCellProgram_support (n start : Nat) (base : Bool) (r bit guard target temporary : Wire)
    (support : List Wire) (hr : r ∈ support) (hb : bit ∈ support)
    (hg : guard ∈ support) (ht : target ∈ support) (hm : temporary ∈ support) :
    straightWires (zeroCellProgram n start base r bit guard target temporary).2 ⊆ support := by
  simp only [zeroCellProgram,prependCompiled_support,List.append_subset]
  constructor
  · cases base <;> simp [measuredZeroPrefix,circuitWires,gateWires,hr,hb,hg,ht,hm]
  · exact andEraseProgram_support n start r bit temporary support hr hb hm

attribute [local irreducible] zeroCellProgram

theorem upperForwardLeafProgram_support (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hc : control ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold upperForwardLeafProgram
  rw [compiledIf_support]
  split
  · rw [compiledIf_support]
    split <;> exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (by first | exact hc | exact hd _) (hd _) ht
  · simp [straightWires]

theorem upperReverseLeafProgram_support (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold upperReverseLeafProgram
  rw [compiledIf_support]
  split
  · exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (hd _) (hd _) ht
  · simp [straightWires]

theorem lowerForwardLeafProgram_support (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hc : control ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold lowerForwardLeafProgram
  rw [compiledIf_support]
  split
  · rw [compiledIf_support]
    split <;> exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (by first | exact hc | exact hd _) (hd _) ht
  · simp [straightWires]

theorem lowerReverseLeafProgram_support (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold lowerReverseLeafProgram
  rw [compiledIf_support]
  split
  · exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (hd _) (hd _) ht
  · simp [straightWires]

theorem rangeLeafProgram_support (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (label : Nat) (dynamic : Wire) (start : Nat)
    (support : List Wire) (hr : r ∈ support) (hd : dynamic ∈ support)
    (hl : straightWires (leaf label r start).2 ⊆ support) :
    straightWires (rangeLeafProgram n after r leaf label dynamic start).2 ⊆ support := by
  unfold rangeLeafProgram
  rw [compiledIf_support]
  cases after <;> simp only [Bool.false_eq_true,ite_false,ite_true,prependCompiled_support,appendCompiled_support,
    literalProgram_support,List.append_subset]
  · exact ⟨by simp [circuitWires,gateWires,hr,hd],hl⟩
  · exact ⟨hl,by simp [circuitWires,gateWires,hr,hd]⟩

theorem rangeScanProgram_support (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (start : Nat) (support : List Wire)
    (hl : ∀ label ∈ tree.labels, ∀ cursor,
      straightWires (leaf label r cursor).2 ⊆ support)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (hp : path ⊆ support) :
    straightWires (rangeScanProgram n after order tree control r path leaf start).2 ⊆ support := by
  have hu (a : Bool) := unaryProgram_support n order (rangeLeafProgram n a r leaf)
    tree control path start support
    (fun label hlabel dynamic cursor hd => rangeLeafProgram_support n a r leaf label dynamic cursor support hr hd (hl label hlabel cursor)) hi hc hp
  unfold rangeScanProgram
  rw [compiledIf_support]
  cases after <;> simp only [Bool.false_eq_true,ite_false,ite_true,prependCompiled_support,appendCompiled_support,
    literalProgram_support,List.append_subset]
  · exact ⟨hu false,by simp [circuitWires,gateWires,hc,hr]⟩
  · exact ⟨by simp [circuitWires,gateWires,hc,hr],hu true⟩


theorem upperMapProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2 ⊆ support := by
  unfold upperMapProgram
  rw [appendCompiled_support,List.append_subset]
  constructor
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact upperForwardLeafProgram_support n cursor k K control t bitAt dirtyAt label r support hr ht hc hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact upperReverseLeafProgram_support n cursor k K t bitAt dirtyAt label r support hr ht hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp

theorem lowerMapProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2 ⊆ support := by
  unfold lowerMapProgram
  rw [appendCompiled_support,List.append_subset]
  constructor
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact lowerForwardLeafProgram_support n cursor k K control t bitAt dirtyAt label r support hr ht hc hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact lowerReverseLeafProgram_support n cursor k K t bitAt dirtyAt label r support hr ht hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp


theorem upperWriterProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support)
    (hx : targets ⊆ support) :
    straightWires (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2 ⊆ support := by
  have hseed := circuitWires_subset_of_usesOnly ((controlledXorConstant_usesOnly control targets (truthMinusOneValue targets.length K)).mono
    (by
      intro wire hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hc
      · exact hx hw))
  have hwrites : circuitWires (highestPositionDirtyWrites k K targets dirtyAt) ⊆ support := by
    unfold highestPositionDirtyWrites
    apply circuitWires_subset_of_usesOnly
    apply (dirtyConstantWrites_usesOnly targets dirtyAt _ _).mono
    intro wire hw
    simp only [dirtyConstantWritesSupport,List.mem_append,List.mem_map] at hw
    rcases hw with hw | ⟨i,_,rfl⟩
    · exact hx hw
    · exact hd i
  have hm cursor := upperMapProgram_support n k K tree control r t path bitAt dirtyAt cursor support hi hc hr ht hp hb hd
  unfold upperWriterProgram
  simp only [prependCompiled_support,appendCompiled_support,circuitWires,List.flatMap_append,List.append_subset] at hseed hwrites ⊢
  exact ⟨⟨hseed,hwrites⟩,hm _,hwrites,hm _⟩

theorem lowerWriterProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support)
    (hx : targets ⊆ support) :
    straightWires (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2 ⊆ support := by
  have hseed := circuitWires_subset_of_usesOnly ((controlledXorConstant_usesOnly control targets (rightLengthValue width targets.length k)).mono
    (by
      intro wire hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hc
      · exact hx hw))
  have hwrites : circuitWires (rightLengthDirtyWrites width k K targets dirtyAt) ⊆ support := by
    unfold rightLengthDirtyWrites
    apply circuitWires_subset_of_usesOnly
    apply (dirtyConstantWrites_usesOnly targets dirtyAt _ _).mono
    intro wire hw
    simp only [dirtyConstantWritesSupport,List.mem_append,List.mem_map] at hw
    rcases hw with hw | ⟨i,_,rfl⟩
    · exact hx hw
    · exact hd i
  have hm cursor := lowerMapProgram_support n k K tree control r t path bitAt dirtyAt cursor support hi hc hr ht hp hb hd
  unfold lowerWriterProgram
  simp only [prependCompiled_support,appendCompiled_support,circuitWires,List.flatMap_append,List.append_subset] at hseed hwrites ⊢
  exact ⟨⟨hseed,hwrites⟩,hm _,hwrites,hm _⟩


theorem ltUpdateProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) (start : Nat) (support : List Wire)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hcarry : carry ∈ support) (hp : path ⊆ support)
    (h1 : ∀ i, work1At i ∈ support) (h2 : ∀ i, work2At i ∈ support)
    (hx : lengthT ⊆ support) (hy : lengthRP ⊆ support) (hz : constants ⊆ support) :
    straightWires (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 ⊆ support := by
  have hs : constants ++ lengthRP ++ [carry] ⊆ support := by
    simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
    exact ⟨⟨hz,hy⟩,hcarry⟩
  have ha := (circuitWires_subset_of_usesOnly (constMinus_usesOnly lengthRP constants carry (width+2))).trans hs
  have hb := (circuitWires_subset_of_usesOnly (constMinus_usesOnly lengthRP constants carry (width+2))).trans hs
  unfold ltUpdateProgram
  simp only [surroundCompiled_support,appendCompiled_support,List.append_subset]
  refine ⟨⟨ha,?_,?_⟩,hb⟩
  all_goals apply upperWriterProgram_support <;> assumption

theorem lrpUpdateProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) (start : Nat) (support : List Wire)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hcarry : carry ∈ support) (hp : path ⊆ support)
    (h1 : ∀ i, work1At i ∈ support) (h2 : ∀ i, work2At i ∈ support)
    (hx : lengthT ⊆ support) (hy : lengthRP ⊆ support) (hz : constants ⊆ support) :
    straightWires (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 ⊆ support := by
  have hs : constants ++ lengthT ++ [carry] ⊆ support := by
    simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
    exact ⟨⟨hz,hx⟩,hcarry⟩
  have ha := (circuitWires_subset_of_usesOnly (addConstant_usesOnly lengthT constants carry 3)).trans hs
  have hb := (circuitWires_subset_of_usesOnly (subConstant_usesOnly lengthT constants carry 3)).trans hs
  unfold lrpUpdateProgram
  simp only [surroundCompiled_support,appendCompiled_support,List.append_subset]
  refine ⟨⟨ha,?_,?_⟩,hb⟩
  all_goals apply lowerWriterProgram_support <;> assumption
end ShorECDLP.Paper2607_13816.ChallengeMigration
