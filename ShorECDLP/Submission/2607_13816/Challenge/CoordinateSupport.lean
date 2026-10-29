import ShorECDLP.Submission.«2607_13816».Challenge.InPlaceSupport
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedResources
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
/-- Complete coordinate candidate allocation, including the zero-divisor flag. -/
def coordinateBaseSupport : List Wire := 837 :: windowBaseSupport
private theorem old_in_complete : windowBaseSupport ⊆ coordinateBaseSupport :=
  List.subset_cons_of_subset 837 (List.Subset.refl _)
private theorem zero_layout_in_complete : zeroAllowedLayout ⊆ coordinateBaseSupport := by
  intro w hw
  simp only [zeroAllowedLayout,List.mem_append,List.mem_range,List.mem_singleton] at hw
  simp only [coordinateBaseSupport,windowBaseSupport,List.mem_cons,List.mem_append,List.mem_range,List.mem_nil_iff,or_false,List.mem_range'_1]
  dsimp only [Wire] at *
  omega
private theorem zero_wrapper_literals :
    circuitWires fig15ZeroPrepare ⊆ coordinateBaseSupport ∧
    circuitWires fig15ZeroRestore ⊆ coordinateBaseSupport := by
  constructor
  · intro w hw
    apply zero_layout_in_complete
    apply secp256k1ZeroAllowedDivision_wires_subset
    simp only [secp256k1ZeroAllowedDivision,modularWires_seq,AdaptiveCircuit.wires,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl (Or.inl hw)
  · intro w hw
    apply zero_layout_in_complete
    apply secp256k1ZeroAllowedDivision_wires_subset
    simp only [secp256k1ZeroAllowedDivision,modularWires_seq,AdaptiveCircuit.wires,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr hw

theorem zeroDivisionProgram_support_static (n start : Nat) :
    straightWires (zeroDivisionProgram n start).2 ⊆ coordinateBaseSupport := by
  simp only [zeroDivisionProgram,surroundCompiled_support,List.append_subset]
  exact ⟨⟨zero_wrapper_literals.1,(divisionProgram_support_static n start).trans old_in_complete⟩,zero_wrapper_literals.2⟩

theorem zeroMultiplicationProgram_support_static (n start : Nat) :
    straightWires (zeroMultiplicationProgram n start).2 ⊆ coordinateBaseSupport := by
  simp only [zeroMultiplicationProgram,surroundCompiled_support,List.append_subset]
  exact ⟨⟨zero_wrapper_literals.1,(multiplicationProgram_support_static n start).trans old_in_complete⟩,zero_wrapper_literals.2⟩

attribute [local irreducible] fieldLookupAddProgram signedFieldProgram zeroDivisionProgram
  pointSquareProgram zeroMultiplicationProgram xNegateProgram

theorem coordinateProgram_support_static (start : Nat) :
    straightWires (coordinateProgram start).2 ⊆ coordinateBaseSupport := by
  have ha : List.range' 263 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    omega
  have hf field cursor := (fieldLookupAddProgram_support_static field _ ha (by simp) cursor).trans old_in_complete
  have hs field cursor := (signedFieldProgram_support_static field cursor).trans old_in_complete
  unfold coordinateProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [coordinateSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hf _ _
  · exact hs _ _
  · exact zeroDivisionProgram_support_static _ _
  · exact (pointSquareProgram_support_static _ _).trans old_in_complete
  · exact hf _ _
  · exact zeroMultiplicationProgram_support_static _ _
  · exact (xNegateProgram_support_static _ _).trans old_in_complete
  · exact hf _ _
  · exact hs _ _
theorem zeroDivision_touches837 (n start : Nat) :
    837 ∈ straightWires (zeroDivisionProgram n start).2 := by
  simp only [zeroDivisionProgram,surroundCompiled_support,List.mem_append]
  left; left
  simp only [fig15ZeroPrepare,nonzeroInputPrepare,circuitWires,List.flatMap_append,List.mem_append]
  right
  simp [gateWires]

theorem coordinateProgram_touches837 (start : Nat) :
    837 ∈ straightWires (coordinateProgram start).2 := by
  simp only [coordinateProgram,coordinateSegments,sequenceProgram,appendCompiled_support,List.mem_append]
  exact Or.inr (Or.inr (Or.inl (zeroDivision_touches837 _ _)))
end ShorECDLP.Paper2607_13816.ChallengeMigration
