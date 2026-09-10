import ShorECDLP.Submission.«2607_13816».EEA.SourceRotation

namespace ShorECDLP.Paper2607_13816
open _root_.ShorECDLP.Classical
noncomputable section
private theorem rotation_values_0 :
    (sourceRotationSwaps 259 1).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-1%259) := by decide +kernel
private theorem rotation_bounds_0 :
    ((sourceRotationSwaps 259 1).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_0 :
    (sourceRotationSwaps 259 1).length=258 := by decide +kernel

private theorem rotation_values_1 :
    (sourceRotationSwaps 259 2).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-2%259) := by decide +kernel
private theorem rotation_bounds_1 :
    ((sourceRotationSwaps 259 2).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_1 :
    (sourceRotationSwaps 259 2).length=258 := by decide +kernel

private theorem rotation_values_2 :
    (sourceRotationSwaps 259 4).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-4%259) := by decide +kernel
private theorem rotation_bounds_2 :
    ((sourceRotationSwaps 259 4).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_2 :
    (sourceRotationSwaps 259 4).length=258 := by decide +kernel

private theorem rotation_values_3 :
    (sourceRotationSwaps 259 8).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-8%259) := by decide +kernel
private theorem rotation_bounds_3 :
    ((sourceRotationSwaps 259 8).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_3 :
    (sourceRotationSwaps 259 8).length=258 := by decide +kernel

private theorem rotation_values_4 :
    (sourceRotationSwaps 259 16).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-16%259) := by decide +kernel
private theorem rotation_bounds_4 :
    ((sourceRotationSwaps 259 16).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_4 :
    (sourceRotationSwaps 259 16).length=258 := by decide +kernel

private theorem rotation_values_5 :
    (sourceRotationSwaps 259 32).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-32%259) := by decide +kernel
private theorem rotation_bounds_5 :
    ((sourceRotationSwaps 259 32).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_5 :
    (sourceRotationSwaps 259 32).length=258 := by decide +kernel

private theorem rotation_values_6 :
    (sourceRotationSwaps 259 64).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-64%259) := by decide +kernel
private theorem rotation_bounds_6 :
    ((sourceRotationSwaps 259 64).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_6 :
    (sourceRotationSwaps 259 64).length=258 := by decide +kernel

private theorem rotation_values_7 :
    (sourceRotationSwaps 259 128).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-128%259) := by decide +kernel
private theorem rotation_bounds_7 :
    ((sourceRotationSwaps 259 128).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_7 :
    (sourceRotationSwaps 259 128).length=258 := by decide +kernel

private theorem rotation_values_8 :
    (sourceRotationSwaps 259 256).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-256%259) := by decide +kernel
private theorem rotation_bounds_8 :
    ((sourceRotationSwaps 259 256).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_8 :
    (sourceRotationSwaps 259 256).length=258 := by decide +kernel

private theorem rotation_values_9 :
    (sourceRotationSwaps 259 512).foldl sourceListSwap (List.range 259) =
      (List.range 259).rotate (259-512%259) := by decide +kernel
private theorem rotation_bounds_9 :
    ((sourceRotationSwaps 259 512).all fun p => decide (p.1<259 ∧ p.2<259 ∧ p.1≠p.2))=true := by decide +kernel
private theorem rotation_length_9 :
    (sourceRotationSwaps 259 512).length=258 := by decide +kernel

private theorem rotation_data (bit : Fin 10) :
    let swaps := sourceRotationSwaps 259 (2^bit.val)
    swaps.foldl sourceListSwap (List.range 259) = (List.range 259).rotate (259-2^bit.val%259) ∧
    (∀ p∈swaps,p.1<259 ∧ p.2<259 ∧ p.1≠p.2) ∧ swaps.length=258 := by
  fin_cases bit
  · exact ⟨rotation_values_0,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_0,rotation_length_0⟩
  · exact ⟨rotation_values_1,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_1,rotation_length_1⟩
  · exact ⟨rotation_values_2,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_2,rotation_length_2⟩
  · exact ⟨rotation_values_3,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_3,rotation_length_3⟩
  · exact ⟨rotation_values_4,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_4,rotation_length_4⟩
  · exact ⟨rotation_values_5,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_5,rotation_length_5⟩
  · exact ⟨rotation_values_6,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_6,rotation_length_6⟩
  · exact ⟨rotation_values_7,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_7,rotation_length_7⟩
  · exact ⟨rotation_values_8,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_8,rotation_length_8⟩
  · exact ⟨rotation_values_9,by simpa only [List.all_eq_true,decide_eq_true_eq] using rotation_bounds_9,rotation_length_9⟩

/-- One source-ordered controlled right rotation of the production Work2 bank by `2^bit`.
These are the ten permutation stages in `_canonical_rotate_work2` of the pinned wrapper. -/
def canonicalWork2RotationBit (control : Wire) (bit : Fin 10) : Circuit :=
  sourceSwapCircuit control ((sourceRotationSwaps 259 (2^bit.val)).map fun p => (263+p.1,263+p.2))

/-- Each source permutation has the stated rotation direction and preserves every wire outside Work2. -/
theorem canonicalWork2RotationBit_correct (control : Wire) (bit : Fin 10)
    (hc : control∉List.range' 263 259) (s : BasisState) :
    let out := run (canonicalWork2RotationBit control bit) s
    wireValues (List.range' 263 259) out =
      (if s control then (wireValues (List.range' 263 259) s).rotate (259-2^bit.val%259)
       else wireValues (List.range' 263 259) s) ∧
    ∀ w∉List.range' 263 259,out w=s w := by
  have hd := rotation_data bit
  exact sourceRotation_correct _ 259 _ 263 hd.2.1 hd.1 control hc s

/-- Counts and physical support refer to the same literal controlled permutation. -/
theorem canonicalWork2RotationBit_resources (control : Wire) (bit : Fin 10) :
    eeaToffoliCount (canonicalWork2RotationBit control bit)=258 ∧
    eeaCnotCount (canonicalWork2RotationBit control bit)=516 ∧
    eeaXCount (canonicalWork2RotationBit control bit)=0 ∧
    tCount (canonicalWork2RotationBit control bit)=1806 ∧
    PaperCircuitUsesOnly (control::List.range' 263 259) (canonicalWork2RotationBit control bit) ∧
    qubitCount (canonicalWork2RotationBit control bit)≤260 := by
  have hd := rotation_data bit
  have hcount := sourceSwapCircuit_counts
    ((sourceRotationSwaps 259 (2^bit.val)).map fun p => (263+p.1,263+p.2)) control
  simp only [List.length_map,hd.2.2] at hcount
  have hu : PaperCircuitUsesOnly (control::List.range' 263 259)
      (canonicalWork2RotationBit control bit) := by
    apply sourceSwapCircuit_support _ control _ (by simp)
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hh := hd.2.1 q hq
    constructor
    · exact List.mem_cons_of_mem _ (List.mem_range'.mpr ⟨q.1,hh.1,by simp⟩)
    · exact List.mem_cons_of_mem _ (List.mem_range'.mpr ⟨q.2,hh.2.1,by simp⟩)
  exact ⟨hcount.1,hcount.2.1,hcount.2.2.1,hcount.2.2.2,hu,by
    simpa only [List.length_cons,List.length_range'] using source_qubit_bound hu⟩

/-- The source rotation stage contains only classical reversible gates. -/
theorem canonicalWork2RotationBit_HPFree (control : Wire) (bit : Fin 10) :
    HPFree (canonicalWork2RotationBit control bit) := by
  have hs (swaps : List (Nat×Nat)) : HPFree (sourceSwapCircuit control swaps) := by
    induction swaps with
    | nil => simp [sourceSwapCircuit]
    | cons p ps ih =>
        simp only [sourceSwapCircuit,List.flatMap_cons,hpFree_append]
        exact ⟨controlledSwap_HPFree _ _ _,ih⟩
  exact hs _
/-- All controls and swapped data wires are physically distinct in the source stage. -/
theorem canonicalWork2RotationBit_wellFormed (control : Wire) (bit : Fin 10)
    (hc : control∉List.range' 263 259) :
    CircuitWellFormed (canonicalWork2RotationBit control bit) := by
  have hs (swaps : List (Nat×Nat))
      (hh : ∀ p∈swaps, control≠p.1 ∧ control≠p.2 ∧ p.1≠p.2) :
      CircuitWellFormed (sourceSwapCircuit control swaps) := by
    induction swaps with
    | nil => simp [sourceSwapCircuit,CircuitWellFormed]
    | cons p ps ih =>
      have hp := hh p (by simp)
      have ht := ih (fun q hq => hh q (by simp [hq]))
      simp only [sourceSwapCircuit,List.flatMap_cons,circuitWellFormed_append]
      exact ⟨controlledSwap_wellFormed _ _ _ hp.1 hp.2.1 hp.2.2,ht⟩
  apply hs
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hq' := (rotation_data bit).2.1 q hq
  have hleft : 263+q.1∈List.range' 263 259 := List.mem_range'.mpr ⟨q.1,hq'.1,by omega⟩
  have hright : 263+q.2∈List.range' 263 259 := List.mem_range'.mpr ⟨q.2,hq'.2.1,by omega⟩
  exact ⟨fun he => hc (he.symm ▸ hleft),fun he => hc (he.symm ▸ hright),by omega⟩

end
end ShorECDLP.Paper2607_13816
