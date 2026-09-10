import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Rotate
import Mathlib.Data.Finset.Card
import ShorECDLP.Submission.«2607_13816».EEA.BitCircuits
/-! # Source-ordered canonical Work2 rotation stages

The pinned wrapper greedily swaps current source positions into their desired destinations.
The private builder below follows that loop literally. Kernel-checked finite certificates cover
its ten production powers of two; symbolic lemmas transfer their index permutations to arbitrary
basis states and establish the complete frame. Counter preparation and stage composition are
proved separately.
-/
namespace ShorECDLP.Paper2607_13816
open _root_.ShorECDLP.Classical
noncomputable section
private def sourceSwapIndex (left right w : Nat) : Nat :=
  if w=right then left else if w=left then right else w
private def sourcePermutation : List (Nat×Nat) → Nat → Nat
  | [], w => w
  | (left,right)::rest,w => sourceSwapIndex left right (sourcePermutation rest w)
private def sourceSwapCircuit (control : Wire) (swaps : List (Nat×Nat)) : Circuit :=
  swaps.flatMap fun (left,right) => controlledSwap control left right
private theorem sourceSwapState (s : BasisState) (left right : Wire) :
    s[left ↦ s right][right ↦ s left] = fun w => s (sourceSwapIndex left right w) := by
  funext w
  simp only [upd,sourceSwapIndex]
  split <;> rename_i h
  · simp
  · split <;> simp_all
private theorem sourceSwapCircuit_correct (swaps : List (Nat×Nat)) (control : Wire)
    (h : ∀ p∈swaps, control≠p.1 ∧ control≠p.2 ∧ p.1≠p.2) (s : BasisState) :
    run (sourceSwapCircuit control swaps) s =
      if s control then (fun w => s (sourcePermutation swaps w)) else s := by
  induction swaps generalizing s with
  | nil => simp [sourceSwapCircuit,sourcePermutation,Classical.run]
  | cons p ps ih =>
    obtain ⟨left,right⟩ := p
    have hh := h (left,right) (by simp)
    have ht : ∀ p∈ps, control≠p.1 ∧ control≠p.2 ∧ p.1≠p.2 := by
      intro p hp; exact h p (by simp [hp])
    simp only [sourceSwapCircuit,List.flatMap_cons,Classical.run_append]
    rw [run_controlledSwap _ _ _ _ hh.1 hh.2.1 hh.2.2]
    by_cases hc : s control
    · rw [if_pos hc]
      rw [show ps.flatMap (fun (left,right) => controlledSwap control left right)=sourceSwapCircuit control ps from rfl,ih ht]
      have he : s[left ↦ s right][right ↦ s left] control = s control := by
        simp [upd,hh.1,hh.2.1]
      rw [he,if_pos hc,if_pos hc,sourceSwapState]
      rfl
    · rw [if_neg hc,if_neg hc]
      exact ih ht s |>.trans (if_neg hc)
private def sourceRotationSwaps (size offset : Nat) : List (Nat×Nat) :=
  ((List.range size).foldl (fun (current,swaps) pos =>
    let want := (pos+size-offset%size)%size
    let old := current.getD pos 0
    if old=want then (current,swaps) else
      let other := current.idxOf want
      (current.set pos want |>.set other old,(pos,other)::swaps))
    (List.range size,[])).2.reverse
private def sourceListSwap (values : List Nat) (p : Nat×Nat) : List Nat :=
  (values.set p.1 (values.getD p.2 0)).set p.2 (values.getD p.1 0)
private theorem listSwap_map (m left right : Nat) (f : Nat→Nat)
    (hl : left<m) (hr : right<m) :
    sourceListSwap ((List.range m).map f) (left,right) =
      (List.range m).map (fun w => f (sourceSwapIndex left right w)) := by
  apply List.ext_getElem
  · simp [sourceListSwap]
  · intro i hi hj
    simp only [sourceListSwap,List.getElem_set,List.getElem_map,List.getElem_range]
    simp [hl,hr,sourceSwapIndex]
    by_cases hir : i=right
    · simp [hir]
    · by_cases hil : i=left
      · subst i
        simp [hir,Ne.symm hir]
      · simp [hir,hil,Ne.symm hir,Ne.symm hil]
private theorem permutation_computed (swaps : List (Nat×Nat)) (m : Nat)
    (h : ∀ p∈swaps,p.1<m ∧ p.2<m) (f : Nat→Nat) :
    swaps.foldl sourceListSwap ((List.range m).map f) =
      (List.range m).map (fun w => f (sourcePermutation swaps w)) := by
  induction swaps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨left,right⟩ := p
    have hh := h (left,right) (by simp)
    rw [List.foldl_cons,listSwap_map m left right f hh.1 hh.2]
    rw [ih (by intro p hp; exact h p (by simp [hp]))]
    rfl
private theorem sourcePermutation_outside (swaps : List (Nat×Nat)) (w : Nat)
    (h : ∀ p∈swaps,w≠p.1 ∧ w≠p.2) : sourcePermutation swaps w=w := by
  induction swaps with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p (by simp)
    simp only [sourcePermutation]
    rw [ih (by intro p hp; exact h p (by simp [hp]))]
    simp [sourceSwapIndex,hp.1,hp.2]
private theorem sourcePermutation_offset (swaps : List (Nat×Nat)) (base i : Nat) :
    sourcePermutation (swaps.map fun p => (base+p.1,base+p.2)) (base+i) =
      base+sourcePermutation swaps i := by
  induction swaps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,sourcePermutation,ih,sourceSwapIndex,Nat.add_left_cancel_iff]
    split
    · rfl
    · split <;> rfl
private theorem sourcePermutation_map (swaps : List (Nat×Nat)) (m offset : Nat)
    (h : ∀ p∈swaps,p.1<m ∧ p.2<m)
    (hd : swaps.foldl sourceListSwap (List.range m)=(List.range m).rotate offset) :
    (List.range m).map (sourcePermutation swaps)=(List.range m).rotate offset := by
  have hc := permutation_computed swaps m h id
  simp only [List.map_id,id_eq] at hc
  exact hc.symm.trans hd
private theorem sourceRotation_values (swaps : List (Nat×Nat)) (m offset base : Nat)
    (h : ∀ p∈swaps,p.1<m ∧ p.2<m)
    (hd : swaps.foldl sourceListSwap (List.range m)=(List.range m).rotate offset)
    (s : BasisState) :
    wireValues (List.range' base m)
      (fun w => s (sourcePermutation (swaps.map fun p => (base+p.1,base+p.2)) w)) =
      (wireValues (List.range' base m) s).rotate offset := by
  have hm := sourcePermutation_map swaps m offset h hd
  have hmap := congrArg (List.map (fun i => s (base+i))) hm
  simpa only [wireValues,List.range'_eq_map_range,List.map_map,Function.comp_def,
    sourcePermutation_offset,List.map_rotate] using hmap
private theorem sourceSwapCircuit_counts (swaps : List (Nat×Nat)) (control : Wire) :
    eeaToffoliCount (sourceSwapCircuit control swaps)=swaps.length ∧
    eeaCnotCount (sourceSwapCircuit control swaps)=2*swaps.length ∧
    eeaXCount (sourceSwapCircuit control swaps)=0 ∧
    tCount (sourceSwapCircuit control swaps)=7*swaps.length := by
  induction swaps with
  | nil => simp [sourceSwapCircuit,eeaToffoliCount,eeaCnotCount,eeaXCount,tCount]
  | cons p ps ih =>
    obtain ⟨left,right⟩ := p
    simp only [sourceSwapCircuit,List.flatMap_cons,eeaToffoliCount_append,eeaCnotCount_append,
      eeaXCount_append,tCount_append,controlledSwap_toffoliCount,controlledSwap_cnotCount,
      controlledSwap_xCount,controlledSwap_tCount,List.length_cons]
    change 1+eeaToffoliCount (sourceSwapCircuit control ps)=_ ∧
      2+eeaCnotCount (sourceSwapCircuit control ps)=_ ∧
      0+eeaXCount (sourceSwapCircuit control ps)=_ ∧
      7+tCount (sourceSwapCircuit control ps)=_
    rw [ih.1,ih.2.1,ih.2.2.1,ih.2.2.2]
    omega
private theorem sourceRotation_correct (swaps : List (Nat×Nat)) (m offset base : Nat)
    (h : ∀ p∈swaps,p.1<m ∧ p.2<m ∧ p.1≠p.2)
    (hd : swaps.foldl sourceListSwap (List.range m)=(List.range m).rotate offset)
    (control : Wire) (hc : control∉List.range' base m) (s : BasisState) :
    let out := run (sourceSwapCircuit control (swaps.map fun p => (base+p.1,base+p.2))) s
    wireValues (List.range' base m) out =
      (if s control then (wireValues (List.range' base m) s).rotate offset
       else wireValues (List.range' base m) s) ∧
    ∀ w∉List.range' base m,out w=s w := by
  have hmem : ∀ i<m,base+i∈List.range' base m := by
    intro i hi; exact List.mem_range'.mpr ⟨i,hi,by simp⟩
  have hbound : ∀ p∈swaps,p.1<m ∧ p.2<m := by
    intro p hp; exact ⟨(h p hp).1,(h p hp).2.1⟩
  have hv := sourceRotation_values swaps m offset base hbound hd s
  have hroles : ∀ p∈swaps.map (fun p => (base+p.1,base+p.2)),
      control≠p.1 ∧ control≠p.2 ∧ p.1≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hh := h q hq
    refine ⟨?_,?_,?_⟩
    · intro he; exact hc (he ▸ hmem q.1 hh.1)
    · intro he; exact hc (he ▸ hmem q.2 hh.2.1)
    · exact fun he => hh.2.2 (Nat.add_left_cancel he)
  dsimp only
  rw [sourceSwapCircuit_correct _ _ hroles]
  by_cases hs : s control
  · rw [if_pos hs,if_pos hs]
    refine ⟨hv,?_⟩
    intro w hw
    congr 1
    apply sourcePermutation_outside
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hh := h q hq
    constructor
    · intro he; exact hw (he ▸ hmem q.1 hh.1)
    · intro he; exact hw (he ▸ hmem q.2 hh.2.1)
  · simp [hs]
private theorem sourceSwapCircuit_support (swaps : List (Nat×Nat)) (control : Wire) (support : List Wire)
    (hc : control∈support) (h : ∀ p∈swaps,p.1∈support ∧ p.2∈support) :
    PaperCircuitUsesOnly support (sourceSwapCircuit control swaps) := by
  induction swaps with
  | nil => simp [sourceSwapCircuit,PaperCircuitUsesOnly]
  | cons p ps ih =>
    obtain ⟨left,right⟩ := p
    have hh := h (left,right) (by simp)
    apply PaperCircuitUsesOnly.append
    · apply (controlledSwap_usesOnly control left right).mono
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hc
      · exact hh.1
      · exact hh.2
    · exact ih (by intro p hp; exact h p (by simp [hp]))
private theorem source_qubit_bound {support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit) : qubitCount circuit≤support.length := by
  have hsub : (circuitWires circuit).toFinset ⊆ support.toFinset := by
    intro wire hw
    simp only [List.mem_toFinset] at hw ⊢
    obtain ⟨gate,hg,hw⟩ := List.mem_flatMap.mp hw
    exact huses gate hg wire hw
  have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le support)
  rw [qubitCount,←List.toFinset_card_of_nodup (List.nodup_dedup _)]
  have he : (circuitWires circuit).dedup.toFinset=(circuitWires circuit).toFinset := by
    ext wire; simp
  rw [he]
  exact hcard
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

end
end ShorECDLP.Paper2607_13816
