import ShorECDLP.Submission.«2607_13816».Window.CorrectionControl
import ShorECDLP.Submission.«2607_13816».Window.TableLookup
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem toggle_frame (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) (s : BasisState) (w : Wire)
    (hw : w∉acc::register++flag::scratch) :
    Classical.run (toggleEqConstUnderControl root register value acc flag scratch) s w=s w := by
  have hn : w∉register++flag::scratch := fun h => hw (by simp [h])
  have hwa : w≠acc := fun h => hw (by simp [h])
  have hc (t : BasisState) := (computeEqConst_usesOnly register value flag scratch).preservesOutside t hn
  rw [toggleEqConstUnderControl,Classical.run_append,Classical.run_append,hc]
  simp only [Classical.run_cons,Classical.run_nil,Classical.applyGate,upd,hwa,if_false]
  exact hc s

def correctionWrittenBank : List Wire := pointLogicalWires++558::559::pointCorrectionScratch

private theorem edge_unconditional_frame (t : Wire) (ht : t∈pointLogicalWires) (a b : Nat)
    (s : BasisState) (w : Wire) (hw : w∉correctionWrittenBank) :
    Classical.run (pointCorrectionEdge t a b) s w=s w := by
  have hx : w∉558::pointCorrectionX.erase t++559::pointCorrectionScratch := by
    intro h
    apply hw
    simp only [List.mem_cons,List.mem_append] at h
    rcases h with (rfl | h) | rfl | h
    · simp [correctionWrittenBank]
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_erase h))
    · simp [correctionWrittenBank]
    · simp [correctionWrittenBank,h]
  have hy : w∉t::pointCorrectionYInf.erase t++559::pointCorrectionScratch := by
    intro h
    apply hw
    simp only [List.mem_cons,List.mem_append] at h
    rcases h with (rfl | h) | rfl | h
    · exact List.mem_append_left _ ht
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_of_mem_erase h))
    · simp [correctionWrittenBank]
    · simp [correctionWrittenBank,h]
  rw [pointCorrectionEdge,twoRegisterControlledFlip,Classical.run_append,Classical.run_append,
    toggle_frame _ _ _ _ _ _ _ w hx,toggle_frame _ _ _ _ _ _ _ w hy,toggle_frame _ _ _ _ _ _ _ w hx]

private theorem word_edge_unconditional_frame (a b : List Bool) (ha : WordsAdjacent a b)
    (hl : a.length=513) (s : BasisState) (w : Wire) (hw : w∉correctionWrittenBank) :
    Classical.run (pointWordEdge a b) s w=s w := by
  have h := adjacent_word_patterns pointLogicalWires a b pointLogicalWires_nodup (by simpa using hl) ha
  have ht : pointLogicalWires.getD (firstDifferentBit a b) 0∈pointLogicalWires := by
    rw [List.getD_eq_getElem _ _ h.1]
    exact List.getElem_mem _
  exact edge_unconditional_frame _ ht _ _ s w hw

private theorem word_program_unconditional_frame (ps : List (List Bool×List Bool))
    (hv : ∀ p∈ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513)
    (s : BasisState) (w : Wire) (hw : w∉correctionWrittenBank) :
    Classical.run (pointWordProgram ps) s w=s w := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have hp := hv p (by simp)
    rw [pointWordProgram,Classical.run_append,ih (fun p hp => hv p (by simp [hp]))]
    exact word_edge_unconditional_frame _ _ hp.1 hp.2 s w hw

theorem pointCorrectionCircuit_unconditional_frame {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y)
    (s : BasisState) (w : Wire) (hw : w∉correctionWrittenBank) :
    Classical.run (pointCorrectionCircuit hC) s w=s w :=
  word_program_unconditional_frame _ (pointCorrectionWordEdges_adjacent hC) s w hw


theorem pointCorrectionAt_unconditional_frame {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire)
    (hq : q∉correctionWrittenBank) (s : BasisState) (w : Wire) (hw : w∉correctionWrittenBank) :
    Classical.run (pointCorrectionAt hC q) s w=s w := by
  have hroot : 836∉correctionWrittenBank := by decide +kernel
  have ho : (Equiv.swap 836 q) w∉correctionWrittenBank := by
    by_cases h0 : w=836
    · subst w; simpa using hq
    by_cases h1 : w=q
    · subst w; simpa using hroot
    · simpa [Equiv.swap_apply_def,h0,h1] using hw
  rw [pointCorrectionAt_run]
  simp only [Quantum.relabelBasis,Equiv.symm_swap]
  rw [pointCorrectionCircuit_unconditional_frame hC _ _ ho]
  simp [Quantum.relabelBasis]

def correctionTableBits : List Wire := List.range' 839 16
def correctionTablePath : List Wire := List.range' 519 16

def correctionTableProgram (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) : AdaptiveCircuit :=
  unaryAction .inc (fun a q => pointCorrectionAt (hc a) q)
    (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath

private theorem correction_decoder_outside (w : Wire)
    (hw : w∈836::correctionTableBits++correctionTablePath) : w∉correctionWrittenBank := by
  simp only [correctionTableBits,correctionTablePath,List.mem_cons,List.mem_append,List.mem_range'] at hw
  intro ht
  simp only [correctionWrittenBank,pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
    pointCorrectionScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'] at ht
  rcases hw with (rfl | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩ <;>
    rcases ht with ((⟨j,hj,hwj⟩ | ⟨j,hj,hwj⟩ | ht) | ht | ht | ⟨j,hj,hwj⟩) <;> (try dsimp only [Wire] at *) <;> omega

theorem correctionTableProgram_coherent (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    CoherentlyImplementsOn (correctionTableProgram x y hc)
      (Quantum.run (unaryActionUnitary .inc (fun a q => pointCorrectionAt (hc a) q)
        (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath)) (Clean correctionTablePath) := by
  apply unaryAction_coherent _ _ _ _ _
    (tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel))
  · intro a q hq s w hw
    rw [tableAddressTree_index _ _ _ (by exact List.nodup_range' 1 (by decide))] at hq hw
    exact pointCorrectionAt_unconditional_frame (hc a) q (correction_decoder_outside q hq) s w (correction_decoder_outside w hw)
  · intro a q
    exact pointCorrectionAt_HPFree (hc a) q


theorem correctionTableProgram_wellFormed (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (correctionTableProgram x y hc).WellFormed := by
  apply unaryAction_wellFormed _ _ _ _ _
    (tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel))
  intro a _ q _
  exact pointCorrectionAt_wellFormed (hc a) q

theorem correctionTableProgram_measurements (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (correctionTableProgram x y hc).measurementCount=65535 := by
  have h := unaryAction_measurementCount .inc (fun a q => pointCorrectionAt (hc a) q)
    (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath
    (tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel))
  have hn := tableAddressTree_nodes correctionTableBits 0 1
  have hl : correctionTableBits.length=16 := rfl
  rw [hl] at hn
  change (correctionTableProgram x y hc).measurementCount=_ at h
  omega
private theorem correction_unitary_support (leafAction : Nat → Wire → Circuit) (tree : UnaryActionTree)
    (q : Wire) (ancillas support : List Wire) (hq : q∈support)
    (hi : tree.indexWires ⊆ support) (ha : ancillas ⊆ support)
    (hm : ∀ label q, q∈support → PaperCircuitUsesOnly support (leafAction label q)) :
    PaperCircuitUsesOnly support (unaryActionUnitary .inc
      leafAction tree q ancillas) := by
  induction tree generalizing q ancillas with
  | leaf label => exact hm label q hq
  | node bit zero one hz ho =>
    cases ancillas with
    | nil => simp [unaryActionUnitary,PaperCircuitUsesOnly]
    | cons path rest =>
      have hb := hi (by simp [UnaryActionTree.indexWires] : bit∈(UnaryActionTree.node bit zero one).indexWires)
      have hp := ha (by simp : path∈path::rest)
      have hr : rest ⊆ support := by intro w hw; exact ha (by simp [hw])
      have hz' := hz path rest hp (by intro w hw; exact hi (by simp [UnaryActionTree.indexWires,hw])) hr
      have ho' := ho path rest hp (by intro w hw; exact hi (by simp [UnaryActionTree.indexWires,hw])) hr
      have hc : PaperCircuitUsesOnly support (computeZeroAnd q bit path) := by
        simp [computeZeroAnd,PaperCircuitUsesOnly,PaperGateUsesOnly,gateWires,hq,hb,hp]
      have ht : PaperCircuitUsesOnly support ([.CX q path] : Circuit) := by
        simp [PaperCircuitUsesOnly,PaperGateUsesOnly,gateWires,hq,hp]
      simpa only [unaryActionUnitary,List.nil_append,List.append_assoc] using
        hc.append (hz'.append (ht.append (ho'.append (ht.append hc))))


theorem correctionTableProgram_support (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (correctionTableProgram x y hc).wires ⊆ List.range 855 := by
  have h := correction_unitary_support (fun a q => pointCorrectionAt (hc a) q)
    (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath (List.range 855)
    (by decide +kernel)
    (by intro w hw; rw [tableAddressTree_mem_index] at hw; simp [correctionTableBits] at hw ⊢; omega)
    (by intro w hw; simp [correctionTablePath] at hw ⊢; omega)
    (by intro a q hq g hg w hw; exact pointCorrectionAt_support (hc a) q (List.mem_range.mp hq) (List.mem_flatMap.mpr ⟨g,hg,hw⟩))
  intro w hw
  have hm := unaryAction_wires_subset .inc (fun a q => pointCorrectionAt (hc a) q)
    (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hm
  exact h g hg w hw


theorem correctionTableProgram_tCount (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (correctionTableProgram x y hc).tCount =
      (tableAddressTree correctionTableBits 0 1).leafCostSum
        (fun a q => ShorECDLP.tCount (pointCorrectionAt (hc a) q)) 836 correctionTablePath+458745 := by
  have h := unaryAction_tCount .inc (fun a q => pointCorrectionAt (hc a) q)
    (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath
    (tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel))
  have hn := tableAddressTree_nodes correctionTableBits 0 1
  have hl : correctionTableBits.length=16 := rfl
  rw [hl] at hn
  have he : (tableAddressTree correctionTableBits 0 1).internalNodes=65535 := by omega
  rw [he] at h
  exact h

end
end ShorECDLP.Paper2607_13816
