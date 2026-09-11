import ShorECDLP.Submission.«2607_13816».Window.CorrectionTable
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem edge_support (t : Wire) (ht : t∈pointLogicalWires) (a b : Nat) :
    PaperCircuitUsesOnly (836::correctionWrittenBank) (pointCorrectionEdge t a b) := by
  apply (twoRegisterControlledFlip_usesOnly 836 t 558 559 _ _ a b pointCorrectionScratch).mono
  intro w hw
  simp only [List.mem_cons,List.mem_append,or_assoc] at hw
  rcases hw with h | h | h | h | h | h | h
  · subst w; simp
  · subst w; simp [correctionWrittenBank,ht]
  · subst w; simp [correctionWrittenBank]
  · subst w; simp [correctionWrittenBank]
  · have hh := List.mem_of_mem_erase h
    simp [correctionWrittenBank,pointLogicalWires,hh]
  · have hh := List.mem_of_mem_erase h
    simp [correctionWrittenBank,pointLogicalWires,hh]
  · simp [correctionWrittenBank,h]
private theorem word_support (a b : List Bool) (ha : WordsAdjacent a b) (hl : a.length=513) :
    PaperCircuitUsesOnly (836::correctionWrittenBank) (pointWordEdge a b) := by
  have h := adjacent_word_patterns pointLogicalWires a b pointLogicalWires_nodup (by simpa using hl) ha
  have ht : pointLogicalWires.getD (firstDifferentBit a b) 0∈pointLogicalWires := by
    rw [List.getD_eq_getElem _ _ h.1]
    exact List.getElem_mem _
  exact edge_support _ ht _ _
private theorem program_support (ps : List (List Bool×List Bool))
    (hv : ∀ p∈ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513) :
    PaperCircuitUsesOnly (836::correctionWrittenBank) (pointWordProgram ps) := by
  induction ps with
  | nil => simp [pointWordProgram,PaperCircuitUsesOnly]
  | cons p ps ih =>
    exact (word_support _ _ (hv p (by simp)).1 (hv p (by simp)).2).append
      (ih (fun p hp => hv p (by simp [hp])))
private theorem correction_tight_support {x y : ShorECDLP.Fp}
    (hc : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) :
    PaperCircuitUsesOnly (836::correctionWrittenBank) (pointCorrectionCircuit hc) :=
  program_support _ (pointCorrectionWordEdges_adjacent hc)
private def logicalCorrection {x y : ShorECDLP.Fp}
    (hc : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (active : Bool) (s : BasisState) : BasisState :=
  (Classical.run (pointCorrectionCircuit hc) (s[836↦active]))[836↦s 836]
private theorem correction_runs_logically {x y : ShorECDLP.Fp}
    (hc : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire)
    (hq : q∉correctionWrittenBank) (s : BasisState) :
    Classical.run (pointCorrectionAt hc q) s=logicalCorrection hc (s q) s := by
  funext w
  by_cases hw : w∈correctionWrittenBank
  · have hroot : 836∉correctionWrittenBank := by decide +kernel
    have hw0 : w≠836 := fun h => hroot (h ▸ hw)
    have hwq : w≠q := fun h => hq (h ▸ hw)
    rw [pointCorrectionAt_run]
    simp only [Quantum.relabelBasis,Equiv.symm_swap]
    rw [Equiv.swap_apply_of_ne_of_ne hw0 hwq]
    change Classical.run (pointCorrectionCircuit hc) (Quantum.relabelBasis (Equiv.swap 836 q) s) w = _
    have he := (correction_tight_support hc).run_congrOn
      (Quantum.relabelBasis (Equiv.swap 836 q) s) (s[836↦s q]) (by
        intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · subst v; simp [Quantum.relabelBasis,upd]
        · have hv0 : v≠836 := fun h => hroot (h ▸ hv)
          have hvq : v≠q := fun h => hq (h ▸ hv)
          simp [Quantum.relabelBasis,Equiv.swap_apply_def,upd,hv0,hvq]) w (by simp [hw])
    simpa [logicalCorrection,upd,hw0] using he
  · rw [pointCorrectionAt_unconditional_frame hc q hq s w hw]
    by_cases hw0 : w=836
    · subst w; simp [logicalCorrection,upd]
    · simp only [logicalCorrection,upd,hw0,if_false]
      rw [pointCorrectionCircuit_unconditional_frame hc _ w hw]
      simp [upd,hw0]
private def correctionDecoderBank : List Wire := 836::correctionTableBits++correctionTablePath
private theorem decoder_disjoint : List.Disjoint correctionDecoderBank correctionWrittenBank := by
  intro w hw ht
  have h : ∀ w∈correctionDecoderBank, w∉correctionWrittenBank := by decide +kernel
  exact h w hw ht
private theorem logical_frame {x y : ShorECDLP.Fp}
    (hc : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (active : Bool)
    (s : BasisState) (w : Wire) (hw : w∉correctionWrittenBank) :
    logicalCorrection hc active s w=s w := by
  by_cases h : w=836
  · subst w; simp [logicalCorrection,upd]
  · simp only [logicalCorrection,upd,h,if_false]
    rw [pointCorrectionCircuit_unconditional_frame hc _ w hw]
    simp [upd,h]
private theorem logical_outside {x y : ShorECDLP.Fp}
    (hc : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (active : Bool)
    (left right : BasisState) (he : AgreesOutside correctionDecoderBank left right) :
    AgreesOutside correctionDecoderBank (logicalCorrection hc active left) (logicalCorrection hc active right) := by
  intro w hw
  by_cases hb : w∈correctionWrittenBank
  · have hw0 : w≠836 := fun h => hw (by simp [correctionDecoderBank,h])
    have hrun := (correction_tight_support hc).run_congrOn (left[836↦active]) (right[836↦active]) (by
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v; simp [upd]
      · have hn : v∉correctionDecoderBank := fun h => decoder_disjoint h hv
        have hv0 : v≠836 := fun h => hn (by simp [correctionDecoderBank,h])
        simpa [upd,hv0] using he v hn) w (by simp [hb])
    simpa [logicalCorrection,upd,hw0] using hrun
  · rw [logical_frame hc active left w hb,logical_frame hc active right w hb]
    exact he w hw

private theorem correction_table_logical (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (s : BasisState) (hs : Clean correctionTablePath s) :
    Classical.run (unaryActionUnitary .inc (fun a q => pointCorrectionAt (hc a) q)
      (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath) s =
    (tableAddressTree correctionTableBits 0 1).runLogicalTree .inc
      (fun a active => logicalCorrection (hc a) active) (s 836) s s := by
  apply run_unaryActionUnitary_as_runLogicalTree .inc _
    (fun a q => Classical.run (pointCorrectionAt (hc a) q)) _ _ _ _ correctionDecoderBank s
    (tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel))
  · intro a q s; rfl
  · intro a q hq s
    exact correction_runs_logically (hc a) q (fun h => decoder_disjoint hq h) s
  · intro a q hq s w hw
    exact pointCorrectionAt_unconditional_frame (hc a) q (fun h => decoder_disjoint hq h) s w
      (fun h => decoder_disjoint hw h)
  · intro a active s w hw
    exact logical_frame (hc a) active s w (fun h => decoder_disjoint hw h)
  · intro a active left right he _
    exact logical_outside (hc a) active left right he
  · intro w hw
    rw [tableAddressTree_index _ _ _ (by exact List.nodup_range' 1 (by decide))] at hw
    exact hw
  · exact hs

private theorem logical_clean {x y : ShorECDLP.Fp}
    (hc : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (active : Bool)
    (s : BasisState) (hs : Clean (558::559::pointCorrectionScratch) s) :
    Clean (558::559::pointCorrectionScratch) (logicalCorrection hc active s) := by
  have hn : 836∉558::559::pointCorrectionScratch := by decide +kernel
  have hclean : Clean (558::559::pointCorrectionScratch) (s[836↦active]) := by
    intro w hw
    have h : w≠836 := fun h => hn (h ▸ hw)
    simpa [upd,h] using hs w hw
  intro w hw
  have h : w≠836 := fun h => hn (h ▸ hw)
  simpa [logicalCorrection,upd,h] using pointCorrectionCircuit_clean hc _ hclean w hw
private theorem logical_disabled {x y : ShorECDLP.Fp}
    (hc : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y)
    (s : BasisState) (hs : Clean (558::559::pointCorrectionScratch) s) :
    logicalCorrection hc false s=s := by
  have hn : 836∉558::559::pointCorrectionScratch := by decide +kernel
  have hclean : Clean (558::559::pointCorrectionScratch) (s[836↦false]) := by
    intro w hw
    have h : w≠836 := fun h => hn (h ▸ hw)
    simpa [upd,h] using hs w hw
  unfold logicalCorrection
  rw [pointCorrectionCircuit_disabled hc _ hclean (by simp [upd])]
  funext w
  by_cases h : w=836 <;> simp [upd,h]
private theorem logical_selected (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (tree : UnaryActionTree) (active : Bool) (route s : BasisState)
    (hs : Clean (558::559::pointCorrectionScratch) s) :
    tree.runLogicalTree .inc (fun a active => logicalCorrection (hc a) active) active route s =
      logicalCorrection (hc (tree.routeLabel route)) active s := by
  induction tree generalizing active s with
  | leaf a => rfl
  | node bit zero one ihz iho =>
    cases active <;> cases hb : route bit <;>
      simp only [UnaryActionTree.runLogicalTree,UnaryActionTree.routeLabel,hb,
        Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and]
    · rw [ihz false s hs,logical_disabled _ s hs,iho false s hs,logical_disabled _ s hs,logical_disabled _ s hs]
    · rw [ihz false s hs,logical_disabled _ s hs,iho false s hs,logical_disabled _ s hs,logical_disabled _ s hs]
    · rw [ihz true s hs,iho false _ (logical_clean _ true s hs),logical_disabled _ _ (logical_clean _ true s hs)]
      exact congrArg (fun a => logicalCorrection (hc a) true s) (by simp [hb])
    · rw [ihz false s hs,logical_disabled _ s hs,iho true s hs]
      exact congrArg (fun a => logicalCorrection (hc a) true s) (by simp [hb])
def correctionTableState (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) (s : BasisState) : BasisState :=
  Classical.run (pointCorrectionCircuit (hc ((tableAddressTree correctionTableBits 0 1).routeLabel s))) s

theorem correctionTable_selected (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (s : BasisState) (hp : Clean correctionTablePath s)
    (hs : Clean (558::559::pointCorrectionScratch) s) :
    Classical.run (unaryActionUnitary .inc (fun a q => pointCorrectionAt (hc a) q)
      (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath) s = correctionTableState x y hc s := by
  rw [correction_table_logical x y hc s hp,logical_selected x y hc _ _ s s hs]
  have hu : s[836↦s 836]=s := by funext w; by_cases h : w=836 <;> simp [upd,h]
  simp only [logicalCorrection,hu,correctionTableState]
  funext w
  by_cases h : w=836
  · subst w
    simp only [upd,if_true]
    exact (pointCorrectionCircuit_unconditional_frame _ s 836 (by decide +kernel)).symm
  · simp [upd,h]

theorem correctionTable_coherent_selected (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    CoherentlyImplementsOn (correctionTableProgram x y hc)
      (Finsupp.lmapDomain ℂ ℂ (correctionTableState x y hc))
      (fun s => Clean correctionTablePath s ∧ Clean (558::559::pointCorrectionScratch) s) := by
  have h : CoherentlyImplementsOn (correctionTableProgram x y hc)
      (Quantum.run (unaryActionUnitary .inc (fun a q => pointCorrectionAt (hc a) q)
        (tableAddressTree correctionTableBits 0 1) 836 correctionTablePath))
      (fun s => Clean correctionTablePath s ∧ Clean (558::559::pointCorrectionScratch) s) := by
    obtain ⟨cs,ha,hm⟩ := correctionTableProgram_coherent x y hc
    exact ⟨cs,ha.imp (fun b c hb s hs => hb s hs.1),hm⟩
  apply h.congrIdeal
  intro s hs
  rw [run_ket_agrees_classical _ _ (unaryActionUnitary_HPFree _ _ _ _ _
    (by intro a q; exact pointCorrectionAt_HPFree (hc a) q)),correctionTable_selected x y hc s hs.1 hs.2]
  simp [ket]

theorem correctionTableState_clean (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (s : BasisState) (hs : Clean (558::559::pointCorrectionScratch) s) :
    Clean (558::559::pointCorrectionScratch) (correctionTableState x y hc s) :=
  pointCorrectionCircuit_clean _ s hs

theorem correctionTableState_frame (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (s : BasisState) (hs : Clean (558::559::pointCorrectionScratch) s) :
    ∀ w, w∉pointLogicalWires → correctionTableState x y hc s w=s w :=
  pointCorrectionCircuit_frame _ s hs

theorem correctionTableState_correct (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState)
    (hs : Clean (558::559::pointCorrectionScratch) s) (hq : s 836=true)
    (hw : wireValues pointLogicalWires s=pointCoordinateWord
      (fig14EncodedEquiv (x ((tableAddressTree correctionTableBits 0 1).routeLabel s))
        (y ((tableAddressTree correctionTableBits 0 1).routeLabel s)) (fig14PointEncoding P))) :
    wireValues pointLogicalWires (correctionTableState x y hc s)=
      pointCoordinateWord (fig14PointEncoding (P+.some (hc ((tableAddressTree correctionTableBits 0 1).routeLabel s)))) :=
  pointCorrectionCircuit_correct _ P s hs hq hw

theorem correctionTableState_ready (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (s : BasisState) (hs : Clean correctionTablePath s ∧ Clean (558::559::pointCorrectionScratch) s) :
    Clean correctionTablePath (correctionTableState x y hc s) ∧
      Clean (558::559::pointCorrectionScratch) (correctionTableState x y hc s) := by
  refine ⟨?_,correctionTableState_clean x y hc s hs.2⟩
  intro w hw
  have hn : w∉correctionWrittenBank := fun h => decoder_disjoint (by simp [correctionDecoderBank,hw]) h
  rw [correctionTableState,pointCorrectionCircuit_unconditional_frame _ s w hn]
  exact hs.1 w hw

theorem correctionTableState_address (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) (s : BasisState) :
    correctionTableState x y hc s = Classical.run
      (pointCorrectionCircuit (hc (tableAddressValue correctionTableBits s))) s := by
  simp only [correctionTableState,tableAddressTree_route,zero_add,one_mul]

end
end ShorECDLP.Paper2607_13816
