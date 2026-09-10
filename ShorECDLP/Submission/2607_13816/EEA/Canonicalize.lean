import ShorECDLP.Submission.«2607_13816».EEA.CanonicalRotation
import ShorECDLP.Submission.«2607_13816».EEA.TerminalEntry
namespace ShorECDLP.Paper2607_13816
open _root_.ShorECDLP.Classical
attribute [local irreducible] canonicalWork2RotationBit
noncomputable section
private theorem terminalCounterCanonicalValue (padding : Nat) (hp : padding≤596) :
    (terminalShiftLow padding+512*(!terminalShiftEpoch padding).toNat+1)%1024=padding := by
  by_cases h : 1≤padding ∧ padding≤512
  · simp only [terminalShiftLow,terminalShiftEpoch,decide_eq_true h,Bool.not_true,Bool.toNat_false,
      Nat.mul_zero,Nat.add_zero]
    omega
  · have hn : decide (1≤padding ∧ padding≤512)=false := decide_eq_false h
    simp only [terminalShiftLow,terminalShiftEpoch,hn,Bool.not_false,Bool.toNat_true,Nat.mul_one]
    omega
private def canonicalCounterWires : List Wire := List.range' 540 9 ++ [559]
private def canonicalCounterPrepare : Circuit :=
  [.X 559] ++ addConstant canonicalCounterWires (List.range' 560 10) 570 1
private theorem counter_word_append (a b : List Bool) :
    boolWordToNat (a++b)=boolWordToNat a+2^a.length*boolWordToNat b := by
  induction a with
  | nil => simp
  | cons bit bits ih =>
    simp only [List.cons_append,boolWordToNat_cons,ih,List.length_cons,pow_succ]
    ring
private theorem canonicalCounterPrepare_correct (padding : Nat) (hp : padding≤596)
    (s : BasisState) (ht : Secp256k1TerminalState padding s) :
    let out := run canonicalCounterPrepare s
    boolWordToNat (wireValues canonicalCounterWires out)=padding ∧
    Clean (List.range' 560 10++[570]) out ∧
    ∀ w∉canonicalCounterWires,out w=s w := by
  let flipped := s[559 ↦ !s 559]
  have hsub : ∀ w∈List.range' 560 10++[570], w∈indexedStepProductionRegisters.sharedScratch := by decide
  have hne : ∀ w∈List.range' 560 10++[570], w≠559 := by decide
  have hclean : Clean (List.range' 560 10++[570]) flipped := by
    intro w hw
    rw [show flipped w=s w from upd_other _ _ _ (hne w hw)]
    exact ht.ready w (hsub w hw)
  have ha := addConstant_correct canonicalCounterWires (List.range' 560 10) 570 1 flipped
    (by decide) (by change (570::List.range' 560 10++(List.range' 540 9++[559])).Nodup; decide) hclean
  have hlow : wireValues (List.range' 540 9) flipped=wireValues (List.range' 540 9) s := by
    apply List.map_congr_left
    intro w hw
    exact upd_other _ _ _ ((by decide : ∀ w∈List.range' 540 9,w≠559) w hw)
  have hword : boolWordToNat (wireValues canonicalCounterWires flipped)=
      terminalShiftLow padding+512*(!terminalShiftEpoch padding).toNat := by
    change boolWordToNat (wireValues (List.range' 540 9) flipped++[flipped 559])=_
    rw [counter_word_append,hlow]
    have hl : boolWordToNat (wireValues (List.range' 540 9) s)=terminalShiftLow padding := ht.low
    have he : s 559=terminalShiftEpoch padding := ht.epoch
    rw [hl,show flipped 559= !s 559 from rfl,he]
    simp only [wireValues,List.length_map,List.length_range',boolWordToNat_cons,boolWordToNat_nil,
      Nat.mul_zero,Nat.add_zero]
    rfl
  change _ ∧ _ ∧ _
  rw [show run canonicalCounterPrepare s=run (addConstant canonicalCounterWires (List.range' 560 10) 570 1) flipped from rfl]
  refine ⟨?_,ha.2.1,?_⟩
  · rw [ha.1,boolWordToNat_cuccaroAddBits false _ _ (by
      simp [canonicalCounterWires,wireValues,constantBits_length])]
    simp only [Bool.toNat_false,Nat.zero_add,boolWordToNat_constantBits,constantBits_length,
      List.length_range']
    rw [hword]
    have hn := terminalCounterCanonicalValue padding hp
    change (1+(terminalShiftLow padding+512*(!terminalShiftEpoch padding).toNat))%1024=padding
    simpa only [Nat.add_comm] using hn
  · intro w hw
    rw [ha.2.2 w hw]
    exact upd_other _ _ _ (by intro he; apply hw; simp [canonicalCounterWires,he])
private def counterControl (bit : Fin 10) : Wire := if bit.val<9 then 540+bit.val else 559
private def counterRotationChain (bits : List (Fin 10)) : Circuit :=
  bits.flatMap fun bit => canonicalWork2RotationBit (counterControl bit) bit
private def counterRotationAmount (bits : List (Fin 10)) (s : BasisState) : Nat :=
  (bits.map fun bit => (s (counterControl bit)).toNat*2^bit.val).sum
private theorem counterControl_outside (bit : Fin 10) : counterControl bit∉List.range' 263 259 := by
  have hb := bit.isLt
  dsimp only [counterControl,Wire]
  split <;> intro hm <;> obtain ⟨i,hi,he⟩ := List.mem_range'.mp hm <;> omega
private theorem counterAmount_congr (bits : List (Fin 10)) (s t : BasisState)
    (h : ∀ bit,s (counterControl bit)=t (counterControl bit)) :
    counterRotationAmount bits s=counterRotationAmount bits t := by
  simp only [counterRotationAmount]
  congr 1
  apply List.map_congr_left
  intro bit _
  rw [h bit]
private theorem chainRotation_cancel (bits : List Bool) (hlen : bits.length=259) (amount : Nat) :
    (bits.rotate (259-amount%259)).rotate amount=bits := by
  rw [List.rotate_rotate,←List.rotate_mod,hlen]
  have hm : (259-amount%259+amount)%259=0 := by omega
  rw [hm,List.rotate_zero]
private theorem counterRotationChain_correct (bits : List (Fin 10)) (s : BasisState) :
    let out := run (counterRotationChain bits) s
    (wireValues (List.range' 263 259) out).rotate (counterRotationAmount bits s)=
      wireValues (List.range' 263 259) s ∧
    ∀ w∉List.range' 263 259,out w=s w := by
  induction bits generalizing s with
  | nil => simp [counterRotationChain,counterRotationAmount,run]
  | cons bit bits ih =>
    let first := run (canonicalWork2RotationBit (counterControl bit) bit) s
    have hh := canonicalWork2RotationBit_correct (counterControl bit) bit (counterControl_outside bit) s
    have ht := ih first
    have hamount : counterRotationAmount bits first=counterRotationAmount bits s :=
      counterAmount_congr bits first s (fun b => hh.2 _ (counterControl_outside b))
    dsimp only at hh ht ⊢
    rw [hamount] at ht
    change _ ∧ _
    simp only [counterRotationChain,List.flatMap_cons,run_append]
    refine ⟨?_,?_⟩
    · change (wireValues _ (run (counterRotationChain bits) first)).rotate
        (counterRotationAmount (bit::bits) s)=_
      simp only [counterRotationAmount,List.map_cons,List.sum_cons]
      change (wireValues _ (run (counterRotationChain bits) first)).rotate
        ((s (counterControl bit)).toNat*2^bit.val+counterRotationAmount bits s)=_
      rw [Nat.add_comm,←List.rotate_rotate,ht.1,hh.1]
      cases hb : s (counterControl bit) with
      | false => simp
      | true =>
        simp only [Bool.toNat_true,Nat.one_mul,ite_true]
        apply chainRotation_cancel
        simp [wireValues]
    · intro w hw
      exact (ht.2 w hw).trans (hh.2 w hw)
private theorem counterRotationAmount_full (s : BasisState) :
    counterRotationAmount (List.finRange 10) s =
      boolWordToNat (wireValues (List.range' 540 9++[559]) s) := by
  rw [show List.range' 540 9=[540,541,542,543,544,545,546,547,548] from rfl]
  simp [counterRotationAmount,List.finRange,counterControl,wireValues,boolWordToNat]
  ring

private def canonicalCounterRestore : Circuit :=
  subConstant canonicalCounterWires (List.range' 560 10) 570 1 ++ [.X 559]
private def canonicalRestoreSupport : List Wire :=
  List.range' 560 10 ++ canonicalCounterWires ++ [570]
private theorem canonicalRestore_support :
    PaperCircuitUsesOnly canonicalRestoreSupport canonicalCounterRestore := by
  apply PaperCircuitUsesOnly.append
  · exact subConstant_usesOnly _ _ _ _
  · intro gate hg w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    subst gate
    simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
    subst w
    simp [canonicalRestoreSupport,canonicalCounterWires]
private theorem canonicalSupport_outside :
    ∀ w∈canonicalRestoreSupport,w∉List.range' 263 259 := by
  intro w hw hm
  obtain ⟨i,hi,he⟩ := List.mem_range'.mp hm
  simp only [canonicalRestoreSupport,canonicalCounterWires,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,List.mem_range',Nat.one_mul] at hw
  dsimp only [Wire] at *
  omega
private theorem canonicalRestore_prepare (s : BasisState) :
    run canonicalCounterRestore (run canonicalCounterPrepare s)=s := by
  rw [canonicalCounterRestore,canonicalCounterPrepare,run_append,run_append,
    run_subConstant_after_add _ _ _ _ _ (by decide)
      (by change (570::List.range' 560 10++(List.range' 540 9++[559])).Nodup; decide)]
  funext w
  by_cases hw : w=559
  · subst w; simp [run,applyGate,upd]
  · simp [run,applyGate,upd,hw]
/-- The source counter preparation, ten controlled rotations, and exact counter restoration. -/
def canonicalWork2Rotation : Circuit :=
  canonicalCounterPrepare ++ counterRotationChain (List.finRange 10) ++ canonicalCounterRestore
/-- Canonical rotation restores Work2 and every external wire from the terminal counter encoding. -/
theorem canonicalWork2Rotation_correct (padding : Nat) (hp : padding≤596)
    (s : BasisState) (ht : Secp256k1TerminalState padding s)
    (canonical : List Bool) (hbank : wireValues (List.range' 263 259) s=canonical.rotate padding) :
    let out := run canonicalWork2Rotation s
    wireValues (List.range' 263 259) out=canonical ∧
    ∀ w∉List.range' 263 259,out w=s w := by
  let prepared := run canonicalCounterPrepare s
  let rotated := run (counterRotationChain (List.finRange 10)) prepared
  have hprep := canonicalCounterPrepare_correct padding hp s ht
  have hchain := counterRotationChain_correct (List.finRange 10) prepared
  have hamount : counterRotationAmount (List.finRange 10) prepared=padding :=
    (counterRotationAmount_full prepared).trans hprep.1
  have hcounter : ∀ w∈canonicalCounterWires,w∉List.range' 263 259 := by
    intro w hw
    exact canonicalSupport_outside w (by simp [canonicalRestoreSupport,hw])
  have hprebank : wireValues (List.range' 263 259) prepared=wireValues (List.range' 263 259) s := by
    apply List.map_congr_left
    intro w hw
    exact hprep.2.2 w (by intro h; exact hcounter w h hw)
  have hrotbank : wireValues (List.range' 263 259) rotated=canonical := by
    apply List.rotate_injective padding
    exact (by simpa only [hamount,hprebank,hbank] using hchain.1)
  have hrestore : ∀ w∉List.range' 263 259,
      run canonicalCounterRestore rotated w=run canonicalCounterRestore prepared w := by
    intro w hw
    by_cases hs : w∈canonicalRestoreSupport
    · apply canonicalRestore_support.run_congrOn rotated prepared _ w hs
      intro v hv
      exact hchain.2 v (canonicalSupport_outside v hv)
    · rw [canonicalRestore_support.preservesOutside rotated hs,
        canonicalRestore_support.preservesOutside prepared hs]
      exact hchain.2 w hw
  change _ ∧ _
  rw [show run canonicalWork2Rotation s=run canonicalCounterRestore rotated from by
    rw [canonicalWork2Rotation,run_append,run_append]]
  constructor
  · calc
      wireValues (List.range' 263 259) (run canonicalCounterRestore rotated)=
          wireValues (List.range' 263 259) rotated := by
        apply List.map_congr_left
        intro w hw
        exact canonicalRestore_support.preservesOutside rotated (by
          intro hs; exact canonicalSupport_outside w hs hw)
      _ = canonical := hrotbank
  · intro w hw
    rw [hrestore w hw,canonicalRestore_prepare s]
private theorem counterRotationChain_counts (bits : List (Fin 10)) :
    eeaToffoliCount (counterRotationChain bits)=258*bits.length ∧
    eeaCnotCount (counterRotationChain bits)=516*bits.length ∧
    eeaXCount (counterRotationChain bits)=0 ∧
    tCount (counterRotationChain bits)=1806*bits.length := by
  induction bits with
  | nil => simp [counterRotationChain,eeaToffoliCount,eeaCnotCount,eeaXCount,tCount]
  | cons bit bits ih =>
    have hb := canonicalWork2RotationBit_resources (counterControl bit) bit
    simp only [counterRotationChain,List.flatMap_cons,eeaToffoliCount_append,
      eeaCnotCount_append,eeaXCount_append,tCount_append,List.length_cons]
    change eeaToffoliCount (canonicalWork2RotationBit _ bit)+eeaToffoliCount (counterRotationChain bits)=_ ∧
      eeaCnotCount (canonicalWork2RotationBit _ bit)+eeaCnotCount (counterRotationChain bits)=_ ∧
      eeaXCount (canonicalWork2RotationBit _ bit)+eeaXCount (counterRotationChain bits)=_ ∧
      tCount (canonicalWork2RotationBit _ bit)+tCount (counterRotationChain bits)=_
    rw [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2]
    omega
private def canonicalRotationSupport : List Wire := List.range' 263 259++canonicalRestoreSupport
private theorem counterControl_mem (bit : Fin 10) : counterControl bit∈canonicalCounterWires := by
  fin_cases bit <;> decide
private theorem canonicalRotation_support : PaperCircuitUsesOnly canonicalRotationSupport canonicalWork2Rotation := by
  have hsub : canonicalRestoreSupport⊆canonicalRotationSupport := by
    intro w hw; exact List.mem_append_right _ hw
  have hprep : PaperCircuitUsesOnly canonicalRestoreSupport canonicalCounterPrepare := by
    apply PaperCircuitUsesOnly.append
    · intro gate hg w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
      subst gate
      simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
      subst w
      simp [canonicalRestoreSupport,canonicalCounterWires]
    · exact addConstant_usesOnly _ _ _ _
  have hchain : ∀ bits,PaperCircuitUsesOnly canonicalRotationSupport (counterRotationChain bits) := by
    intro bits
    induction bits with
    | nil => simp [counterRotationChain,PaperCircuitUsesOnly]
    | cons bit bits ih =>
      apply PaperCircuitUsesOnly.append
      · apply (canonicalWork2RotationBit_resources (counterControl bit) bit).2.2.2.2.1.mono
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · apply hsub
          simp only [canonicalRestoreSupport,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
          exact Or.inl (Or.inr (counterControl_mem bit))
        · exact List.mem_append_left _ hw
      · exact ih
  exact ((hprep.mono hsub).append (hchain _)).append (canonicalRestore_support.mono hsub)
private theorem canonical_rotation_qubits : qubitCount canonicalWork2Rotation≤280 := by
  have hsub : (circuitWires canonicalWork2Rotation).toFinset ⊆ canonicalRotationSupport.toFinset := by
    intro w hw
    simp only [List.mem_toFinset] at hw ⊢
    obtain ⟨gate,hg,hw⟩ := List.mem_flatMap.mp hw
    exact canonicalRotation_support gate hg w hw
  have hc := (Finset.card_le_card hsub).trans (List.toFinset_card_le canonicalRotationSupport)
  rw [qubitCount,←List.toFinset_card_of_nodup (List.nodup_dedup _)]
  have he : (circuitWires canonicalWork2Rotation).dedup.toFinset=(circuitWires canonicalWork2Rotation).toFinset := by
    ext w; simp
  rw [he]
  simpa [canonicalRotationSupport,canonicalRestoreSupport,canonicalCounterWires] using hc
/-- Gate counts and physical support bound for the same complete canonicalization circuit. -/
theorem canonicalWork2Rotation_resources :
    eeaToffoliCount canonicalWork2Rotation=2620 ∧ eeaCnotCount canonicalWork2Rotation=5240 ∧
    eeaXCount canonicalWork2Rotation=6 ∧ tCount canonicalWork2Rotation=18340 ∧
    qubitCount canonicalWork2Rotation≤280 := by
  have hp : eeaToffoliCount canonicalCounterPrepare=20 ∧ eeaCnotCount canonicalCounterPrepare=40 ∧
      eeaXCount canonicalCounterPrepare=3 ∧ tCount canonicalCounterPrepare=140 := by decide +kernel
  have hr : eeaToffoliCount canonicalCounterRestore=20 ∧ eeaCnotCount canonicalCounterRestore=40 ∧
      eeaXCount canonicalCounterRestore=3 ∧ tCount canonicalCounterRestore=140 := by decide +kernel
  have hc := counterRotationChain_counts (List.finRange 10)
  simp only [List.length_finRange] at hc
  refine ⟨?_,?_,?_,?_,canonical_rotation_qubits⟩ <;>
    simp only [canonicalWork2Rotation,eeaToffoliCount_append,eeaCnotCount_append,
      eeaXCount_append,tCount_append,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

/-- The production EEA schedule followed by the source wrapper restores the terminal coefficient's canonical bit order. -/
theorem secp256k1EEAForward_canonical_coefficient (s : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p) :
    let initial := paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))
    let final := paperRun initial
    let out := run (secp256k1EEAForwardUnitary indexedStepProductionRegisters ++ canonicalWork2Rotation)
      (eeaPreprocessIdealState s)
    wireValues indexedStepProductionRegisters.work1 out = constantBits final.lT final.t ++ [false] ++
      (constantBits final.lQ final.q).reverse ++ (constantBits (259-(final.lT+final.lQ+1)) final.r).reverse ∧
    wireValues indexedStepProductionRegisters.work2 out = constantBits 259 final.tPrime ∧
    out indexedStepProductionRegisters.iter=final.iter ∧
    boolWordToNat (wireValues indexedStepProductionRegisters.lengthT out)=truthMinusOneValue 9 final.lT := by
  let initial := paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))
  let middle := run (secp256k1EEAForwardUnitary indexedStepProductionRegisters) (eeaPreprocessIdealState s)
  have hd := secp256k1EEAForward_payload s hclean hx hxp
  have ht := secp256k1EEAForward_terminalState s hclean hx hxp
  have hc := canonicalWork2Rotation_correct (paperPadding initial)
    (secp256k1_paperPadding_le_596 hx hxp) middle ht (constantBits 259 (paperRun initial).tPrime) hd.2.1
  have hwork : wireValues indexedStepProductionRegisters.work1 (run canonicalWork2Rotation middle)=
      wireValues indexedStepProductionRegisters.work1 middle := by
    apply List.map_congr_left
    intro w hw
    apply hc.2 w
    change w∈List.range' 4 259 at hw
    intro hm
    obtain ⟨i,hi,he⟩ := List.mem_range'.mp hw
    obtain ⟨j,hj,hf⟩ := List.mem_range'.mp hm
    dsimp only [Wire] at *
    omega
  have hlength : wireValues indexedStepProductionRegisters.lengthT (run canonicalWork2Rotation middle)=
      wireValues indexedStepProductionRegisters.lengthT middle := by
    apply List.map_congr_left
    intro w hw
    apply hc.2 w
    change w∈List.range' 522 9 at hw
    intro hm
    obtain ⟨i,hi,he⟩ := List.mem_range'.mp hw
    obtain ⟨j,hj,hf⟩ := List.mem_range'.mp hm
    dsimp only [Wire] at *
    omega
  dsimp only
  rw [run_append]
  exact ⟨hwork.trans hd.1,hc.1,(hc.2 _ (by decide)).trans hd.2.2.1,
    (congrArg boolWordToNat hlength).trans hd.2.2.2⟩

end
end ShorECDLP.Paper2607_13816
