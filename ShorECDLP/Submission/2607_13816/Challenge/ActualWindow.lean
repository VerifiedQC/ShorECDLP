import ShorECDLP.Submission.«2607_13816».Challenge.PreparedBatch
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
private theorem parkedWindow_valid (start : Nat) (hs : 855≤start) (s : BasisState)
    (hv : PointLookupValid s) : PointLookupValid (relabelBasis (windowAddressPerm start hs).symm s) := by
  have he (w : Wire) (hw : w<839) : relabelBasis (windowAddressPerm start hs).symm s w=s w := by
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w hw]
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro w hw
    have hb : w<839 := by simp only [List.mem_append,List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    rw [he w hb]
    exact hv.1.1 w hw
  · rw [he 837 (by decide)]; exact hv.1.2.1
  · have hh : wireValues (List.range' 263 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 263 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.1
  · have hh : wireValues (List.range' 580 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 580 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.2
  · rw [he 836 (by decide)]; exact hv.2

private theorem point_bank_bound (w : Wire) (hw : w∈pointLogicalWires) : w<839 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega
private theorem relabel_pointWrite (start : Nat) (hs : 855≤start)
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis (windowAddressPerm start hs)
      (pointWrite P (relabelBasis (windowAddressPerm start hs).symm s))=pointWrite P s := by
  have hsym : (windowAddressPerm start hs).symm=windowAddressPerm start hs := rfl
  funext w
  by_cases hw : w∈pointLogicalWires
  · have he := windowAddressPerm_core start hs w (point_bank_bound w hw)
    simp [relabelBasis,hsym,he,pointWrite,hw]
  · have hn : (windowAddressPerm start hs).symm w∉pointLogicalWires := by
      intro h
      have he := windowAddressPerm_core start hs _ (point_bank_bound _ h)
      rw [Equiv.apply_symm_apply] at he
      exact hw (he ▸ h)
    simp [relabelBasis,pointWrite,hw,hn]

private theorem relabel_coordinates (start : Nat) (hs : 855≤start) (s : BasisState) :
    pointStateCoordinates (relabelBasis (windowAddressPerm start hs).symm s)=pointStateCoordinates s := by
  have he (bits : List Wire) (hb : ∀ w∈bits,w<839) :
      wireValues bits (relabelBasis (windowAddressPerm start hs).symm s)=wireValues bits s := by
    apply List.map_congr_left
    intro w hw
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w (hb w hw)]
  have hx := he (List.range' 263 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hy := he (List.range' 580 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs 838 (by decide)]


theorem windowAddressPerm_workspace (w : Wire) (hw : w ∈ batchWorkspace) :
    windowAddressPerm 855 (by decide) w=w := by
  change windowAddressSwap 855 w=w
  simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
  unfold windowAddressSwap
  split_ifs <;> (try dsimp only [Wire] at *) <;> omega

theorem actualWindow_pullback_ready (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (relabelBasis (windowAddressPerm 855 (by decide)).symm s) := by
  refine ⟨parkedWindow_valid 855 (by decide) s hs.1,?_⟩
  intro w hw
  change s (windowAddressPerm 855 (by decide) w)=false
  rw [windowAddressPerm_workspace w hw]
  exact hs.2 w hw

theorem actualWindow_pullback_valid (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (relabelBasis (windowAddressPerm 855 (by decide)).symm s) := by
  obtain ⟨hs,P,hP⟩ := hs
  exact ⟨actualWindow_pullback_ready s hs,P,(relabel_coordinates 855 (by decide) s).trans hP⟩

noncomputable def actualBatchedWindowState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm 855 (by decide))
    (preparedBatchState Q w (relabelBasis (windowAddressPerm 855 (by decide)).symm s))

theorem actualBatchedWindow_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn (((actualBatchedWindow w).program start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
  have h := (batchedWindowPreparedSource_coherent Q hQ hn w).relabel (windowAddressPerm 855 (by decide))
  have hr : CoherentlyImplementsOn ((batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide)))
      ((relabelState (windowAddressPerm 855 (by decide))).comp
        ((Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)).comp
          (relabelState (windowAddressPerm 855 (by decide)).symm))) BatchedWindowValid := by
    obtain ⟨cs,hc,hm⟩ := h
    exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (actualWindow_pullback_valid s hs)),hm⟩
  have he : CoherentlyImplementsOn ((batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide)))
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
    apply hr.congrIdeal
    intro s hs
    simp [actualBatchedWindowState,LinearMap.comp_apply,relabelState,ket]
  unfold CoherentlyImplementsOn at he ⊢
  rw [actualBatchedWindow_run w start Q hQ history]
  exact he

theorem actualBatchedWindowState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))
        else -windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))) s := by
  unfold actualBatchedWindowState
  rw [preparedBatchState_correct Q hQ hn w _ (actualWindow_pullback_ready s hs) P
    ((relabel_coordinates 855 (by decide) s).trans hP),relabel_pointWrite]
  have he : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854=s 870 := by
    simp only [relabelBasis,Equiv.symm_symm]
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [he]

private theorem address_word_eq (bits : List Wire) (s : BasisState) :
    tableAddressValue bits s=boolWordToNat (wireValues bits s) := by
  induction bits with
  | nil => rfl
  | cons w ws ih => simpa only [tableAddressValue,wireValues,List.map_cons,boolWordToNat] using congrArg (fun n => (s w).toNat+2*n) ih

theorem actualWindow_selected_address (s : BasisState) (hs : BatchedPointReady s) :
    tableAddressValue pointLookupAddress
      (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s))=
      signedTableAddress 32768 (windowRawDigit 0 s) := by
  have hq : relabelBasis (windowAddressPerm 855 (by decide)).symm s 836=true :=
    (actualWindow_pullback_ready s hs).1.2
  rw [address_word_eq,batchPrepareState,signedAddressState_value _ _ _ _ hq]
  have ha := parkedWindow_address 855 (by decide) s
  rw [address_word_eq,address_word_eq] at ha
  have hz : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854=s 870 := by
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [ha,hz]
  rfl


theorem actualBatchedWindowState_selected (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
        else -windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) s := by
  rw [actualBatchedWindowState_correct Q hQ hn w s hs P hP,actualWindow_selected_address s hs]

theorem actualBatchedWindowState_valid (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (actualBatchedWindowState Q w s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

theorem actualBatchedWindowState_frame (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) (v : Wire) (hv : v∉pointLogicalWires) :
    actualBatchedWindowState Q w s v=s v := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected Q hQ hn w s hs P hP]
  simp [pointWrite,hv]

/-- The mixed first-window table may contain infinity; this direct-load theorem
has no nonzero-table-entry hypothesis. -/
theorem actualFirstWindow_coherent (Q : Point) (hQ : order • Q=0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actualFirstWindow.program start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite
        (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
          ((2^(16*15)) • G) (tableAddressValue (List.range' 855 16) s)) s))
      (DirectPointLookupValid (List.range' 519 16) 836) := by
  unfold CoherentlyImplementsOn
  rw [actualFirstWindow_run start Q hQ history]
  exact physicalPointLookup_coherent _
end ShorECDLP.Paper2607_13816.ChallengeMigration
