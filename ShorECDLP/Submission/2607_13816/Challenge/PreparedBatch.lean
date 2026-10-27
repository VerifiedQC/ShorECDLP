import ShorECDLP.Submission.«2607_13816».Challenge.BatchedWindowCoherent
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
def batchPrepareState : BasisState → BasisState := signedAddressState 836 854 pointLookupAddress

theorem batchPrepareState_frame (s : BasisState) (w : Wire) (hw : w ∉ pointLookupAddress) :
    batchPrepareState s w=s w := signedAddressState_frame 836 854 pointLookupAddress s w hw

private theorem address_outside_point (w : Wire) (hw : w ∈ pointLogicalWires) : w ∉ pointLookupAddress := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false] at hw
  simp only [pointLookupAddress,List.mem_range'_1]
  dsimp only [Wire] at *
  omega

private theorem prepare_word (s : BasisState) (bits : List Wire)
    (h : ∀ w ∈ bits, w ∉ pointLookupAddress) : wireValues bits (batchPrepareState s)=wireValues bits s := by
  apply List.map_congr_left
  intro w hw
  exact batchPrepareState_frame s w (h w hw)

theorem batchPrepareState_ready (s : BasisState) (hs : BatchedPointReady s) : BatchedPointReady (batchPrepareState s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩
  · intro w hw
    rw [batchPrepareState_frame s w (by
      simp only [List.mem_append,List.mem_range'_1] at hw
      simp only [pointLookupAddress,List.mem_range'_1]
      omega)]
    exact hs.1.1.1 w hw
  · rw [batchPrepareState_frame s 837 (by decide)]
    exact hs.1.1.2.1
  · rw [prepare_word s (List.range' 263 256) (fun w hw => address_outside_point w (List.mem_append_left _ hw))]
    exact hs.1.1.2.2.1
  · rw [prepare_word s (List.range' 580 256) (fun w hw => address_outside_point w (List.mem_append_right _ (List.mem_append_left _ hw)))]
    exact hs.1.1.2.2.2
  · rw [batchPrepareState_frame s 836 (by decide)]
    exact hs.1.2
  · intro w hw
    rw [batchPrepareState_frame s w (by
      simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
      simp only [pointLookupAddress,List.mem_range'_1]
      omega)]
    exact hs.2 w hw

theorem batchPrepareState_coordinates (s : BasisState) : pointStateCoordinates (batchPrepareState s)=pointStateCoordinates s := by
  unfold pointStateCoordinates
  rw [batchPrepareState_frame s 838 (by decide),
    prepare_word s (List.range' 263 256) (fun w hw => address_outside_point w (List.mem_append_left _ hw)),
    prepare_word s (List.range' 580 256) (fun w hw => address_outside_point w (List.mem_append_right _ (List.mem_append_left _ hw)))]

theorem batchPrepareState_pointWrite (P : Point) (s : BasisState) :
    batchPrepareState (pointWrite P s)=pointWrite P (batchPrepareState s) := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · rw [batchPrepareState_frame _ w (address_outside_point w hw)]
    simp only [pointWrite,if_pos hw]
  · rw [pointWrite_frame _ _ w hw]
    unfold batchPrepareState signedAddressState tableXorState
    rw [pointWrite_frame P s 854 (by decide +kernel),pointWrite_frame P s 836 (by decide +kernel),pointWrite_frame P s w hw]

theorem batchPrepareState_involution (s : BasisState) : batchPrepareState (batchPrepareState s)=s :=
  signedAddressState_involution 836 854 pointLookupAddress (by decide) (by decide) s
theorem batchPrepareState_valid (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (batchPrepareState s) := by
  obtain ⟨hs,P,hP⟩ := hs
  exact ⟨batchPrepareState_ready s hs,P,(batchPrepareState_coordinates s).trans hP⟩

theorem batchedWindowState_valid (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (batchedWindowState Q w s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [batchedWindowState_correct Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

noncomputable def preparedBatchState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  batchPrepareState (batchedWindowState Q w (batchPrepareState s))

theorem preparedBatchState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    preparedBatchState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress (batchPrepareState s))
        else -windowPoint Q w (tableAddressValue pointLookupAddress (batchPrepareState s))) s := by
  unfold preparedBatchState
  rw [batchedWindowState_correct Q hQ hn w _ (batchPrepareState_ready s hs) P
    ((batchPrepareState_coordinates s).trans hP),batchPrepareState_pointWrite,
    batchPrepareState_involution,batchPrepareState_frame s 854 (by decide)]

theorem batchPrepare_coherent : CoherentlyImplementsOn
    (.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done)
    (Finsupp.lmapDomain ℂ ℂ batchPrepareState) BatchedWindowValid := by
  have h := CoherentlyImplementsOn.unitary (signedAddressCircuit 836 854 pointLookupAddress) BatchedWindowValid
  apply h.congrIdeal
  intro s hs
  simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,batchPrepareState] using
    signedAddressCircuit_ket 836 854 pointLookupAddress (by decide) (by decide) (by decide) s

attribute [local irreducible] batchPrepareState batchedWindowState

theorem batchedWindowPreparedSource_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) :
    CoherentlyImplementsOn (batchedWindowPreparedSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)) BatchedWindowValid := by
  have hc := composeCoherent (batchedWindowSources_coherent Q hQ hn w) batchPrepare_coherent
    (batchedWindowState_valid Q hQ hn w)
  have h := composeCoherent (f := batchPrepareState)
    (g := fun s => batchPrepareState (batchedWindowState Q w s))
    batchPrepare_coherent hc batchPrepareState_valid
  exact h

theorem batchedWindowPrepared_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((batchedWindowPrepared w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)) BatchedWindowValid := by
  have h := batchedWindowPreparedSource_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := batchedWindowPrepared_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

end ShorECDLP.Paper2607_13816.ChallengeMigration
