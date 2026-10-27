import ShorECDLP.Submission.«2607_13816».Challenge.BatchedWindowState
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
private theorem restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

theorem composeCoherent {a b : AdaptiveCircuit} {f g : BasisState → BasisState}
    {P R : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) P)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) R)
    (hf : ∀ s, P s → R (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) P := by
  have h := ha.seq hb (by
    intro s hs
    simpa [ket] using supportedOn_ket R (f s) (hf s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

noncomputable def signedBatchSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (windowYNegate.seq (placedBatchSource Q w)).seq windowYNegate

theorem signedBatchSource_coherent (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn (signedBatchSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (signedBatchState Q w)) (SignedBatchReady Q w) := by
  have hneg : CoherentlyImplementsOn windowYNegate (Finsupp.lmapDomain ℂ ℂ windowYNegateState)
      (SignedBatchReady Q w) := restrictCoherent windowYNegate_coherent (fun s hs => hs.1.1.1)
  have hfirst := composeCoherent hneg (placedBatchSource_state Q w) (fun s hs =>
    batchedPointReady_batch _ (windowYNegateState_batchedReady s hs.1))
  have hlast := composeCoherent hfirst windowYNegate_coherent (by
    intro s hs
    obtain ⟨hr,x,y,hC,hrow,P,hdata⟩ := hs
    have hn := windowYNegateState_batchedReady s hr
    exact signedBatchState_middle_ready Q w s hr.1.1 (batchedPointReady_batch _ hn)
      (batchedPointReady_words _ hn) hC hrow P hdata)
  exact hlast
theorem batchedWindow_coordinate_ready (Q : Point) (hQ : order • Q=0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : windowPoint Q w (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    SignedBatchReady Q w (signedLookupCoordinateState
      (fun a => fieldValue (windowPoint Q w a) .x) (fun a => fieldValue (windowPoint Q w a) .y) s) := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have hn := windowYNegateState_batchedReady t ht
  have ha : tableAddressValue pointLookupAddress t=tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854=s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hr' : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState t))))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    unfold batchWindowRows
    rw [coefficientAt_window,oddWindowCoefficients_point w _ Q hQ]
    have hb : tableAddressValue pointLookupAddress s < 32768 := tableAddressValue_lt pointLookupAddress s
    simpa only [Nat.mod_eq_of_lt hb] using hr
  have hx : xs (tableAddressValue pointLookupAddress s)=x.val := by simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s)=y.val := by simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s=(if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases s 854 <;> simp [ZMod.neg_val']
  have hd : pointStateCoordinates t=fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  exact ⟨ht,x,y,hC,hr',P,hd⟩

def BatchedWindowValid (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ P : Point, pointStateCoordinates s=fig14PointEncoding P

theorem batchedWindowSources_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) :
    CoherentlyImplementsOn (sequenceCircuit (batchedWindowSources Q w))
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState Q w)) BatchedWindowValid := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
  have hfirst : CoherentlyImplementsOn (signedLookupCoordinateProgram xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    restrictCoherent (signedLookupCoordinateProgram_coherent xs ys) (fun s hs => hs.1.1)
  have h := composeCoherent hfirst (signedBatchSource_coherent Q w) (by
    intro s hs
    obtain ⟨hs,P,hP⟩ := hs
    cases he : windowPoint Q w (tableAddressValue pointLookupAddress s) with
    | zero => exact False.elim (windowPoint_ne_zero Q hQ hn w _ he)
    | some hC => exact batchedWindow_coordinate_ready Q hQ w s hs hC he P hP)
  simpa only [batchedWindowSources,sequenceCircuit,signedBatchSource,adaptive_seq_assoc,adaptive_seq_done,
    batchedWindowState,xs,ys] using h
theorem batchedWindowCore_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((batchedWindowCore w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState Q w)) BatchedWindowValid := by
  have h := batchedWindowSources_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := batchedWindowCore_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

end ShorECDLP.Paper2607_13816.ChallengeMigration
