import ShorECDLP.Submission.«2607_13816».Challenge.BatchBoundary
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
noncomputable def signedBatchState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  windowYNegateState (placedBatchState Q w (windowYNegateState s))

theorem pointWrite_frame_eq (P : Point) (s t : BasisState)
    (h : ∀ w, w ∉ pointLogicalWires → s w=t w) : pointWrite P s=pointWrite P t := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hw]
  · simp only [pointWrite,if_neg hw,h w hw]

theorem signedBatchState_pointWrite (Q : Point) (w : OddWindow) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s)
    (hb : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm (windowYNegateState s)))
    (hz : ∀ j : Fin 6, j ≠ 5 →
      (relabelBasis batchPlacement.symm (windowYNegateState s)) ∘ batchWord 1024 j = fun _ => false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    signedBatchState Q w s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  have he := placedBatchState_pointWrite Q w _ hb hz ht hC hr P' hd
  have hsign : placedBatchState Q w (windowYNegateState s) 854 = s 854 :=
    (placedBatchState_frame Q w _ hb hz 854 (by decide +kernel)).trans
      ((windowYNegateState_correct s hs).2 854 (by decide +kernel))
  have hv := placedBatchState_ready Q w _ hb hz ht hC hr P' hd
  have hc := placedBatchState_coordinates Q w _ hb hz ht hC hr P' hd
  unfold signedBatchState
  rw [windowYNegateState_pointWrite (P' + .some hC) _ hv hc,hsign,he,pointWrite_overwrite]
  have hpoint : (if s 854 then P' + .some hC else -(P' + .some hC)) =
      P + if s 854 then .some hC else -(.some hC) := by
    cases hsg : s 854 <;> simp [P',hsg,add_comm]
  rw [hpoint]
  apply pointWrite_frame_eq
  intro v hv
  apply (windowYNegateState_correct s hs).2 v
  intro hy
  exact hv (List.mem_append_right _ (List.mem_append_left _ hy))
noncomputable def batchedWindowState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  signedBatchState Q w (signedLookupCoordinateState
    (fun a => fieldValue (windowPoint Q w a) .x) (fun a => fieldValue (windowPoint Q w a) .y) s)

theorem batchedWindowState_finite (Q : Point) (hQ : order • Q=0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : windowPoint Q w (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState Q w s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
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
  have he := signedBatchState_pointWrite Q w t ht.1.1 (batchedPointReady_batch _ hn)
    (batchedPointReady_words _ hn) hC hr' P hd
  change signedBatchState Q w t= _
  rw [he,hz]
  apply pointWrite_frame_eq
  intro v hv
  exact signedLookupCoordinateState_frame xs ys s hs.1 v
    (fun hx => hv (List.mem_append_left _ hx))
    (fun hy => hv (List.mem_append_right _ (List.mem_append_left _ hy)))
theorem windowPoint_ne_zero (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) (a : Nat) :
    windowPoint Q w a ≠ 0 := by
  cases w with
  | left j => exact oddWindowPoint_ne_zero G G_ne_zero generator_nsmul_eq_zero j.val a
  | right j => exact oddWindowPoint_ne_zero Q hn hQ j.val a

theorem batchedWindowState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress s)
        else -windowPoint Q w (tableAddressValue pointLookupAddress s)) s := by
  cases he : windowPoint Q w (tableAddressValue pointLookupAddress s) with
  | zero => exact False.elim (windowPoint_ne_zero Q hQ hn w _ he)
  | some hC => exact batchedWindowState_finite Q hQ w s hs hC he P hP

theorem signedBatchState_middle_ready (Q : Point) (w : OddWindow) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s)
    (hb : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm (windowYNegateState s)))
    (hz : ∀ j : Fin 6, j ≠ 5 →
      (relabelBasis batchPlacement.symm (windowYNegateState s)) ∘ batchWord 1024 j = fun _ => false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    Secp256k1ZeroAllowedInputValid (placedBatchState Q w (windowYNegateState s)) := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  exact placedBatchState_ready Q w _ hb hz ht hC hr P' hd

def SignedBatchReady (Q : Point) (w : OddWindow) (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y),
    constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC ∧
    ∃ P : Point, pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)

end ShorECDLP.Paper2607_13816.ChallengeMigration
