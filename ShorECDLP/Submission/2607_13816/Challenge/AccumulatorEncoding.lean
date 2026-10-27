import ShorECDLP.Submission.«2607_13816».Challenge.PlacedBatch
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointWordEdge
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointStateEncoding
import ShorECDLP.Submission.«2607_13816».Challenge.BatchFrame
import ShorECDLP.Submission.«2607_13816».OrderFinding.PointEigenstates
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

theorem accumulatorPort_list : List.ofFn accumulatorPort = pointLogicalWires := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,pointLogicalWires_length]
  · intro i hi hj
    have hib : i < 513 := by simpa only [List.length_ofFn] using hi
    simp only [List.getElem_ofFn,pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
      List.getElem_append,List.length_range',List.getElem_range',accumulatorPort]
    by_cases h : i < 256
    · simp only [h,ite_true,dite_true,one_mul]
    · by_cases h2 : i < 512
      · have h3 : i-256 < 256 := by omega
        simp only [h,h2,h3,ite_false,ite_true,dite_false,dite_true,one_mul]
      · have h3 : ¬ i-256 < 256 := by omega
        have he : i-256-256=0 := by omega
        simp only [h,h2,h3,ite_false,dite_false,he,List.getElem_cons_zero]

private theorem encoding_constant_succ (width value : Nat) :
    constantBits (width+1) value = value.testBit 0 :: constantBits width (value/2) := by
  unfold constantBits
  simp only [List.replicate_succ, xorConstantBits]
  cases hbit : value.testBit 0 <;> simp
private theorem encoding_constant_getD (width value i : Nat) (hi : i < width) :
    (constantBits width value).getD i false = value.testBit i := by
  induction width generalizing value i with
  | zero => omega
  | succ width ih =>
    rw [encoding_constant_succ]
    cases i with
    | zero => rfl
    | succ i =>
      change (constantBits width (value/2)).getD i false = value.testBit (i+1)
      rw [ih _ _ (by omega), Nat.testBit_div_two]
private theorem encoding_constant_getElem (width value i : Nat) (hi : i < (constantBits width value).length) :
    (constantBits width value)[i] = value.testBit i := by
  have h := encoding_constant_getD width value i (by simpa only [constantBits_length] using hi)
  simpa only [List.getD_eq_getElem _ false hi] using h

theorem coordinateWordBits_list (v : Bool × (Fp × Fp)) :
    List.ofFn (coordinateWordBits v) = pointCoordinateWord v := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,pointCoordinateWord_length]
  · intro i hi hj
    have hib : i < 513 := by simpa only [List.length_ofFn] using hi
    simp only [List.getElem_ofFn,pointCoordinateWord,coordinateWordBits,
      List.getElem_append,List.length_append,constantBits_length,encoding_constant_getElem]
    by_cases h : i < 256
    · have h2 : i < 256+256 := by omega
      simp only [h,h2,ite_true,dite_true]
    · by_cases h2 : i < 512
      · simp only [h,h2,ite_false,ite_true,dite_false,dite_true]
      · have he : i-(256+256)=0 := by omega
        simp only [h,h2,ite_false,dite_false,he,List.getElem_cons_zero]

theorem accumulatorPort_word (st : BasisState) :
    List.ofFn (st ∘ accumulatorPort) = wireValues pointLogicalWires st := by
  rw [← List.map_ofFn,accumulatorPort_list]
  rfl

theorem accumulatorPort_encoding_iff (st : BasisState) (v : Bool × (Fp × Fp)) :
    st ∘ accumulatorPort = coordinateWordBits v ↔ wireValues pointLogicalWires st = pointCoordinateWord v := by
  rw [← accumulatorPort_word,← coordinateWordBits_list]
  exact List.ofFn_inj.symm

theorem accumulatorPort_coordinates (st : BasisState) (hs : Secp256k1ZeroAllowedInputValid st) :
    st ∘ accumulatorPort = coordinateWordBits (pointStateCoordinates st) :=
  (accumulatorPort_encoding_iff st _).mpr (pointStateCoordinates_word st hs)

attribute [local irreducible] batchWindowUnitary batchUnitary

theorem placedBatchState_word (Q : Point) (w : OddWindow) (st : BasisState)
    (hs : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm st))
    (hz : ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm st) ∘ batchWord 1024 j = fun _ => false)
    (hv : Secp256k1ZeroAllowedInputValid st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm st)))) = .some hC)
    (P : Point) (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P)) :
    wireValues pointLogicalWires (placedBatchState Q w st) = pointCoordinateWord (fig14PointEncoding (P + .some hC)) := by
  apply (accumulatorPort_encoding_iff _ _).mp
  apply placedBatchState_finite Q w st hs hz hC hr P
  exact (accumulatorPort_coordinates st hv).trans (congrArg coordinateWordBits hdata)

theorem placedBatchState_frame (Q : Point) (win : OddWindow) (st : BasisState)
    (hs : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm st))
    (hz : ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm st) ∘ batchWord 1024 j = fun _ => false)
    (w : Wire) (hw : w ∉ pointLogicalWires) : placedBatchState Q win st w = st w := by
  have hnot : ∀ i, batchPlacement.symm w ≠ batchWord 1024 5 i := by
    intro i he
    have he' : w = accumulatorPort i := by
      have h := congrArg batchPlacement he
      simpa only [Equiv.apply_symm_apply,batchPlacement_data] using h
    apply hw
    rw [← accumulatorPort_list]
    exact List.mem_ofFn.mpr ⟨i,he'.symm⟩
  have hf := batchUnitary_fullFrame coefficientAt Q (batchWindowRows win) 1024 batchWindowTree
    836 pointLookupPath batchWindowTree_layout batchWindowTree_below _ hs hz _ hnot
  change Classical.run (batchWindowUnitary Q win) (relabelBasis batchPlacement.symm st) (batchPlacement.symm w) = st w
  unfold batchWindowUnitary
  rw [hf]
  simp only [relabelBasis,Equiv.symm_symm,Equiv.apply_symm_apply]
theorem accumulator_word_frame_ext (P : Point) (s t : BasisState)
    (hw : wireValues pointLogicalWires t = pointCoordinateWord (fig14PointEncoding P))
    (hf : ∀ w, w ∉ pointLogicalWires → t w = s w) : t = pointWrite P s := by
  funext w
  by_cases hm : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hm]
    have hp := wordPattern_read pointLogicalWires (pointCoordinateWord (fig14PointEncoding P))
      pointLogicalWires_nodup (by simp)
    exact List.map_inj_left.mp (hw.trans hp.symm) w hm
  · simp only [pointWrite,if_neg hm]
    exact hf w hm

theorem placedBatchState_pointWrite (Q : Point) (w : OddWindow) (st : BasisState)
    (hs : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm st))
    (hz : ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm st) ∘ batchWord 1024 j = fun _ => false)
    (hv : Secp256k1ZeroAllowedInputValid st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm st)))) = .some hC)
    (P : Point) (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P)) :
    placedBatchState Q w st = pointWrite (P + .some hC) st :=
  accumulator_word_frame_ext _ st _ (placedBatchState_word Q w st hs hz hv hC hr P hdata)
    (placedBatchState_frame Q w st hs hz)

theorem placedBatchState_coordinates (Q : Point) (w : OddWindow) (st : BasisState)
    (hs : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm st))
    (hz : ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm st) ∘ batchWord 1024 j = fun _ => false)
    (hv : Secp256k1ZeroAllowedInputValid st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm st)))) = .some hC)
    (P : Point) (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P)) :
    pointStateCoordinates (placedBatchState Q w st) = fig14PointEncoding (P + .some hC) := by
  rw [placedBatchState_pointWrite Q w st hs hz hv hC hr P hdata]
  exact pointWrite_coordinates _ st

theorem placedBatchState_ready (Q : Point) (w : OddWindow) (st : BasisState)
    (hs : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm st))
    (hz : ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm st) ∘ batchWord 1024 j = fun _ => false)
    (hv : Secp256k1ZeroAllowedInputValid st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm st)))) = .some hC)
    (P : Point) (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P)) :
    Secp256k1ZeroAllowedInputValid (placedBatchState Q w st) := by
  rw [placedBatchState_pointWrite Q w st hs hz hv hC hr P hdata]
  exact pointWrite_valid _ st hv

end ShorECDLP.Paper2607_13816.ChallengeMigration
