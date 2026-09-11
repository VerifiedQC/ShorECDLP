import ShorECDLP.Submission.«2607_13816».OrderFinding.PointEigenstates
import ShorECDLP.Submission.«2607_13816».Window.CorrectionSelection
import ShorECDLP.Submission.«2607_13816».Window.SignedCoordinate
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
private theorem address_append (a b : List Wire) (s : BasisState) :
    tableAddressValue (a++b) s=tableAddressValue a s+2^a.length*tableAddressValue b s := by
  induction a with
  | nil => simp [tableAddressValue]
  | cons w ws ih =>
    simp only [List.cons_append,tableAddressValue,List.length_cons,ih,pow_succ]
    ring

theorem correction_signed_address (s : BasisState) :
    tableAddressValue correctionTableBits s=tableAddressValue pointLookupAddress s+
      32768*(if s 854 then 1 else 0) := by
  have he : correctionTableBits=pointLookupAddress++[854] := by decide +kernel
  rw [he,address_append]
  simp only [show pointLookupAddress.length=15 from rfl,tableAddressValue]
  cases s 854 <;> simp

def signedCorrectionX (x : Nat → ShorECDLP.Fp) (a : Nat) : ShorECDLP.Fp := x (a%32768)
def signedCorrectionY (y : Nat → ShorECDLP.Fp) (a : Nat) : ShorECDLP.Fp :=
  if a<32768 then -y (a%32768) else y (a%32768)
theorem signedCorrection_nonsingular (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) (a : Nat) :
    ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (signedCorrectionX x a) (signedCorrectionY y a) := by
  unfold signedCorrectionX signedCorrectionY
  split
  · simpa only [ShorECDLP.Secp256k1.negY_eq_neg] using
      (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr (hc (a%32768))
  · exact hc _

theorem signedCorrection_selected (x y : Nat → ShorECDLP.Fp) (s : BasisState) :
    signedCorrectionX x (tableAddressValue correctionTableBits s)=x (tableAddressValue pointLookupAddress s) ∧
    signedCorrectionY y (tableAddressValue correctionTableBits s)=
      (if s 854 then y (tableAddressValue pointLookupAddress s) else -y (tableAddressValue pointLookupAddress s)) := by
  have hb : tableAddressValue pointLookupAddress s<32768 := tableAddressValue_lt pointLookupAddress s
  rw [correction_signed_address]
  cases h : s 854 <;> simp only [Bool.false_eq_true,ite_false,ite_true,mul_zero,mul_one,add_zero]
  · simp [signedCorrectionX,signedCorrectionY,hb,Nat.mod_eq_of_lt hb]
  · have hm : (tableAddressValue pointLookupAddress s+32768)%32768=tableAddressValue pointLookupAddress s := by omega
    have hn : ¬tableAddressValue pointLookupAddress s+32768<32768 := by omega
    simp [signedCorrectionX,signedCorrectionY,hm,hn]
def signedLookupPointProgram (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) : AdaptiveCircuit :=
  (signedLookupCoordinateProgram (fun a => (x a).val) (fun a => (y a).val)).seq
    (correctionTableProgram (signedCorrectionX x) (signedCorrectionY y) (signedCorrection_nonsingular x y hc))
def signedLookupPointState (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) (s : BasisState) : BasisState :=
  correctionTableState (signedCorrectionX x) (signedCorrectionY y) (signedCorrection_nonsingular x y hc)
    (signedLookupCoordinateState (fun a => (x a).val) (fun a => (y a).val) s)
private theorem correction_ready (s : BasisState) (hs : PointLookupValid s) :
    Clean correctionTablePath s ∧ Clean (558::559::pointCorrectionScratch) s := by
  refine ⟨?_,pointCorrection_ready s hs.1⟩
  intro w hw
  apply hs.1.1 w
  simp only [correctionTablePath,List.mem_range'_1] at hw
  simp only [List.mem_append,List.mem_range'_1]
  omega

theorem signedLookupPointProgram_coherent (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    CoherentlyImplementsOn (signedLookupPointProgram x y hc)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupPointState x y hc)) PointLookupValid := by
  have h := (signedLookupCoordinateProgram_coherent (fun a => (x a).val) (fun a => (y a).val)).seq
    (correctionTable_coherent_selected (signedCorrectionX x) (signedCorrectionY y) (signedCorrection_nonsingular x y hc)) (by
      intro s hs
      simpa [ket] using supportedOn_ket _ _ (correction_ready _ (signedLookupCoordinateState_ready _ _ s hs)))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket,signedLookupPointState]

private theorem coordinate_full_address (x y : Nat → Nat) (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue correctionTableBits (signedLookupCoordinateState x y s)=tableAddressValue correctionTableBits s := by
  apply tableAddressValue_congr
  intro w hw
  have h : ∀ w∈correctionTableBits, w∉List.range' 263 256 ∧ w∉List.range' 580 256 := by decide +kernel
  exact signedLookupCoordinateState_frame x y s hs w (h w hw).1 (h w hw).2

theorem signedLookupPointState_eq (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (s : BasisState) (hs : PointLookupValid s) :
    signedLookupPointState x y hc s=
      totalPointState (signedCorrection_nonsingular x y hc (tableAddressValue correctionTableBits s)) s := by
  rw [signedLookupPointState,correctionTableState_address,coordinate_full_address _ _ s hs]
  have hx := (signedCorrection_selected x y s).1
  have hy := (signedCorrection_selected x y s).2
  have hcoord := signedLookupCoordinateState_eq (fun a => (x a).val) (fun a => (y a).val) s hs
  have hyval : (signedCorrectionY y (tableAddressValue correctionTableBits s)).val=
      signedPointTableValue (fun a => (y a).val) s := by
    rw [hy]
    cases h : s 854 <;> simp [signedPointTableValue,h,ZMod.neg_val']
  unfold totalPointState
  apply congrArg (Classical.run (pointCorrectionCircuit (signedCorrection_nonsingular x y hc (tableAddressValue correctionTableBits s))))
  rw [hx,hyval,← hcoord]

theorem signedLookupPointState_word (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hP : pointStateCoordinates s=fig14PointEncoding P) :
    wireValues pointLogicalWires (signedLookupPointState x y hc s)=pointCoordinateWord
      (fig14PointEncoding (P+.some (signedCorrection_nonsingular x y hc (tableAddressValue correctionTableBits s)))) := by
  rw [signedLookupPointState_eq x y hc s hs]
  exact totalPointState_word _ P s hs.1 hs.2 hP

theorem signedLookupPointState_frame (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (s : BasisState) (hs : PointLookupValid s) :
    ∀ w, w∉pointLogicalWires → signedLookupPointState x y hc s w=s w := by
  rw [signedLookupPointState_eq x y hc s hs]
  exact totalPointState_frame _ s hs.1

theorem signedLookupPointProgram_wires (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (signedLookupPointProgram x y hc).wires ⊆ List.range 855 := by
  intro w hw
  rw [signedLookupPointProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · exact signedLookupCoordinateProgram_wires _ _ hw
  · exact correctionTableProgram_support _ _ _ hw

private theorem point_some_equal {x₁ y₁ x₂ y₂ : ShorECDLP.Fp}
    (h₁ : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁=x₂) (hy : y₁=y₂) :
    (.some h₁ : ShorECDLP.Secp256k1.Point)=.some h₂ :=
  by subst x₂; subst y₂; rfl
private theorem point_some_negative {x₁ y₁ x₂ y₂ : ShorECDLP.Fp}
    (h₁ : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂)
    (hx : x₁=x₂) (hy : y₁= -y₂) :
    (.some h₁ : ShorECDLP.Secp256k1.Point)= -(.some h₂) := by
  rw [WeierstrassCurve.Affine.Point.neg_some]
  exact point_some_equal _ _ hx (hy.trans (ShorECDLP.Secp256k1.negY_eq_neg _ _).symm)
theorem signedCorrection_point (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) (s : BasisState) :
    (.some (signedCorrection_nonsingular x y hc (tableAddressValue correctionTableBits s)) : ShorECDLP.Secp256k1.Point) =
    if s 854 then .some (hc (tableAddressValue pointLookupAddress s))
    else -(.some (hc (tableAddressValue pointLookupAddress s))) := by
  have hx := (signedCorrection_selected x y s).1
  have hy := (signedCorrection_selected x y s).2
  split
  · rename_i h
    exact point_some_equal _ _ hx (hy.trans (if_pos h))
  · rename_i h
    exact point_some_negative _ _ hx (hy.trans (if_neg h))

theorem signedLookupPointState_signed_word (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hP : pointStateCoordinates s=fig14PointEncoding P) :
    wireValues pointLogicalWires (signedLookupPointState x y hc s)=pointCoordinateWord
      (fig14PointEncoding (P+(if s 854 then .some (hc (tableAddressValue pointLookupAddress s))
        else -(.some (hc (tableAddressValue pointLookupAddress s)))))) := by
  exact (signedLookupPointState_word x y hc P s hs hP).trans
    (congrArg (fun Q => pointCoordinateWord (fig14PointEncoding (P+Q))) (signedCorrection_point x y hc s))

theorem signedLookupPointProgram_qubitCount (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (signedLookupPointProgram x y hc).qubitCount≤855 := by
  have h := signedLookupPointProgram_wires x y hc
  have hs : (signedLookupPointProgram x y hc).wires.dedup.toFinset ⊆ (List.range 855).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h (by simpa using hw))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range (n := 855))] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc

theorem signedLookupPointState_correct (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hP : pointStateCoordinates s=fig14PointEncoding P) :
    signedLookupPointState x y hc s=pointWrite
      (P+(if s 854 then .some (hc (tableAddressValue pointLookupAddress s))
        else -(.some (hc (tableAddressValue pointLookupAddress s))))) s := by
  rw [signedLookupPointState_eq x y hc s hs]
  have h := totalPointState_correct (signedCorrection_nonsingular x y hc (tableAddressValue correctionTableBits s)) P s hs.1 hP
  rw [hs.2,if_pos rfl] at h
  exact h.trans (congrArg (fun Q => pointWrite (P+Q) s) (signedCorrection_point x y hc s))

theorem signedLookupPointState_ready (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hP : pointStateCoordinates s=fig14PointEncoding P) :
    PointLookupValid (signedLookupPointState x y hc s) := by
  rw [signedLookupPointState_correct x y hc P s hs hP]
  exact ⟨pointWrite_valid _ s hs.1,(pointWrite_frame _ s 836 (by decide +kernel)).trans hs.2⟩

end
end ShorECDLP.Paper2607_13816
