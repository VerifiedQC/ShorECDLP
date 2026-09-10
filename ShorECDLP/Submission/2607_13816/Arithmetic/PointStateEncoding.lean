import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCorrectionCircuit
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
/-- Read the canonical field coordinates and the explicit infinity bit. -/
def pointStateCoordinates (s : BasisState) : Bool × (ShorECDLP.Fp × ShorECDLP.Fp) :=
  (s 838,(boolWordToNat (wireValues (List.range' 263 256) s),
    boolWordToNat (wireValues (List.range' 580 256) s)))
private theorem canonical_word (R : List Wire) (s : BasisState) (hl : R.length=256)
    (hv : boolWordToNat (wireValues R s)<ShorECDLP.p) :
    wireValues R s=constantBits 256 ((boolWordToNat (wireValues R s) : ShorECDLP.Fp).val) := by
  apply boolWordToNat_injective_of_length (by simp [wireValues,hl])
  rw [boolWordToNat_constantBits,ZMod.val_natCast,Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt]
  exact hv.trans (by decide +kernel)
theorem pointStateCoordinates_word (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    wireValues pointLogicalWires s=pointCoordinateWord (pointStateCoordinates s) := by
  have hx := canonical_word (List.range' 263 256) s (by simp) hs.2.2.1
  have hy := canonical_word (List.range' 580 256) s (by simp) hs.2.2.2
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,wireValues,List.map_append,
    List.map_cons,List.map_nil,pointCoordinateWord,pointStateCoordinates]
  exact congrArg₂ (fun a b => a++(b++[s 838])) hx hy |>.trans (List.append_assoc _ _ _).symm

attribute [local irreducible] fig14CoordinateState
theorem fig14CoordinateState_encoded (x₂ y₂ : ShorECDLP.Fp)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=true) :
    pointStateCoordinates (fig14CoordinateState x₂.val y₂.val s)=
      fig14EncodedEquiv x₂ y₂ (pointStateCoordinates s) := by
  have he := fig14CoordinateState_equiv x₂.val y₂.val (ZMod.val_lt x₂) (ZMod.val_lt y₂) s hs hq
  have hi := fig14CoordinateState_frame x₂.val y₂.val s hs 838 (by decide +kernel) (by decide +kernel)
  apply Prod.ext hi
  simpa only [pointStateCoordinates,fig14EncodedEquiv,Equiv.prodCongr_apply,ZMod.natCast_zmod_val] using he

theorem pointCorrection_ready (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Clean (558::559::pointCorrectionScratch) s := by
  intro w hw
  apply hs.1 w
  simp only [pointCorrectionScratch,List.mem_cons,List.mem_range'_1] at hw
  simp only [List.mem_append,List.mem_range'_1]
  simp only [Wire] at hw ⊢
  omega

end ShorECDLP.Paper2607_13816
