import ShorECDLP.Submission.«2607_13816».Arithmetic.PointStateEncoding
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
attribute [local irreducible] fig14CoordinateState
/-- Complete coordinate program followed by physical exceptional correction. -/
def totalPointProgram {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) : AdaptiveCircuit :=
  (fig14CoordinateProgram x₂.val y₂.val).seq (.unitary (pointCorrectionCircuit hC) .done)
def totalPointState {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) (s : BasisState) : BasisState :=
  Classical.run (pointCorrectionCircuit hC) (fig14CoordinateState x₂.val y₂.val s)

theorem totalPointState_word {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) (P : ShorECDLP.Secp256k1.Point)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=true)
    (hP : pointStateCoordinates s=fig14PointEncoding P) :
    wireValues pointLogicalWires (totalPointState hC s)=pointCoordinateWord (fig14PointEncoding (P+(.some hC))) := by
  have hr := fig14CoordinateState_ready x₂.val y₂.val s hs
  have he := fig14CoordinateState_encoded x₂ y₂ s hs hq
  have hw := pointStateCoordinates_word _ hr
  have hc := pointCorrection_ready _ hr
  have hq' : fig14CoordinateState x₂.val y₂.val s 836=true :=
    (fig14CoordinateState_frame x₂.val y₂.val s hs 836 (by decide +kernel) (by decide +kernel)).trans hq
  rw [he,hP] at hw
  exact pointCorrectionCircuit_correct hC P _ hc hq' hw

theorem totalPointState_frame {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    ∀ w, w ∉ pointLogicalWires → totalPointState hC s w=s w := by
  intro w hw
  have hf := pointCorrectionCircuit_frame hC _ (pointCorrection_ready _ (fig14CoordinateState_ready x₂.val y₂.val s hs)) w hw
  have hx : w ∉ List.range' 263 256 := by intro hm; exact hw (List.mem_append_left _ hm)
  have hy : w ∉ List.range' 580 256 := by intro hm; exact hw (List.mem_append_right _ (List.mem_append_left _ hm))
  exact hf.trans (fig14CoordinateState_frame x₂.val y₂.val s hs w hx hy)

theorem totalPointState_disabled {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=false) :
    totalPointState hC s=s := by
  rw [totalPointState,fig14CoordinateState_disabled x₂.val y₂.val (ZMod.val_lt x₂) s hs hq]
  exact pointCorrectionCircuit_disabled hC s (pointCorrection_ready s hs) hq

theorem totalPointProgram_coherent {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    CoherentlyImplementsOn (totalPointProgram hC)
      (Finsupp.lmapDomain ℂ ℂ (totalPointState hC)) Secp256k1ZeroAllowedInputValid := by
  have hsecond := CoherentlyImplementsOn.unitary (pointCorrectionCircuit hC) (fun _ => True)
  have hh := (fig14CoordinateProgram_coherent x₂.val y₂.val).seq hsecond (by
    intro s hs
    simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    exact supportedOn_ket _ _ trivial)
  apply hh.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply]
  have he := pointCorrectionCircuit_ket hC (fig14CoordinateState x₂.val y₂.val s)
  simpa only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,totalPointState] using he
end ShorECDLP.Paper2607_13816
