import ShorECDLP.Submission.«2607_13816».Arithmetic.PointTotalCircuit
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
attribute [local irreducible] fig14CoordinateState
/-- Replace only the canonical point word, preserving every other wire. -/
def pointWrite (P : ShorECDLP.Secp256k1.Point) (s : BasisState) : BasisState :=
  fun w => if w ∈ pointLogicalWires then wordPattern pointLogicalWires (pointCoordinateWord (fig14PointEncoding P)) w else s w

private theorem word_frame_ext (P : ShorECDLP.Secp256k1.Point) (s t : BasisState)
    (hw : wireValues pointLogicalWires t=pointCoordinateWord (fig14PointEncoding P))
    (hf : ∀ w, w ∉ pointLogicalWires → t w=s w) : t=pointWrite P s := by
  funext w
  by_cases hm : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hm]
    have hp := wordPattern_read pointLogicalWires (pointCoordinateWord (fig14PointEncoding P))
      pointLogicalWires_nodup (by simp)
    have he : wireValues pointLogicalWires t=wireValues pointLogicalWires
        (wordPattern pointLogicalWires (pointCoordinateWord (fig14PointEncoding P))) := hw.trans hp.symm
    exact List.map_inj_left.mp he w hm
  · simp only [pointWrite,if_neg hm]
    exact hf w hm

/-- Complete state, including all exceptions and every external wire. -/
theorem totalPointState_correct {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) (P : ShorECDLP.Secp256k1.Point)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hP : pointStateCoordinates s=fig14PointEncoding P) :
    totalPointState hC s=if s 836 then pointWrite (P+(.some hC)) s else s := by
  cases hq : s 836 with
  | false => simpa only [hq,Bool.false_eq_true,if_false] using totalPointState_disabled hC s hs hq
  | true =>
    simp only [if_true]
    exact word_frame_ext _ s _ (totalPointState_word hC P s hs hq hP) (totalPointState_frame hC s hs)

/-- Addition by infinity is a static empty program. -/
def pointAddProgram : ShorECDLP.Secp256k1.Point → AdaptiveCircuit
  | .zero => .done
  | .some hC => totalPointProgram hC
def pointAddState : ShorECDLP.Secp256k1.Point → BasisState → BasisState
  | .zero => id
  | .some hC => totalPointState hC

theorem pointAddState_correct (C P : ShorECDLP.Secp256k1.Point) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    pointAddState C s=if s 836 then pointWrite (P+C) s else s := by
  cases C with
  | zero =>
    have hw : wireValues pointLogicalWires s=pointCoordinateWord (fig14PointEncoding P) :=
      (pointStateCoordinates_word s hs).trans (congrArg pointCoordinateWord hP)
    have he := word_frame_ext P s s hw (by intros; rfl)
    change s=if s 836 then pointWrite (P+0) s else s
    rw [add_zero]
    cases s 836
    · rfl
    · exact he
  | some hC => exact totalPointState_correct hC P s hs hP

theorem pointAddProgram_coherent (C : ShorECDLP.Secp256k1.Point) :
    CoherentlyImplementsOn (pointAddProgram C)
      (Finsupp.lmapDomain ℂ ℂ (pointAddState C)) Secp256k1ZeroAllowedInputValid := by
  cases C with
  | zero =>
    have hd : CoherentlyImplementsOn AdaptiveCircuit.done LinearMap.id Secp256k1ZeroAllowedInputValid := by
      refine ⟨[1],?_,by simp⟩
      simp only [AdaptiveCircuit.run]
      apply List.Forall₂.cons
      · intro s hs; simp
      · exact .nil
    apply hd.congrIdeal
    intro s hs
    simp [pointAddState,ket]
  | some hC => exact totalPointProgram_coherent hC
end ShorECDLP.Paper2607_13816
