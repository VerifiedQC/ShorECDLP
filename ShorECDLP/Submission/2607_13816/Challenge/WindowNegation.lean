import ShorECDLP.Submission.«2607_13816».Challenge.CoordinateConjugacy
import ShorECDLP.Submission.«2607_13816».Challenge.AccumulatorEncoding
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointStateEncoding
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨Secp256k1.p_prime⟩

def windowYNegateState : BasisState → BasisState :=
  negativeModularNegateState (List.range' 580 256) (constantBits 256 ShorECDLP.p) 854 558

theorem windowYNegateState_correct (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    boolWordToNat (wireValues (List.range' 580 256) (windowYNegateState s)) =
      (if s 854 then boolWordToNat (wireValues (List.range' 580 256) s)
        else (ShorECDLP.p-boolWordToNat (wireValues (List.range' 580 256) s))%ShorECDLP.p) ∧
    ∀ w, w ∉ List.range' 580 256 → windowYNegateState s w=s w := by
  exact negativeModularNegateState_correct _ _ ShorECDLP.p 854 558 s
    (by simp) (by simp) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (hs.1 558 (by decide +kernel)) (by simp; decide +kernel) hs.2.2.2
    (by rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt (by decide +kernel)])

theorem windowYNegateState_ready (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (windowYNegateState s) := by
  have hc := windowYNegateState_correct s hs
  refine ⟨?_,?_,?_,?_⟩
  · intro w hw
    rw [hc.2 w (by simp only [List.mem_append,List.mem_range'_1] at hw ⊢; omega)]
    exact hs.1 w hw
  · rw [hc.2 837 (by decide +kernel)]
    exact hs.2.1
  · have he : wireValues (List.range' 263 256) (windowYNegateState s) =
        wireValues (List.range' 263 256) s := by
      apply List.map_congr_left
      intro w hw
      exact hc.2 w (by simp only [List.mem_range'_1] at hw ⊢; omega)
    rw [he]
    exact hs.2.2.1
  · rw [hc.1]
    split
    · exact hs.2.2.2
    · exact Nat.mod_lt _ Secp256k1.p_prime.pos

theorem windowYNegate_coherent : CoherentlyImplementsOn windowYNegate
    (Finsupp.lmapDomain ℂ ℂ windowYNegateState) Secp256k1ZeroAllowedInputValid := by
  have h := negativeControlledModularNegate_coherent (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) ShorECDLP.p 854 559 560 561 558
    (by simp) (by simp) (by simp) (by decide +kernel) Secp256k1.p_prime.pos
  obtain ⟨cs,hc,hm⟩ := h
  refine ⟨cs,hc.imp ?_,hm⟩
  intro b c hb s hs
  apply hb s
  exact ⟨hs.1 559 (by decide +kernel),hs.1 560 (by decide +kernel),hs.1 561 (by decide +kernel),hs.1 558 (by decide +kernel),hs.2.2.2⟩
theorem windowYNegateState_coordinates (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    pointStateCoordinates (windowYNegateState s) =
      (if s 854 then pointStateCoordinates s else
        ((pointStateCoordinates s).1,((pointStateCoordinates s).2.1,-(pointStateCoordinates s).2.2))) := by
  have hc := windowYNegateState_correct s hs
  have hx : wireValues (List.range' 263 256) (windowYNegateState s) =
      wireValues (List.range' 263 256) s := by
    apply List.map_congr_left
    intro w hw
    exact hc.2 w (by simp only [List.mem_range'_1] at hw ⊢; omega)
  have hz := hc.2 838 (by decide)
  unfold pointStateCoordinates
  rw [hz,hx,hc.1]
  cases hsg : s 854
  · simp only [Bool.false_eq_true,ite_false]
    apply congrArg (Prod.mk (s 838))
    apply congrArg (Prod.mk _)
    apply ZMod.val_injective
    rw [ZMod.val_natCast,ZMod.neg_val',ZMod.val_natCast,Nat.mod_eq_of_lt hs.2.2.2]
    exact Nat.mod_mod _ _
  · simp only [ite_true]

theorem windowYNegateState_pointWrite (P : Point) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    windowYNegateState s = pointWrite (if s 854 then P else -P) s := by
  apply accumulator_word_frame_ext
  · have hc := windowYNegateState_coordinates s hs
    have hw := pointStateCoordinates_word _ (windowYNegateState_ready s hs)
    rw [hc,hP] at hw
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,fig14PointEncoding_neg,encodedNegY] using hw
    · simpa only [hsg,ite_true] using hw
  · intro w hw
    apply (windowYNegateState_correct s hs).2 w
    intro hy
    exact hw (List.mem_append_right _ (List.mem_append_left _ hy))
end ShorECDLP.Paper2607_13816.ChallengeMigration
