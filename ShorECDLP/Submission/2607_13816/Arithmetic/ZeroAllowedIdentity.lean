import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowed

/-! Zero inputs are a literal identity extension of the nonzero Figure 15 operations. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem inverse_one_mod : paperInverse ShorECDLP.p 1 % ShorECDLP.p=1 := by
  have hh := paperRun_inverse_mod_prime ShorECDLP.Secp256k1.p_prime (x:=1) (by omega) (by decide +kernel)
  have hv := congrArg ZMod.val hh
  simpa using hv
private theorem word_frame_ext (s t : BasisState)
    (he : boolWordToNat (wireValues (List.range' 580 256) s)=boolWordToNat (wireValues (List.range' 580 256) t))
    (hf : ∀ w, w ∉ List.range' 580 256 → s w=t w) : s=t := by
  have hw : wireValues (List.range' 580 256) s=wireValues (List.range' 580 256) t :=
    boolWordToNat_injective_of_length (by simp [wireValues]) he
  funext w
  by_cases h : w ∈ List.range' 580 256
  · exact List.map_inj_left.mp hw w h
  · exact hf w h

theorem zeroAllowedDivisionOutputState_zero (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hz : boolWordToNat (wireValues (List.range' 263 256) s)=0) : zeroAllowedDivisionOutputState s=s := by
  apply word_frame_ext
  · rw [zeroAllowedDivisionOutputState_word s hs,if_pos hz,Nat.mul_mod,inverse_one_mod,Nat.mul_one,
      Nat.mod_mod,Nat.mod_eq_of_lt hs.2.2.2]
  · intro w hw
    simp only [zeroAllowedDivisionOutputState_frame s hs,if_neg hw]
theorem zeroAllowedMultiplicationOutputState_zero (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hz : boolWordToNat (wireValues (List.range' 263 256) s)=0) : zeroAllowedMultiplicationOutputState s=s := by
  apply word_frame_ext
  · rw [zeroAllowedMultiplicationOutputState_word s hs,if_pos hz,Nat.mul_one,Nat.mod_eq_of_lt hs.2.2.2]
  · intro w hw
    simp only [zeroAllowedMultiplicationOutputState_frame s hs,if_neg hw]
end ShorECDLP.Paper2607_13816
