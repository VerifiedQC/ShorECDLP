import ShorECDLP.Submission.«2607_13816».EEA.InitialEncoding

/-! # Initial packed work-register encoding -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

private theorem packed_word_append (a b : List Bool) :
    boolWordToNat (a ++ b) = boolWordToNat a + 2 ^ a.length * boolWordToNat b := by
  induction a with
  | nil => simp
  | cons bit bits ih =>
    simp only [List.cons_append, boolWordToNat_cons, ih, List.length_cons, pow_succ]
    ring

private theorem packed_zero_word (n : Nat) : boolWordToNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem packed_canonical_be (bits : List Bool) :
    bits = List.replicate (bits.length - (boolWordToNat bits.reverse).size) false ++
      (constantBits (boolWordToNat bits.reverse).size (boolWordToNat bits.reverse)).reverse := by
  have hsize : (boolWordToNat bits.reverse).size ≤ bits.length :=
    Nat.size_le.mpr (by simpa using boolWordToNat_lt_pow_two bits.reverse)
  apply List.reverse_injective
  apply boolWordToNat_injective_of_length
  · simp only [List.length_reverse, List.length_append, List.length_replicate, constantBits_length]
    omega
  · rw [List.reverse_append, List.reverse_reverse, List.reverse_replicate, packed_word_append,
      packed_zero_word, mul_zero, add_zero, boolWordToNat_constantBits]
    exact (Nat.mod_eq_of_lt (Nat.lt_size_self _)).symm

private theorem packed_be_of_value (bits : List Bool) (value : Nat)
    (hv : boolWordToNat bits.reverse = value) :
    bits = (constantBits bits.length value).reverse := by
  apply List.reverse_injective
  rw [List.reverse_reverse]
  apply boolWordToNat_injective_of_length (by simp only [List.length_reverse, constantBits_length])
  rw [boolWordToNat_constantBits, ← hv, Nat.mod_eq_of_lt]
  simpa only [List.length_reverse] using boolWordToNat_lt_pow_two bits.reverse

private theorem packed_initial_banks (after : BasisState) (p value : Nat)
    (h4 : after 4 = true) (h5 : after 5 = false) (h6 : after 6 = false)
    (hp : wireValues (List.range' 7 256).reverse after = constantBits 256 p)
    (hfit : p < 2 ^ 256)
    (hhead : ∀ i : Fin 3, after (263 + i.val) = false)
    (hv : boolWordToNat (wireValues (List.range' 266 256).reverse after) = value) :
    wireValues (List.range' 4 259) after = [true, false] ++ (constantBits 257 p).reverse ∧
    wireValues (List.range' 263 259) after =
      List.replicate (259 - value.size) false ++ (constantBits value.size value).reverse := by
  have hr : boolWordToNat (wireValues (List.range' 6 257) after).reverse = p := by
    change boolWordToNat (after 6 :: wireValues (List.range' 7 256) after).reverse = p
    rw [h6, List.reverse_cons, packed_word_append]
    simp only [boolWordToNat_cons, boolWordToNat_nil, Bool.toNat_false, mul_zero, add_zero]
    rw [show (wireValues (List.range' 7 256) after).reverse =
      wireValues (List.range' 7 256).reverse after by simp only [wireValues, List.map_reverse],
      hp, boolWordToNat_constantBits, Nat.mod_eq_of_lt hfit]
  have hrbits := packed_be_of_value _ p hr
  simp only [wireValues, List.length_map, List.length_range'] at hrbits
  constructor
  · change after 4 :: after 5 :: wireValues (List.range' 6 257) after = _
    rw [h4, h5]
    exact congrArg (fun bits => [true, false] ++ bits) hrbits
  · have hw : boolWordToNat (wireValues (List.range' 263 259) after).reverse = value := by
      change boolWordToNat (after 263 :: after 264 :: after 265 ::
        wireValues (List.range' 266 256) after).reverse = value
      rw [show after 263 = false from hhead ⟨0, by decide⟩,
        show after 264 = false from hhead ⟨1, by decide⟩,
        show after 265 = false from hhead ⟨2, by decide⟩]
      simpa only [List.reverse_cons, packed_word_append, boolWordToNat_cons,
        boolWordToNat_nil, Bool.toNat_false, mul_zero, zero_add, add_zero,
        wireValues, List.map_reverse] using hv
    have hb := packed_canonical_be (wireValues (List.range' 263 259) after)
    rw [hw] at hb
    simpa only [wireValues, List.length_map, List.length_range'] using hb

private theorem packed_constant_zero (width : Nat) :
    constantBits width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simpa only [constantBits, List.replicate_succ, xorConstantBits, Nat.testBit_zero,
      Bool.cond_false, Nat.zero_div] using congrArg (List.cons false) ih

private theorem packed_modulus_size : (2 ^ 256 - 2 ^ 32 - 977 : Nat).size = 256 := by
  have hlo := Nat.lt_size.mpr (show 2 ^ 255 ≤ (2 ^ 256 - 2 ^ 32 - 977 : Nat) by decide)
  have hhi := Nat.size_le.mpr (show (2 ^ 256 - 2 ^ 32 - 977 : Nat) < 2 ^ 256 by decide)
  omega

attribute [local irreducible] eeaPreprocessIdealState

/-- Both complete work banks contain the canonical initial packed fields, including
all guard and leading-zero bits. The second bank has zero initial rotation. -/
theorem eeaPreprocess_initial_workBanks (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977) :
    let after := eeaPreprocessIdealState state
    let initial := paperInitial (2 ^ 256 - 2 ^ 32 - 977)
      (boolWordToNat (wireValues (List.range' 263 256) state))
    let width := (packedView (2 ^ 256 - 2 ^ 32 - 977) initial).width
    wireValues (List.range' 4 259) after =
      constantBits initial.lT initial.t ++ [false] ++
      (constantBits initial.lQ initial.q).reverse ++
      (constantBits (width - initial.lT - 1 - initial.lQ) initial.r).reverse ∧
    wireValues (List.range' 263 259) after =
      constantBits (width - initial.lRPrime) initial.tPrime ++
      (constantBits initial.lRPrime initial.rPrime).reverse := by
  have h := eeaPreprocessIdealState_correct state hclean hx hxp
  have hn := eeaPreprocess_initial_divisor state hclean hx hxp
  dsimp only at h hn ⊢
  have hb := packed_initial_banks (eeaPreprocessIdealState state)
    (2 ^ 256 - 2 ^ 32 - 977) _ h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 (by decide) h.2.2.2.2.2.2.2.2.1 hn.1
  simp only [paperInitial, packedView,
    packed_modulus_size] at hn hb ⊢
  simp only [packed_constant_zero, show constantBits 1 1 = [true] from rfl,
    List.replicate_zero, List.reverse_nil, List.append_nil,
    List.cons_append, List.nil_append, Nat.reduceAdd, Nat.reduceSub]
  simpa only [List.cons_append, List.nil_append] using hb

private theorem packed_clean_word (wires : List Wire) (state : BasisState)
    (h : Clean wires state) : wireValues wires state = constantBits wires.length 0 := by
  rw [packed_constant_zero]
  calc
    _ = wires.map (fun _ => false) := List.map_congr_left h
    _ = _ := by simp

/-- Phase, sign, parity and all four metadata words encode the logical initial state.
Zero lengths and zero shift use the source's all-ones nine-bit sentinel. -/
theorem eeaPreprocess_initial_metadata (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977) :
    let after := eeaPreprocessIdealState state
    let initial := paperInitial (2 ^ 256 - 2 ^ 32 - 977)
      (boolWordToNat (wireValues (List.range' 263 256) state))
    (after 0, after 1) = initial.phase.bits ∧ after 3 = initial.sign ∧ after 2 = initial.iter ∧
    wireValues (List.range' 522 9) after = constantBits 9 (initial.lT - 1) ∧
    wireValues (List.range' 531 9) after =
      constantBits 9 (if initial.lQ = 0 then 511 else initial.lQ - 1) ∧
    wireValues (List.range' 540 9) after =
      constantBits 9 (if initial.shift = 0 then 511 else initial.shift - 1) ∧
    wireValues (List.range' 549 9) after = constantBits 9 (initial.lRPrime - 1) := by
  have h := eeaPreprocessIdealState_correct state hclean hx hxp
  have hn := eeaPreprocess_initial_divisor state hclean hx hxp
  dsimp only at h hn ⊢
  have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h0 := hc 0 (by simp)
  have h1 := hc 1 (by simp)
  have h3 := hc 3 (by simp)
  have ht : Clean (List.range' 522 9) (eeaPreprocessIdealState state) := by
    intro w hw
    exact hc w (by simp only [List.mem_append]; exact Or.inl (Or.inl hw))
  have htw := packed_clean_word _ _ ht
  simp only [List.length_range'] at htw
  simp only [paperInitial, EEAPhase.bits, Nat.sub_self, ↓reduceIte] at hn ⊢
  exact ⟨Prod.ext h0 h1, h3, hn.2.1, htw, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, hn.2.2⟩

end
end ShorECDLP.Paper2607_13816
