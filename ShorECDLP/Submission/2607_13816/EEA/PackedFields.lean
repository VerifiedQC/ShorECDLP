import ShorECDLP.Submission.«2607_13816».EEA.RangeExtraction
import ShorECDLP.Submission.«2607_13816».EEA.InitialPacked

/-! # Decoding the logical fields of canonical packed banks -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem packed_middle (pre field suffix : List Bool) :
    (((pre ++ field) ++ suffix).drop pre.length).take field.length = field := by
  simp

/-- Arithmetic extraction recovers a fitting little-endian field amid arbitrary neighboring bits. -/
theorem packedField_le_decode (pre suffix : List Bool) (width value : Nat)
    (hfit : value < 2^width) :
    (boolWordToNat (pre ++ constantBits width value ++ suffix) / 2^pre.length) %
      2^width = value := by
  have h := boolWordToNat_slice (pre ++ constantBits width value ++ suffix) pre.length width
    (by simp only [List.length_append, constantBits_length]; omega)
  have hm := packed_middle pre (constantBits width value) suffix
  simp only [constantBits_length] at hm
  rw [hm, boolWordToNat_constantBits, Nat.mod_eq_of_lt hfit] at h
  exact h.symm

/-- Arithmetic extraction recovers a fitting big-endian field amid arbitrary neighboring bits. -/
theorem packedField_be_decode (pre suffix : List Bool) (width value : Nat)
    (hfit : value < 2^width) :
    (boolWordToNat (pre ++ (constantBits width value).reverse ++ suffix).reverse /
      2^suffix.length) % 2^width = value := by
  simpa only [List.reverse_append, List.reverse_reverse, List.length_reverse, List.append_assoc]
    using packedField_le_decode suffix.reverse pre.reverse width value hfit

/-- All three logical values are recoverable from the canonical first bank. -/
theorem packedWork1_decode (s : EEAState) (width : Nat)
    (hspan : s.lT + 1 + s.lQ ≤ width)
    (ht : s.t < 2^s.lT) (hq : s.q < 2^s.lQ)
    (hr : s.r < 2^(width-s.lT-1-s.lQ)) :
    let bank := constantBits s.lT s.t ++ [false] ++ (constantBits s.lQ s.q).reverse ++
      (constantBits (width-s.lT-1-s.lQ) s.r).reverse
    bank.length = width ∧ boolWordToNat bank % 2^s.lT = s.t ∧
    (boolWordToNat bank.reverse / 2^(width-s.lT-1-s.lQ)) % 2^s.lQ = s.q ∧
    boolWordToNat bank.reverse % 2^(width-s.lT-1-s.lQ) = s.r := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_reverse, constantBits_length, List.length_singleton]
    omega
  constructor
  · simpa only [List.nil_append, List.length_nil, Nat.pow_zero, Nat.div_one, List.append_assoc]
      using packedField_le_decode [] ([false] ++ (constantBits s.lQ s.q).reverse ++
        (constantBits (width-s.lT-1-s.lQ) s.r).reverse) s.lT s.t ht
  constructor
  · simpa only [List.length_reverse, constantBits_length, List.append_assoc]
      using packedField_be_decode (constantBits s.lT s.t ++ [false])
        (constantBits (width-s.lT-1-s.lQ) s.r).reverse s.lQ s.q hq
  · simpa only [List.append_nil, List.length_nil, Nat.pow_zero, Nat.div_one]
      using packedField_be_decode (constantBits s.lT s.t ++ [false] ++
        (constantBits s.lQ s.q).reverse) ([] : List Bool) (width-s.lT-1-s.lQ) s.r hr

/-- Both logical values are recoverable from the unrotated canonical second bank. -/
theorem packedWork2_decode (s : EEAState) (width : Nat)
    (hspan : s.lRPrime ≤ width)
    (ht : s.tPrime < 2^(width-s.lRPrime)) (hr : s.rPrime < 2^s.lRPrime) :
    let bank := constantBits (width-s.lRPrime) s.tPrime ++ (constantBits s.lRPrime s.rPrime).reverse
    bank.length = width ∧ boolWordToNat bank % 2^(width-s.lRPrime) = s.tPrime ∧
    boolWordToNat bank.reverse % 2^s.lRPrime = s.rPrime := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_reverse, constantBits_length]
    omega
  constructor
  · simpa only [List.nil_append, List.length_nil, Nat.pow_zero, Nat.div_one]
      using packedField_le_decode [] (constantBits s.lRPrime s.rPrime).reverse
        (width-s.lRPrime) s.tPrime ht
  · simpa only [List.append_nil, List.length_nil, Nat.pow_zero, Nat.div_one]
      using packedField_be_decode (constantBits (width-s.lRPrime) s.tPrime) ([] : List Bool) s.lRPrime s.rPrime hr

end ShorECDLP.Paper2607_13816
