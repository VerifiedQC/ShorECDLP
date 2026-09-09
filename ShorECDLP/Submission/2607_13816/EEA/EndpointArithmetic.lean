import ShorECDLP.Submission.«2607_13816».EEA.Endpoint
import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks

/-! # Arithmetic interpretation of prepared interval endpoints -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem subtraction_balance (m a b : Nat) (ha : a ≤ b + m) :
    (b + m - a) % m + a ≡ b [MOD m] := by
  calc
    (b + m - a) % m + a ≡ (b + m - a) + a [MOD m] :=
      (Nat.mod_modEq _ _).add_right a
    _ = b + m := Nat.sub_add_cancel ha
    _ ≡ b [MOD m] := by simp

private theorem subtractWord_balance (a b : List Bool) (h : a.length = b.length) :
    boolWordToNat (cuccaroSubBits false a b) + boolWordToNat a ≡
      boolWordToNat b [MOD 2^a.length] := by
  rw [boolWordToNat_cuccaroSubBits_false a b h]
  exact subtraction_balance _ _ _ (by have := boolWordToNat_lt_pow_two a; omega)

private theorem addWord_balance (a b : List Bool) (h : a.length = b.length) :
    boolWordToNat (cuccaroAddBits false a b) ≡
      boolWordToNat a + boolWordToNat b [MOD 2^a.length] := by
  rw [boolWordToNat_cuccaroAddBits false a b h]
  simpa using Nat.mod_modEq (boolWordToNat a + boolWordToNat b) (2^a.length)

private theorem left_balance (t q : List Bool) (offset : Nat) (h : t.length = q.length) :
    boolWordToNat (intervalLeftBits t q offset) + offset ≡
      boolWordToNat t + boolWordToNat q + 4 [MOD 2^q.length] := by
  have hl : (cuccaroAddBits false t q).length = q.length := by
    rw [cuccaroAddBits_length false t q h, h]
  have hf : (cuccaroAddBits false (constantBits q.length 4)
      (cuccaroAddBits false t q)).length = q.length := by
    rw [cuccaroAddBits_length]; simp; simp [hl]
  have hs := subtractWord_balance (constantBits q.length offset)
    (cuccaroAddBits false (constantBits q.length 4) (cuccaroAddBits false t q))
    (by simp [hf])
  have ha := addWord_balance (constantBits q.length 4) (cuccaroAddBits false t q)
    (by simp [hl])
  have hb := addWord_balance t q h
  simp only [constantBits_length, boolWordToNat_constantBits] at hs ha
  rw [h] at hb
  have he := ((Nat.ModEq.refl (boolWordToNat (intervalLeftBits t q offset))).add
    (Nat.mod_modEq offset (2^q.length)).symm).trans hs
  exact (he.trans ha).trans (by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.mod_modEq 4 (2^q.length)).add hb)

private theorem right_balance (s : List Bool) (n offset : Nat) :
    boolWordToNat (intervalRightBits s n offset) + offset + boolWordToNat s ≡
      n + 2 [MOD 2^s.length] := by
  have hs := subtractWord_balance (constantBits s.length offset)
    (constMinusBits s (n+2)) (by simp)
  simp only [constantBits_length, boolWordToNat_constantBits] at hs
  have he := ((Nat.ModEq.refl (boolWordToNat (intervalRightBits s n offset))).add
    (Nat.mod_modEq offset (2^s.length)).symm).trans hs
  have hr : boolWordToNat (constMinusBits s (n+2)) + boolWordToNat s ≡
      n+2 [MOD 2^s.length] := by
    rw [boolWordToNat_constMinusBits]
    exact subtraction_balance _ _ _ (by have := boolWordToNat_lt_pow_two s; omega)
  exact (he.add_right _).trans hr

private theorem truthMinusOne_balance (width value : Nat) (hw : 0 < width) :
    truthMinusOneValue width value + 1 ≡ value [MOD 2^width] := by
  have hm : 1 < 2^width := Nat.one_lt_two_pow hw.ne'
  change (value + 2^width - 1 % 2^width) % 2^width + 1 ≡ value [MOD 2^width]
  rw [Nat.mod_eq_of_lt hm]
  exact subtraction_balance _ _ _ (by omega)

private theorem left_interpretation (t q : List Bool) (T Q offset : Nat)
    (h : t.length = q.length) (hw : 0 < q.length)
    (ht : boolWordToNat t = truthMinusOneValue q.length T)
    (hq : boolWordToNat q = truthMinusOneValue q.length Q)
    (hlo : offset ≤ T + Q + 2) (hhi : T + Q + 2 - offset < 2^q.length) :
    boolWordToNat (intervalLeftBits t q offset) = T + Q + 2 - offset := by
  have hb := left_balance t q offset h
  have ht' := truthMinusOne_balance q.length T hw
  have hq' := truthMinusOne_balance q.length Q hw
  rw [← ht] at ht'
  rw [← hq] at hq'
  have he : boolWordToNat t + boolWordToNat q + 4 ≡ T + Q + 2 [MOD 2^q.length] := by
    have hh := (ht'.add hq').add_right 2
    have hhLeft : (boolWordToNat t + 1 + (boolWordToNat q + 1)) + 2 =
        boolWordToNat t + boolWordToNat q + 4 := by omega
    rw [hhLeft] at hh
    exact hh
  have heq : T+Q+2 = (T+Q+2-offset)+offset := by omega
  rw [heq] at he
  have hh := Nat.ModEq.add_right_cancel' offset (hb.trans he)
  exact hh.eq_of_lt_of_lt (by
    have := boolWordToNat_lt_pow_two (intervalLeftBits t q offset)
    simpa only [intervalLeftBits_length t q offset h] using this) hhi

private theorem right_interpretation (s : List Bool) (shift n offset : Nat)
    (hw : 0 < s.length)
    (hs : boolWordToNat s = truthMinusOneValue s.length shift)
    (hlo : shift + offset ≤ n+3) (hhi : n+3-shift-offset < 2^s.length) :
    boolWordToNat (intervalRightBits s n offset) = n+3-shift-offset := by
  have hb := (right_balance s n offset).add_right 1
  have hs' := truthMinusOne_balance s.length shift hw
  rw [← hs] at hs'
  have he : boolWordToNat (intervalRightBits s n offset) + (shift+offset) ≡
      n+3 [MOD 2^s.length] := by
    have hr := (hs'.add_left (boolWordToNat (intervalRightBits s n offset) + offset)).symm
    have hh := hr.trans (by simpa [Nat.add_assoc] using hb)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  have heq : n+3 = (n+3-shift-offset)+(shift+offset) := by omega
  rw [heq] at he
  exact (Nat.ModEq.add_right_cancel' (shift+offset) he).eq_of_lt_of_lt (by
    have := boolWordToNat_lt_pow_two (intervalRightBits s n offset)
    simpa using this) hhi

/-- The literal preparation circuit decodes the stored truth-minus-one lengths into the
intended interval indices. Zero logical values use the same modular sentinel encoding;
only the resulting indices must be nonnegative and fit their respective words. -/
theorem prepareIntervalEndpoints_arithmetic
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (n offset T Q shift : Nat) (state : BasisState)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hqPositive : 0 < lengthQ.length) (hsPositive : 0 < lengthS.length)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry)
    (hclean : Clean (scratch ++ [carry]) state)
    (ht : boolWordToNat (wireValues lengthT state) = truthMinusOneValue lengthQ.length T)
    (hq : boolWordToNat (wireValues lengthQ state) = truthMinusOneValue lengthQ.length Q)
    (hs : boolWordToNat (wireValues lengthS state) = truthMinusOneValue lengthS.length shift)
    (hleftLow : offset ≤ T+Q+2) (hleftHigh : T+Q+2-offset < 2^lengthQ.length)
    (hrightLow : shift+offset ≤ n+3) (hrightHigh : n+3-shift-offset < 2^lengthS.length) :
    let after := run (prepareIntervalEndpoints lengthT lengthQ lengthS scratch carry n offset) state
    wireValues lengthT after = wireValues lengthT state ∧
      boolWordToNat (wireValues lengthQ after) = T+Q+2-offset ∧
      boolWordToNat (wireValues lengthS after) = n+3-shift-offset ∧
      Clean (scratch ++ [carry]) after ∧
      ∀ wire, wire ∉ lengthQ → wire ∉ lengthS → after wire = state wire := by
  have hc := prepareIntervalEndpoints_correct lengthT lengthQ lengthS scratch carry n offset state
    htqLength hqWidth hsWidth hsPositive hlayout hclean
  refine ⟨hc.1, ?_, ?_, hc.2.2.2.1, hc.2.2.2.2⟩
  · rw [hc.2.1]
    exact left_interpretation _ _ T Q offset (by simpa [wireValues] using htqLength)
      (by simpa [wireValues] using hqPositive) (by simpa [wireValues] using ht)
      (by simpa [wireValues] using hq) hleftLow (by simpa [wireValues] using hleftHigh)
  · rw [hc.2.2.1]
    exact right_interpretation _ shift n offset (by simpa [wireValues] using hsPositive)
      (by simpa [wireValues] using hs) hrightLow (by simpa [wireValues] using hrightHigh)

end ShorECDLP.Paper2607_13816
