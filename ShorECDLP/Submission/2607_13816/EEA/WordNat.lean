import ShorECDLP.Submission.«2607_13816».EEA.Affine

/-!
# Little-endian Boolean words as naturals

The paper circuits state their direct semantics on fixed-width little-endian Boolean words.
This module supplies the arithmetic boundary used to interpret those words modulo `2^width`.
In particular it proves that the source `constMinusBits` map is the modular reflection
`x ↦ value - x`, and hence is an involution.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

/-- Natural represented by a little-endian Boolean word. -/
def boolWordToNat : List Bool → Nat
  | [] => 0
  | bit :: bits => bit.toNat + 2 * boolWordToNat bits

@[simp]
theorem boolWordToNat_nil : boolWordToNat [] = 0 := rfl

@[simp]
theorem boolWordToNat_cons (bit : Bool) (bits : List Bool) :
    boolWordToNat (bit :: bits) = bit.toNat + 2 * boolWordToNat bits := rfl

/-- Every fixed-width Boolean word lies in its canonical residue range. -/
theorem boolWordToNat_lt_pow_two (bits : List Bool) :
    boolWordToNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
      cases bit <;> simp only [boolWordToNat_cons, Bool.toNat_false,
        Bool.toNat_true, List.length_cons, Nat.pow_succ]
      all_goals omega

private theorem lowBit_mod_two_mul_pow
    (bit x width : Nat) (hbit : bit < 2) :
    (bit + 2 * x) % (2 * 2 ^ width) =
      bit + 2 * (x % 2 ^ width) := by
  rw [Nat.add_mod]
  have hmodulus : 0 < 2 * 2 ^ width :=
    Nat.mul_pos (by omega) (Nat.two_pow_pos width)
  rw [Nat.mod_eq_of_lt (by omega : bit < 2 * 2 ^ width)]
  rw [Nat.mul_mod_mul_left]
  have hx := Nat.mod_lt x (Nat.two_pow_pos width)
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem cuccaro_cell_value (addend target carry : Bool) :
    (cuccaroSum addend target carry).toNat +
        2 * (cuccaroCarry addend target carry).toNat =
      addend.toNat + target.toNat + carry.toNat := by
  cases addend <;> cases target <;> cases carry <;>
    decide

/-- The Boolean Cuccaro recurrence is addition modulo its word width. -/
theorem boolWordToNat_cuccaroAddBits
    (carry : Bool) (addends targets : List Bool)
    (hlength : addends.length = targets.length) :
    boolWordToNat (cuccaroAddBits carry addends targets) =
      (carry.toNat + boolWordToNat addends + boolWordToNat targets) %
        2 ^ addends.length := by
  induction addends generalizing targets carry with
  | nil =>
      have : targets = [] := List.length_eq_zero_iff.mp hlength.symm
      subst targets
      cases carry <;> rfl
  | cons addend addends ih =>
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          have htail : addends.length = targets.length := by
            simpa using hlength
          simp only [cuccaroAddBits, boolWordToNat_cons, List.length_cons]
          rw [ih (cuccaroCarry addend target carry) targets htail]
          rw [Nat.pow_succ]
          rw [show 2 ^ addends.length * 2 = 2 * 2 ^ addends.length by omega]
          rw [← lowBit_mod_two_mul_pow
            (cuccaroSum addend target carry).toNat
            ((cuccaroCarry addend target carry).toNat
              + boolWordToNat addends + boolWordToNat targets)
            addends.length (by cases cuccaroSum addend target carry <;> decide)]
          have hcell := cuccaro_cell_value addend target carry
          congr 1
          omega

private theorem increment_cell_value (bit carry : Bool) :
    (Bool.xor bit carry).toNat + 2 * (bit && carry).toNat =
      bit.toNat + carry.toNat := by
  cases bit <;> cases carry <;> decide

@[simp]
theorem incrementBits_length (carry : Bool) (bits : List Bool) :
    (incrementBits carry bits).length = bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp [incrementBits, ih]

/-- The increment recurrence adds its input carry modulo the word width. -/
theorem boolWordToNat_incrementBits
    (carry : Bool) (bits : List Bool) :
    boolWordToNat (incrementBits carry bits) =
      (carry.toNat + boolWordToNat bits) % 2 ^ bits.length := by
  induction bits generalizing carry with
  | nil => cases carry <;> rfl
  | cons bit bits ih =>
      simp only [incrementBits, boolWordToNat_cons, List.length_cons]
      rw [ih (bit && carry), Nat.pow_succ]
      rw [show 2 ^ bits.length * 2 = 2 * 2 ^ bits.length by omega]
      rw [← lowBit_mod_two_mul_pow
        (Bool.xor bit carry).toNat
        ((bit && carry).toNat + boolWordToNat bits)
        bits.length (by cases Bool.xor bit carry <;> decide)]
      have hcell := increment_cell_value bit carry
      congr 1
      omega

/-- Complementing a width-`w` word maps `x` to `2^w - 1 - x`. -/
theorem boolWordToNat_map_not_add (bits : List Bool) :
    boolWordToNat (bits.map Bool.not) + boolWordToNat bits =
      2 ^ bits.length - 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;>
        simp only [List.map_cons, Bool.not_false, Bool.not_true,
          boolWordToNat_cons, Bool.toNat_false, Bool.toNat_true,
          List.length_cons, Nat.pow_succ]
      all_goals have hp : 0 < 2 ^ bits.length := Nat.two_pow_pos bits.length
      all_goals omega

private theorem testBit_zero_toNat (value : Nat) :
    (value.testBit 0).toNat = value % 2 := by
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one value with hzero | hone
  · simp [hzero]
  · simp [hone]

private theorem constantBits_succ (width value : Nat) :
    constantBits (width + 1) value =
      value.testBit 0 :: constantBits width (value / 2) := by
  unfold constantBits
  simp only [List.replicate_succ, xorConstantBits]
  cases hbit : value.testBit 0 <;> simp

@[simp]
theorem constantBits_length (width value : Nat) :
    (constantBits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
      rw [constantBits_succ]
      simp [ih]

/-- The Cuccaro word recurrence preserves the common operand width. -/
theorem cuccaroAddBits_length
    (carry : Bool) (addends targets : List Bool)
    (hlength : addends.length = targets.length) :
    (cuccaroAddBits carry addends targets).length = addends.length := by
  induction addends generalizing targets carry with
  | nil =>
      have : targets = [] := List.length_eq_zero_iff.mp hlength.symm
      subst targets
      rfl
  | cons addend addends ih =>
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          simp only [cuccaroAddBits, List.length_cons, Nat.succ.injEq]
          exact ih (cuccaroCarry addend target carry) targets (by simpa using hlength)

/-- The inverse Cuccaro recurrence preserves the common operand width. -/
theorem cuccaroSubBits_length
    (carry : Bool) (addends sums : List Bool)
    (hlength : addends.length = sums.length) :
    (cuccaroSubBits carry addends sums).length = addends.length := by
  induction addends generalizing sums carry with
  | nil =>
      have : sums = [] := List.length_eq_zero_iff.mp hlength.symm
      subst sums
      rfl
  | cons addend addends ih =>
      cases sums with
      | nil => simp at hlength
      | cons sum sums =>
          simp only [cuccaroSubBits, List.length_cons, Nat.succ.injEq]
          exact ih _ sums (by simpa using hlength)

/-- `constantBits width value` is the canonical low-`width` residue of `value`. -/
theorem boolWordToNat_constantBits (width value : Nat) :
    boolWordToNat (constantBits width value) = value % 2 ^ width := by
  induction width generalizing value with
  | zero =>
      change 0 = value % 1
      rw [Nat.mod_one]
  | succ width ih =>
      rw [constantBits_succ]
      simp only [boolWordToNat_cons]
      rw [ih (value / 2), Nat.pow_succ]
      rw [show 2 ^ width * 2 = 2 * 2 ^ width by omega]
      rw [← lowBit_mod_two_mul_pow (value.testBit 0).toNat (value / 2)
        width (by cases value.testBit 0 <;> decide)]
      rw [testBit_zero_toNat]
      have hdecomp := Nat.mod_add_div value 2
      congr 1

/-- Equal-width little-endian words have unique natural interpretations. -/
theorem boolWordToNat_injective_of_length
    {left right : List Bool} (hlength : left.length = right.length)
    (hvalue : boolWordToNat left = boolWordToNat right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      exact (List.length_eq_zero_iff.mp hlength.symm).symm
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simpa using hlength
          have hhead : left = right := by
            cases left <;> cases right <;>
              simp only [boolWordToNat_cons, Bool.toNat_false,
                Bool.toNat_true] at hvalue
            all_goals try rfl
            all_goals omega
          subst right
          have htailValue : boolWordToNat lefts = boolWordToNat rights := by
            cases left <;>
              simp only [boolWordToNat_cons, Bool.toNat_false,
                Bool.toNat_true] at hvalue
            all_goals omega
          exact congrArg (List.cons left) (ih htail htailValue)

/-- The source two's-complement construction is `value - bits` modulo `2^width`. -/
theorem boolWordToNat_constMinusBits (bits : List Bool) (value : Nat) :
    boolWordToNat (constMinusBits bits value) =
      (value + 2 ^ bits.length - boolWordToNat bits) % 2 ^ bits.length := by
  have hlenNot : (bits.map Bool.not).length = bits.length := by simp
  have hincLen : (incrementBits true (bits.map Bool.not)).length = bits.length := by simp
  have hconstLen : (constantBits bits.length value).length = bits.length := by simp
  have hbitsBound := boolWordToNat_lt_pow_two bits
  have hnotSum := boolWordToNat_map_not_add bits
  have hinc := boolWordToNat_incrementBits true (bits.map Bool.not)
  rw [hlenNot] at hinc
  have hincValue :
      boolWordToNat (incrementBits true (bits.map Bool.not)) =
        (2 ^ bits.length - boolWordToNat bits) % 2 ^ bits.length := by
    rw [hinc]
    simp only [Bool.toNat_true]
    congr 1
    have hp := Nat.two_pow_pos bits.length
    omega
  unfold constMinusBits
  rw [boolWordToNat_cuccaroAddBits false _ _ (by
    exact hconstLen.trans hincLen.symm)]
  rw [hconstLen, boolWordToNat_constantBits, hincValue]
  simp only [Bool.toNat_false, Nat.zero_add]
  rw [Nat.add_sub_assoc (Nat.le_of_lt hbitsBound) value]
  simp only [Nat.add_mod, Nat.mod_mod]

@[simp]
theorem constMinusBits_length (bits : List Bool) (value : Nat) :
    (constMinusBits bits value).length = bits.length := by
  unfold constMinusBits
  rw [cuccaroAddBits_length]
  · simp
  · simp

private theorem modularReflect_reduced_involutive
    (modulus value current : Nat)
    (hvalue : value < modulus)
    (hcurrent : current < modulus) :
    (value + modulus - ((value + modulus - current) % modulus)) % modulus =
      current := by
  by_cases hle : current ≤ value
  · have hreflect : (value + modulus - current) % modulus = value - current := by
      rw [Nat.add_comm value modulus, Nat.add_sub_assoc hle modulus]
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hreflect]
    have heq : value + modulus - (value - current) = modulus + current := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt hcurrent]
  · have hreflectLt : value + modulus - current < modulus := by omega
    rw [Nat.mod_eq_of_lt hreflectLt]
    have heq : value + modulus - (value + modulus - current) = current := by omega
    rw [heq, Nat.mod_eq_of_lt hcurrent]

private theorem modularReflect_reduce
    (modulus value current : Nat) (hcurrent : current ≤ modulus) :
    (value + modulus - current) % modulus =
      (value % modulus + modulus - current) % modulus := by
  rw [Nat.add_sub_assoc hcurrent value,
    Nat.add_sub_assoc hcurrent (value % modulus)]
  simp only [Nat.add_mod, Nat.mod_mod]

private theorem modularReflect_involutive
    (modulus value current : Nat)
    (hmodulus : 0 < modulus) (hcurrent : current < modulus) :
    (value + modulus - ((value + modulus - current) % modulus)) % modulus =
      current := by
  have hcurrentLe : current ≤ modulus := Nat.le_of_lt hcurrent
  rw [modularReflect_reduce modulus value current hcurrentLe]
  let reflected :=
    (value % modulus + modulus - current) % modulus
  have hreflected : reflected < modulus := Nat.mod_lt _ hmodulus
  change (value + modulus - reflected) % modulus = current
  rw [modularReflect_reduce modulus value reflected (Nat.le_of_lt hreflected)]
  exact modularReflect_reduced_involutive modulus (value % modulus) current
    (Nat.mod_lt value hmodulus) hcurrent

/-- Applying the source Boolean reflection twice restores the complete word. -/
theorem constMinusBits_involutive (bits : List Bool) (value : Nat) :
    constMinusBits (constMinusBits bits value) value = bits := by
  apply boolWordToNat_injective_of_length
  · simp
  · rw [boolWordToNat_constMinusBits, boolWordToNat_constMinusBits]
    have hlen : (constMinusBits bits value).length = bits.length := by
      unfold constMinusBits
      rw [cuccaroAddBits_length]
      · simp
      · simp
    rw [hlen]
    have hmodulus := Nat.two_pow_pos bits.length
    have hbits := boolWordToNat_lt_pow_two bits
    exact modularReflect_involutive (2 ^ bits.length)
      value (boolWordToNat bits) hmodulus hbits

end ShorECDLP.Paper2607_13816
