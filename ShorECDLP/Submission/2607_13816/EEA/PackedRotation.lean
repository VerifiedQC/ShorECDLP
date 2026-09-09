import ShorECDLP.Submission.«2607_13816».EEA.PackedFields

/-! # Numeric cyclic rotation of packed work words -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem rotation_append (xs ys : List Bool) :
    boolWordToNat (xs ++ ys) = boolWordToNat xs + 2^xs.length * boolWordToNat ys := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.cons_append, boolWordToNat_cons, List.length_cons, ih, Nat.pow_succ]
    ring

/-- Left rotation of a little-endian word moves the low field to the high end. -/
theorem boolWordToNat_rotate (bits : List Bool) (count : Nat) (hcount : count ≤ bits.length) :
    boolWordToNat (bits.rotate count) = boolWordToNat bits / 2^count +
      2^(bits.length-count) * (boolWordToNat bits % 2^count) := by
  have hs := rotation_append (bits.take count) (bits.drop count)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hcount] at hs
  have hb := boolWordToNat_lt_pow_two (bits.take count)
  rw [List.length_take, Nat.min_eq_left hcount] at hb
  have ht : boolWordToNat bits % 2^count = boolWordToNat (bits.take count) := by
    rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have hd : boolWordToNat bits / 2^count = boolWordToNat (bits.drop count) := by
    rw [hs, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hb, Nat.zero_add]
  rw [List.rotate_eq_drop_append_take hcount, rotation_append, List.length_drop, ht, hd]

/-- Undoing a normalized cyclic rotation recovers the complete packed word. -/
theorem packedRotation_roundTrip (bits : List Bool) (shift : Nat) :
    (bits.rotate shift).rotate (bits.length - shift % bits.length) = bits := by
  by_cases hn : bits.length = 0
  · have he : bits = [] := List.eq_nil_of_length_eq_zero hn
    simp [he]
  · have hm : shift % bits.length ≤ bits.length := Nat.le_of_lt (Nat.mod_lt _ (by omega))
    rw [← List.rotate_mod bits shift, List.rotate_rotate,
      Nat.add_sub_of_le hm, List.rotate_length]

private theorem rotation_leftOne (bits : List Bool) :
    rotateLeftOne bits = bits.rotate (min 1 bits.length) := by
  cases bits with
  | nil => simp [rotateLeftOne]
  | cons b bits =>
    rw [List.rotate_eq_drop_append_take (by simp)]
    simp [rotateLeftOne]

/-- The actual left-by-one cascade moves the low bit to the high end. -/
theorem controlledRotateLeftOne_numeric
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    boolWordToNat (wireValues register (run (controlledRotateLeftOne control register) state)) =
      if state control then
        boolWordToNat (wireValues register state) / 2^(min 1 register.length) +
          2^(register.length-min 1 register.length) *
            (boolWordToNat (wireValues register state) % 2^(min 1 register.length))
      else boolWordToNat (wireValues register state) := by
  rw [run_controlledRotateLeftOne_values control register state hnd]
  split
  · rw [rotation_leftOne, boolWordToNat_rotate _ _ (Nat.min_le_right _ _)]
    simp only [wireValues, List.length_map]
  · rfl

/-- The optimized actual right-by-two circuit has the corresponding numeric action. -/
theorem controlledRotateRightTwo_numeric
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    boolWordToNat (wireValues register (run (controlledRotateRightTwo control register) state)) =
      if state control then
        boolWordToNat (wireValues register state) / 2^(register.length-2) +
          2^(register.length-(register.length-2)) *
            (boolWordToNat (wireValues register state) % 2^(register.length-2))
      else boolWordToNat (wireValues register state) := by
  rw [run_controlledRotateRightTwo_values control register state hnd]
  split
  · rw [boolWordToNat_rotate _ _ (by simp only [wireValues, List.length_map]; omega)]
    simp only [wireValues, List.length_map]
  · rfl

end ShorECDLP.Paper2607_13816
