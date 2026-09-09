import ShorECDLP.Submission.«2607_13816».EEA.PackedRotation
import ShorECDLP.Submission.«2607_13816».EEA.ShiftCounter

/-! # Preservation of bounded logical shift encodings -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem shiftEncoding_small (width value : Nat) (hw : 0 < width) (hv : value < 2^width) :
    truthMinusOneValue width value = if value = 0 then 2^width-1 else value-1 := by
  have hm : 1 < 2^width := Nat.one_lt_two_pow hw.ne'
  change (value + 2^width - 1 % 2^width) % 2^width = _
  rw [Nat.mod_eq_of_lt hm]
  split
  · subst value
    simp only [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · rename_i hn
    rw [show value + 2^width - 1 = value - 1 + 2^width by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

private theorem shiftEncoding_increment (width value : Nat) (hw : 0 < width)
    (hv : value + 1 < 2^width) :
    (1 + truthMinusOneValue width value) % 2^width = truthMinusOneValue width (value+1) := by
  rw [shiftEncoding_small width value hw (by omega), shiftEncoding_small width (value+1) hw hv]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
  by_cases hz : value = 0
  · subst value
    simp only [↓reduceIte, Nat.zero_add, Nat.sub_self]
    have hp : 0 < 2^width := Nat.pow_pos (by decide)
    rw [show 1 + (2^width-1) = 2^width by omega, Nat.mod_self]
  · rw [if_neg hz, show 1 + (value-1) = value by omega, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem shiftEncoding_decrement (width value : Nat) (hw : 0 < width)
    (hpos : 0 < value) (hv : value < 2^width) :
    (truthMinusOneValue width value + 2^width - 1) % 2^width =
      truthMinusOneValue width (value-1) := by
  rw [shiftEncoding_small width value hw hv, if_neg (by omega),
    shiftEncoding_small width (value-1) hw (by omega)]
  by_cases he : value = 1
  · subst value
    simp only [Nat.sub_self, Nat.zero_add, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by have := Nat.pow_pos (a := 2) (n := width) (by decide); omega)
  · rw [if_neg (by omega), show value-1+2^width-1 = (value-1-1)+2^width by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem shiftEncoding_left (bits : List Bool) (h : 0 < bits.length) :
    rotateLeftOne bits = bits.rotate 1 := by
  cases bits with
  | nil => simp at h
  | cons b bits =>
    rw [List.rotate_eq_drop_append_take (by simp)]
    simp [rotateLeftOne]

private theorem shiftEncoding_work (bits : List Bool) (shift : Nat) (backward : Bool)
    (hn : 0 < bits.length) (hdec : backward = true → 0 < shift) :
    (if backward then (bits.rotate shift).rotate (bits.length-1)
      else rotateLeftOne (bits.rotate shift)) =
      bits.rotate (if backward then shift-1 else shift+1) := by
  cases backward with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [shiftEncoding_left _ (by simpa using hn), List.rotate_rotate]
  | true =>
    simp only [↓reduceIte]
    have hp := hdec rfl
    rw [List.rotate_rotate, show shift + (bits.length-1) = bits.length + (shift-1) by omega,
      ← List.rotate_rotate, List.rotate_length]

private theorem shiftEncoding_counter (width shift : Nat) (backward : Bool)
    (hw : 0 < width) (hs : shift < 2^width)
    (hdec : backward = true → 0 < shift)
    (hinc : backward = false → shift+1 < 2^width) :
    (if backward then (truthMinusOneValue width shift + 2^width-1) % 2^width
      else (1+truthMinusOneValue width shift) % 2^width) =
      truthMinusOneValue width (if backward then shift-1 else shift+1) := by
  cases backward with
  | false => exact shiftEncoding_increment width shift hw (hinc rfl)
  | true => exact shiftEncoding_decrement width shift hw (hdec rfl) hs

/-- An enabled post-shift preserves one bounded logical shift across both the
rotated work bank and its truth-minus-one counter. -/
theorem postShiftUnitary_shiftEncoding (r : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout r) (hready : ShiftReady r state) (henabled : state r.phase1 = true)
    (canonical : List Bool) (shift : Nat)
    (hbank : wireValues r.work state = canonical.rotate shift)
    (hcounter : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hwork : 0 < r.work.length) (hwidth : 0 < r.lengthS.length)
    (hshift : shift < 2^r.lengthS.length)
    (hdec : state r.phase2 = true → 0 < shift)
    (hinc : state r.phase2 = false → shift+1 < 2^r.lengthS.length) :
    let next := if state r.phase2 then shift-1 else shift+1
    wireValues r.work (run (postShiftUnitary r) state) = canonical.rotate next ∧
    boolWordToNat (wireValues r.lengthS (run (postShiftUnitary r) state)) =
      truthMinusOneValue r.lengthS.length next ∧ next < 2^r.lengthS.length := by
  dsimp only
  have hlen : r.work.length = canonical.length := by
    have h := congrArg List.length hbank
    simpa only [wireValues, List.length_map, List.length_rotate] using h
  constructor
  · rw [postShiftUnitary_work_bits r state hlayout hready, henabled]
    simp only [↓reduceIte]
    rw [hbank, hlen]
    exact shiftEncoding_work canonical shift _ (by omega) hdec
  constructor
  · rw [postShiftUnitary_counter r state hlayout hready, henabled]
    simp only [↓reduceIte]
    rw [hcounter]
    exact shiftEncoding_counter _ _ _ hwidth hshift hdec hinc
  · split
    · omega
    · exact hinc (by cases h : state r.phase2 <;> simp_all)

/-- The enabled pre-shift preserves the same paired bank/counter encoding. -/
theorem preShiftUnitary_shiftEncoding (r : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout r) (hready : ShiftReady r state) (henabled : state r.phase1 = false)
    (canonical : List Bool) (shift : Nat)
    (hbank : wireValues r.work state = canonical.rotate shift)
    (hcounter : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hwork : 0 < r.work.length) (hwidth : 0 < r.lengthS.length)
    (hshift : shift < 2^r.lengthS.length)
    (hdec : state r.phase2 = true → 0 < shift)
    (hinc : state r.phase2 = false → shift+1 < 2^r.lengthS.length) :
    let next := if state r.phase2 then shift-1 else shift+1
    wireValues r.work (run (preShiftUnitary r) state) = canonical.rotate next ∧
    boolWordToNat (wireValues r.lengthS (run (preShiftUnitary r) state)) =
      truthMinusOneValue r.lengthS.length next ∧ next < 2^r.lengthS.length := by
  dsimp only
  have hlen : r.work.length = canonical.length := by
    have h := congrArg List.length hbank
    simpa only [wireValues, List.length_map, List.length_rotate] using h
  constructor
  · rw [preShiftUnitary_work_bits r state hlayout hready, henabled]
    simp only [Bool.not_false, ↓reduceIte]
    rw [hbank, hlen]
    exact shiftEncoding_work canonical shift _ (by omega) hdec
  constructor
  · rw [preShiftUnitary_counter r state hlayout hready, henabled]
    simp only [Bool.not_false, ↓reduceIte]
    rw [hcounter]
    exact shiftEncoding_counter _ _ _ hwidth hshift hdec hinc
  · split
    · omega
    · exact hinc (by cases h : state r.phase2 <;> simp_all)

end ShorECDLP.Paper2607_13816
