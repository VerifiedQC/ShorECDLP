import ShorECDLP.Submission.«2607_13816».EEA.WordNat
import ShorECDLP.Submission.«2607_13816».EEA.Shift

/-! # Numeric semantics of the source shift counters -/
namespace ShorECDLP.Paper2607_13816
private theorem counter_decrement_length (b : Bool) (xs : List Bool) : (decrementBits b xs).length = xs.length := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simp [decrementBits, ih]
private theorem counter_increment_decrement (b : Bool) (xs : List Bool) :
    incrementBits b (decrementBits b xs) = xs := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => cases x <;> cases b <;> simp [decrementBits, incrementBits, ih]
private theorem counter_decrement (xs : List Bool) : boolWordToNat (decrementBits true xs) =
    (boolWordToNat xs + 2^xs.length - 1) % 2^xs.length := by
  have hi := boolWordToNat_incrementBits true (decrementBits true xs)
  rw [counter_increment_decrement, counter_decrement_length] at hi
  simp only [Bool.toNat_true] at hi
  have hd := boolWordToNat_lt_pow_two (decrementBits true xs)
  rw [counter_decrement_length] at hd
  have hp : 0 < 2^xs.length := pow_pos (by decide) _
  by_cases hz : 1 + boolWordToNat (decrementBits true xs) = 2^xs.length
  · rw [hz, Nat.mod_self] at hi
    rw [hi, zero_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hi
    have he : boolWordToNat xs + 2^xs.length - 1 =
        boolWordToNat (decrementBits true xs) + 2^xs.length := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hd]

open _root_.ShorECDLP.Classical
noncomputable section

/-- Numeric counter semantics of the actual pre-shift, including modular wrap. -/
theorem preShiftUnitary_counter (r : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout r) (hready : ShiftReady r state) :
    boolWordToNat (wireValues r.lengthS (run (preShiftUnitary r) state)) =
      if !state r.phase1 then
        (if state r.phase2 then
          (boolWordToNat (wireValues r.lengthS state) + 2^r.lengthS.length - 1) % 2^r.lengthS.length
         else (1 + boolWordToNat (wireValues r.lengthS state)) % 2^r.lengthS.length)
      else boolWordToNat (wireValues r.lengthS state) := by
  rw [preShiftUnitary_counter_bits r state hlayout hready]
  split_ifs <;> simp only [counter_decrement, boolWordToNat_incrementBits,
    Bool.toNat_true, wireValues, List.length_map]

/-- Numeric counter semantics of the actual post-shift, including modular wrap. -/
theorem postShiftUnitary_counter (r : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout r) (hready : ShiftReady r state) :
    boolWordToNat (wireValues r.lengthS (run (postShiftUnitary r) state)) =
      if state r.phase1 then
        (if state r.phase2 then
          (boolWordToNat (wireValues r.lengthS state) + 2^r.lengthS.length - 1) % 2^r.lengthS.length
         else (1 + boolWordToNat (wireValues r.lengthS state)) % 2^r.lengthS.length)
      else boolWordToNat (wireValues r.lengthS state) := by
  rw [postShiftUnitary_counter_bits r state hlayout hready]
  split_ifs <;> simp only [counter_decrement, boolWordToNat_incrementBits,
    Bool.toNat_true, wireValues, List.length_map]

end
end ShorECDLP.Paper2607_13816
