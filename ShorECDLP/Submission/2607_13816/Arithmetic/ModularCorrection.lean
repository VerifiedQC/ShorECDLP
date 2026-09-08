import ShorECDLP.Submission.«2607_13816».Arithmetic.CarryAdd

/-!
# Arithmetic of the quadratic modular correction

`quadratic_modular_arithmetic.py:append_ctrl_add_modp_quadratic` first adds modulo the machine-word radix, XORs the overflow with a
comparison against the modulus, adds the radix-minus-modulus correction, and
clears the flag by comparing the result with the preserved addend. These lemmas
connect those predicates for canonical operands; they are arithmetic facts, not
claims about an implemented circuit. The doubling lemma matches the final
flag cleanup in `append_dbl_modp_quadratic`.
-/
namespace ShorECDLP.Paper2607_13816

/-- The two source reduction predicates are exclusive on canonical operands. -/
private theorem modularCorrection_flag (radix p x y : Nat) (control : Bool)
    (hpr : p < radix) (hx : x < p) (hy : y < p) :
    Bool.xor (decide (radix ≤ y + if control then x else 0))
      (decide (p ≤ (y + if control then x else 0) % radix)) =
      decide (p ≤ y + if control then x else 0) := by
  cases control
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    have hyr : y < radix := lt_trans hy hpr
    simp [Nat.mod_eq_of_lt hyr, Nat.not_le.mpr hyr, Nat.not_le.mpr hy]
  · simp only [↓reduceIte]
    by_cases hr : y + x < radix
    · rw [Nat.mod_eq_of_lt hr]
      simp [Nat.not_le.mpr hr]
    · have hsum : y + x < radix + radix := by omega
      have hm : (y + x) % radix = y + x - radix := by
        have he : y + x = radix + (y + x - radix) := by omega
        rw [he, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (show y + x - radix < radix by omega)]
      rw [hm]
      have hlow : y + x - radix < p := by omega
      simp [show radix ≤ y + x by omega, show p ≤ y + x by omega,
        Nat.not_le.mpr hlow]

/-- Applying the flagged correction yields the canonical controlled modular sum. -/
private theorem modularCorrection_value (radix p x y : Nat) (control : Bool)
    (hpr : p < radix) (hx : x < p) (hy : y < p) :
    (((y + if control then x else 0) % radix) +
      if p ≤ y + if control then x else 0 then radix - p else 0) % radix =
      (y + if control then x else 0) % p := by
  cases control
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    simp [Nat.not_le.mpr hy, Nat.mod_eq_of_lt hy,
      Nat.mod_eq_of_lt (lt_trans hy hpr)]
  · simp only [↓reduceIte]
    by_cases hpSum : y + x < p
    · simp [Nat.not_le.mpr hpSum, Nat.mod_eq_of_lt hpSum,
        Nat.mod_eq_of_lt (lt_trans hpSum hpr)]
    · have hred : y + x - p < p := by omega
      have hmod : (y + x) % p = y + x - p := by
        have he : y + x = p + (y + x - p) := by omega
        rw [he, Nat.add_mod]
        simp [Nat.mod_eq_of_lt hred]
      rw [if_pos (show p ≤ y + x by omega), hmod]
      by_cases hr : y + x < radix
      · rw [Nat.mod_eq_of_lt hr]
        have he : y + x + (radix - p) = radix + (y + x - p) := by omega
        rw [he, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (lt_trans hred hpr)]
      · have hm : (y + x) % radix = y + x - radix := by
          have he : y + x = radix + (y + x - radix) := by omega
          rw [he, Nat.add_mod]
          simp [Nat.mod_eq_of_lt (show y + x - radix < radix by omega)]
        rw [hm]
        have he : y + x - radix + (radix - p) = y + x - p := by omega
        rw [he, Nat.mod_eq_of_lt (lt_trans hred hpr)]

/-- The final comparison erases the reduction flag, including disabled control. -/
private theorem modularCorrection_cleanup (p x y : Nat) (control : Bool)
    (hx : x < p) (hy : y < p) :
    (control && decide ((y + if control then x else 0) % p < x)) =
      decide (p ≤ y + if control then x else 0) := by
  cases control
  · simp [Nat.not_le.mpr hy]
  · simp only [↓reduceIte, Bool.true_and]
    by_cases hsum : y + x < p
    · rw [Nat.mod_eq_of_lt hsum]
      simp [Nat.not_le.mpr hsum, show ¬ y + x < x by omega]
    · have he : y + x = p + (y + x - p) := by omega
      have hred : y + x - p < p := by omega
      have hm : (y + x) % p = y + x - p := by
        rw [he, Nat.add_mod]
        simp [Nat.mod_eq_of_lt hred]
      rw [hm]
      simp [show y + x - p < x by omega, show p ≤ y + x by omega]

/-- All four arithmetic stages of the source controlled modular adder agree:
the overflow/comparison XOR selects one correction, the result is canonical,
and the final controlled comparison clears the flag. -/
theorem modularCorrection_correct (radix p x y : Nat) (control : Bool)
    (hpr : p < radix) (hx : x < p) (hy : y < p) :
    let total := y + if control then x else 0
    let low := total % radix
    let flag := Bool.xor (decide (radix ≤ total)) (decide (p ≤ low))
    let result := (low + if flag then radix - p else 0) % radix
    result = total % p ∧ result < p ∧
      Bool.xor flag (control && decide (result < x)) = false := by
  dsimp only
  rw [modularCorrection_flag radix p x y control hpr hx hy]
  simp only [decide_eq_true_eq]
  rw [modularCorrection_value radix p x y control hpr hx hy]
  refine ⟨rfl, Nat.mod_lt _ (by omega), ?_⟩
  rw [modularCorrection_cleanup p x y control hx hy]
  simp

/-- For an odd modulus, the low bit of the doubled residue is precisely the
reduction flag. This is the final CNOT cleanup in the source doubling routine. -/
theorem modularDoubling_cleanup (p x : Nat) (hodd : p % 2 = 1) (hx : x < p) :
    decide ((2 * x % p) % 2 = 1) = decide (p ≤ 2 * x) := by
  by_cases hsum : 2 * x < p
  · rw [Nat.mod_eq_of_lt hsum]
    simp [Nat.not_le.mpr hsum]
  · have hred : 2 * x - p < p := by omega
    have hm : 2 * x % p = 2 * x - p := by
      have he : 2 * x = p + (2 * x - p) := by omega
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hred]
    rw [hm]
    have hparity : (2 * x - p) % 2 = 1 := by omega
    simp [hparity, show p ≤ 2 * x by omega]

end ShorECDLP.Paper2607_13816
