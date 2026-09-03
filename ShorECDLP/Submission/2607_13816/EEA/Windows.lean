import Mathlib.Data.Rat.Floor
import ShorECDLP.Submission.«2607_13816».EEA.Bounds

/-!
# Exact active windows for the bit-serial EEA

This file turns Appendix A.2 into exact integer arithmetic.  `eeaWindowSlope` and
`eeaWindowDelta` are conservative rational certificates proved in `EEA.Bounds`; no floating-point
number enters the definitions or containment proofs below.  Windows use the generator's inclusive,
one-based Work-register convention.
-/

namespace ShorECDLP.Paper2607_13816

/-- An inclusive one-based interval of physical Work-register positions. -/
structure ActiveWindow where
  start : ℕ
  stop : ℕ
  deriving DecidableEq, Repr

def ActiveWindow.Contains (window : ActiveWindow) (location : ℕ) : Prop :=
  window.start ≤ location ∧ location ≤ window.stop

def ActiveWindow.Covers (window : ActiveWindow) (left right : ℕ) : Prop :=
  window.start ≤ left ∧ left ≤ right ∧ right ≤ window.stop

/-- Exact ceiling division by a positive natural denominator. -/
def ceilDiv (numerator : ℤ) (denominator : ℕ) : ℤ :=
  -((-numerator) / (denominator : ℤ))

/-- The paper takes the ceiling and then clamps every analytic lower endpoint to at least one. -/
def ceilDivAtLeastOne (numerator : ℤ) (denominator : ℕ) : ℕ :=
  Int.toNat (max 1 (ceilDiv numerator denominator))

-- Clearing the denominators of `c = 2089/1323` and `delta = 727/1000` makes all
-- four lower-window formulas literal integer ceiling divisions.
private def rWindowNumerator (n T : ℕ) : ℤ :=
  1323 * (250 * ((T : ℤ) - n - 1) - 727)

private def swapWindowNumerator (n T : ℕ) : ℤ :=
  1323 * (250 * ((T : ℤ) - 3 * (n + 1)) - 727)

private def lengthTWindowNumerator (n T : ℕ) : ℤ :=
  1323 * (250 * ((T : ℤ) - 4 * (n + 1)) - 727)

private def lengthRPrimeWindowNumerator (T : ℕ) : ℤ :=
  1323 * (250 * (T : ℤ) - 727)

/-! The five rational formulas below reproduce the supplemental generator exactly on the pinned
secp256k1 grid `n = 256`, `1 <= T <= 1620`.  No parametric equality to the generator's
floating-point evaluation is claimed outside that fixed artifact. -/

/-- Exact rational window formula for remainder add/subtract. -/
def remainderWindow (n T : ℕ) : ActiveWindow :=
  ⟨min (ceilDivAtLeastOne (rWindowNumerator n T) 1758250 + 2) (n + 3), n + 3⟩

/-- Exact rational window formula for the quotient/sign swap. -/
def quotientSwapWindow (n T : ℕ) : ActiveWindow :=
  ⟨min (ceilDivAtLeastOne (swapWindowNumerator n T) 1096750 + 1) (n + 2),
    max 1 (min (T / 2 + 2) (n + 2))⟩

/-- Exact rational prefix-window formula for coefficient add/subtract. -/
def coefficientWindow (n T : ℕ) : ActiveWindow :=
  ⟨1, max 1 (min (T / 4 + 2) (n + 1))⟩

/-- Exact rational window formula for the old `l_t` length update. -/
def lengthTWindow (n T : ℕ) : ActiveWindow :=
  ⟨min (ceilDivAtLeastOne (lengthTWindowNumerator n T) 766000) (n + 3),
    max 1 (min (T / 4 + 3) (n + 2))⟩

/-- Exact rational window formula for the updated `l_r'` length update.  The supplemental implementation
keeps its safe upper endpoint at the full Work-register width. -/
def lengthRPrimeWindow (n T : ℕ) : ActiveWindow :=
  ⟨min (ceilDivAtLeastOne (lengthRPrimeWindowNumerator T) 2089000 + 2) (n + 3),
    n + 3⟩

structure EEAWindows where
  remainder : ActiveWindow
  quotientSwap : ActiveWindow
  coefficient : ActiveWindow
  lengthT : ActiveWindow
  lengthRPrime : ActiveWindow
  deriving DecidableEq, Repr

def activeWindows (n T : ℕ) : EEAWindows where
  remainder := remainderWindow n T
  quotientSwap := quotientSwapWindow n T
  coefficient := coefficientWindow n T
  lengthT := lengthTWindow n T
  lengthRPrime := lengthRPrimeWindow n T

/-- Certified remainder window for the concrete gate order.  The supplemental circuit executes
the phase-two remainder add/subtract immediately before incrementing `l_q`, whereas Appendix A.2
derives its lower endpoint from the post-increment length.  Retaining one additional lower lane is
the minimal conservative repair.  The other four rational formulas are unchanged. -/
def certifiedRemainderWindow (n T : ℕ) : ActiveWindow :=
  ⟨min (ceilDivAtLeastOne (rWindowNumerator n T) 1758250 + 1) (n + 3), n + 3⟩

def certifiedActiveWindows (n T : ℕ) : EEAWindows where
  remainder := certifiedRemainderWindow n T
  quotientSwap := quotientSwapWindow n T
  coefficient := coefficientWindow n T
  lengthT := lengthTWindow n T
  lengthRPrime := lengthRPrimeWindow n T

theorem certifiedRemainderWindow_start_le_reference (n T : ℕ) :
    (certifiedRemainderWindow n T).start ≤ (remainderWindow n T).start := by
  simp only [certifiedRemainderWindow, remainderWindow]
  omega

theorem remainderWindow_start_le_certified_add_one (n T : ℕ) :
    (remainderWindow n T).start ≤ (certifiedRemainderWindow n T).start + 1 := by
  simp only [certifiedRemainderWindow, remainderWindow]
  omega

private theorem ceilDiv_eq_ceil (numerator : ℤ) (denominator : ℕ) :
    ceilDiv numerator denominator =
      ⌈((numerator : ℚ) / (denominator : ℚ))⌉ := by
  simpa [ceilDiv] using (Rat.ceil_intCast_div_natCast numerator denominator).symm

private theorem ceilDivAtLeastOne_le {numerator : ℤ} {denominator bound : ℕ}
    (hbound : 1 ≤ bound) (hratio : (numerator : ℚ) / denominator ≤ bound) :
    ceilDivAtLeastOne numerator denominator ≤ bound := by
  rw [ceilDivAtLeastOne, Int.toNat_le]
  apply max_le
  · exact_mod_cast hbound
  · rw [ceilDiv_eq_ceil, Int.ceil_le]
    exact hratio

private theorem rWindow_ratio (n T : ℕ) :
    ((rWindowNumerator n T : ℤ) : ℚ) / 1758250 =
      ((T : ℚ) - n - 1 - 4 * eeaWindowDelta) / (4 * eeaWindowSlope - 1) := by
  norm_num [rWindowNumerator, eeaWindowSlope, eeaWindowDelta]
  ring

private theorem swapWindow_ratio (n T : ℕ) :
    ((swapWindowNumerator n T : ℤ) : ℚ) / 1096750 =
      ((T : ℚ) - 3 * (n + 1) - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 3) := by
  norm_num [swapWindowNumerator, eeaWindowSlope, eeaWindowDelta]
  ring

private theorem lengthTWindow_ratio (n T : ℕ) :
    ((lengthTWindowNumerator n T : ℤ) : ℚ) / 766000 =
      ((T : ℚ) - 4 * (n + 1) - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 4) := by
  norm_num [lengthTWindowNumerator, eeaWindowSlope, eeaWindowDelta]
  ring

private theorem lengthRPrimeWindow_ratio (T : ℕ) :
    ((lengthRPrimeWindowNumerator T : ℤ) : ℚ) / 2089000 =
      ((T : ℚ) - 4 * eeaWindowDelta) / (4 * eeaWindowSlope) := by
  norm_num [lengthRPrimeWindowNumerator, eeaWindowSlope, eeaWindowDelta]
  ring

private theorem remainderWindow_start_le {n T location : ℕ} (hlocation : 3 ≤ location)
    (hcore : ((T : ℚ) - n - 1 - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 1) ≤ location - 2) :
    (remainderWindow n T).start ≤ location := by
  have hceil : ceilDivAtLeastOne (rWindowNumerator n T) 1758250 ≤ location - 2 := by
    apply ceilDivAtLeastOne_le (by omega)
    calc
      ((rWindowNumerator n T : ℤ) : ℚ) / (1758250 : ℕ) =
          ((T : ℚ) - n - 1 - 4 * eeaWindowDelta) /
            (4 * eeaWindowSlope - 1) := by simpa using rWindow_ratio n T
      _ ≤ (location : ℚ) - 2 := hcore
      _ = ((location - 2 : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  simp only [remainderWindow]
  omega

private theorem certifiedRemainderWindow_start_le {n T location : ℕ}
    (hlocation : 2 ≤ location)
    (hcore : ((T : ℚ) - n - 1 - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 1) ≤ location - 1) :
    (certifiedRemainderWindow n T).start ≤ location := by
  have hceil : ceilDivAtLeastOne (rWindowNumerator n T) 1758250 ≤ location - 1 := by
    apply ceilDivAtLeastOne_le (by omega)
    calc
      ((rWindowNumerator n T : ℤ) : ℚ) / (1758250 : ℕ) =
          ((T : ℚ) - n - 1 - 4 * eeaWindowDelta) /
            (4 * eeaWindowSlope - 1) := by simpa using rWindow_ratio n T
      _ ≤ (location : ℚ) - 1 := hcore
      _ = ((location - 1 : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  simp only [certifiedRemainderWindow]
  omega

private theorem quotientSwapWindow_start_le {n T location : ℕ} (hlocation : 2 ≤ location)
    (hcore : ((T : ℚ) - 3 * (n + 1) - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 3) ≤ location - 1) :
    (quotientSwapWindow n T).start ≤ location := by
  have hceil : ceilDivAtLeastOne (swapWindowNumerator n T) 1096750 ≤ location - 1 := by
    apply ceilDivAtLeastOne_le (by omega)
    calc
      ((swapWindowNumerator n T : ℤ) : ℚ) / (1096750 : ℕ) =
          ((T : ℚ) - 3 * (n + 1) - 4 * eeaWindowDelta) /
            (4 * eeaWindowSlope - 3) := by simpa using swapWindow_ratio n T
      _ ≤ (location : ℚ) - 1 := hcore
      _ = ((location - 1 : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  simp only [quotientSwapWindow]
  omega

private theorem lengthTWindow_start_le {n T location : ℕ} (hlocation : 1 ≤ location)
    (hcore : ((T : ℚ) - 4 * (n + 1) - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 4) ≤ location) :
    (lengthTWindow n T).start ≤ location := by
  have hceil : ceilDivAtLeastOne (lengthTWindowNumerator n T) 766000 ≤ location := by
    apply ceilDivAtLeastOne_le hlocation
    calc
      ((lengthTWindowNumerator n T : ℤ) : ℚ) / (766000 : ℕ) =
          ((T : ℚ) - 4 * (n + 1) - 4 * eeaWindowDelta) /
            (4 * eeaWindowSlope - 4) := by simpa using lengthTWindow_ratio n T
      _ ≤ (location : ℚ) := hcore
  simp [lengthTWindow, hceil]

private theorem lengthRPrimeWindow_start_le {n T location : ℕ} (hlocation : 3 ≤ location)
    (hcore : ((T : ℚ) - 4 * eeaWindowDelta) / (4 * eeaWindowSlope) ≤
        location - 2) :
    (lengthRPrimeWindow n T).start ≤ location := by
  have hceil : ceilDivAtLeastOne (lengthRPrimeWindowNumerator T) 2089000 ≤
      location - 2 := by
    apply ceilDivAtLeastOne_le (by omega)
    calc
      ((lengthRPrimeWindowNumerator T : ℤ) : ℚ) / (2089000 : ℕ) =
          ((T : ℚ) - 4 * eeaWindowDelta) / (4 * eeaWindowSlope) := by
        simpa using lengthRPrimeWindow_ratio T
      _ ≤ (location : ℚ) - 2 := hcore
      _ = ((location - 2 : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  simp only [lengthRPrimeWindow]
  omega

/-! ## Exact indexed phase metadata -/

/-- Equation (16): quotient-field length after the indexed microstep. -/
def paperQuotientLength (quotientSize within : ℕ) : ℕ :=
  if within ≤ quotientSize then 0
  else if within ≤ 2 * quotientSize then within - quotientSize
  else if within ≤ 3 * quotientSize then 3 * quotientSize - within
  else 0

/-- Circular shift after the indexed microstep. -/
def paperShiftLength (quotientSize within : ℕ) : ℕ :=
  if within ≤ quotientSize then within
  else if within ≤ 2 * quotientSize then 2 * quotientSize - within
  else if within ≤ 3 * quotientSize then within - 2 * quotientSize
  else 4 * quotientSize - within

/-- The phase in which the indexed microstep executes. -/
def paperMicroPhase (quotientSize within : ℕ) : EEAPhase :=
  if within ≤ quotientSize then .remainder
  else if within ≤ 2 * quotientSize then .quotient
  else if within ≤ 3 * quotientSize then .coefficient
  else .swap

theorem paperQuotientLength_le (quotientSize within : ℕ) :
    paperQuotientLength quotientSize within ≤ quotientSize := by
  simp only [paperQuotientLength]
  split_ifs <;> omega

theorem paperQuotientLength_le_half (quotientSize within : ℕ) :
    2 * paperQuotientLength quotientSize within ≤ within := by
  simp only [paperQuotientLength]
  split_ifs <;> omega

theorem paperShiftLength_le {quotientSize within : ℕ} (hwithin : within ≤ 4 * quotientSize) :
    paperShiftLength quotientSize within ≤ quotientSize := by
  simp only [paperShiftLength]
  split_ifs <;> omega

private theorem size_add_size_le_of_mul_lt_pow {a b n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a * b < 2 ^ n) : a.size + b.size ≤ n + 1 := by
  have haSize : 0 < a.size := Nat.size_pos.mpr ha
  have hbSize : 0 < b.size := Nat.size_pos.mpr hb
  have haPow : 2 ^ (a.size - 1) ≤ a := Nat.lt_size.mp (by omega)
  have hbPow : 2 ^ (b.size - 1) ≤ b := Nat.lt_size.mp (by omega)
  by_contra hsize
  have hexponent : n ≤ (a.size - 1) + (b.size - 1) := by omega
  have hpow : 2 ^ n ≤ 2 ^ ((a.size - 1) + (b.size - 1)) :=
    Nat.pow_le_pow_right (by decide) hexponent
  rw [pow_add] at hpow
  exact (not_lt_of_ge (hpow.trans (Nat.mul_le_mul haPow hbPow))) hab

theorem PaperActiveFrame.quotientSize_add_tSize_le {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n) :
    (paperQuotient frame.boundary).size + frame.boundary.t.size ≤ n + 1 := by
  have hinvariant := frame.reachable.invariant hp hx hxp
  have hrpPos : 0 < frame.boundary.rPrime := Nat.pos_of_ne_zero frame.nonterminal
  have hqPos : 0 < paperQuotient frame.boundary :=
    Nat.div_pos (le_of_lt hinvariant.remainder_decreases) hrpPos
  have htPos : 0 < frame.boundary.t :=
    lt_of_le_of_lt (Nat.zero_le _) hinvariant.coefficient_increases
  obtain ⟨hnextT, _⟩ := paperStep_coefficients frame.nonterminal
  have hproduct : paperQuotient frame.boundary * frame.boundary.t < 2 ^ n := by
    apply lt_of_le_of_lt _ hpN
    calc
      paperQuotient frame.boundary * frame.boundary.t ≤
          frame.boundary.tPrime + paperQuotient frame.boundary * frame.boundary.t :=
        Nat.le_add_left _ _
      _ = (paperStep frame.boundary).t := hnextT.symm
      _ ≤ p := (paperStep_preservesInvariant hinvariant).t_le
  exact size_add_size_le_of_mul_lt_pow hqPos htPos hproduct

theorem PaperActiveFrame.tSize_le_spent_add_one {p x T : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p) :
    frame.boundary.t.size ≤ frame.spent + 1 := by
  apply Nat.size_le.mpr
  have ht := frame.reachable.t_le_pow_spent hp hx hxp
  calc
    frame.boundary.t ≤ 2 ^ frame.spent := ht
    _ < 2 ^ (frame.spent + 1) :=
      Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)

theorem PaperActiveFrame.tSize_le_modulusBits {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n) : frame.boundary.t.size ≤ n := by
  apply Nat.size_le.mpr
  exact (frame.reachable.invariant hp hx hxp).t_le.trans_lt hpN

/-! ## Physical locations inside an active quotient iteration -/

/-- Quotient length visible to the remainder add/subtract.  In phase two the remainder block
precedes insertion of the next quotient bit, so this is one smaller than Equation (16). -/
def remainderQuotientLength (quotientSize within : ℕ) : ℕ :=
  if within ≤ quotientSize then 0 else within - quotientSize - 1

/-- Work2's circular shift after the remainder block's pre-shift. -/
def remainderShiftLength (quotientSize within : ℕ) : ℕ :=
  if within ≤ quotientSize then within else 2 * quotientSize - within

/-- Quotient length at the shared quotient/sign selector: phase two inserts before selecting and
phase three removes after selecting. -/
def swapQuotientLength (quotientSize within : ℕ) : ℕ :=
  if within ≤ 2 * quotientSize then within - quotientSize
  else 3 * quotientSize - within + 1

def PaperActiveFrame.remainderLeft {p x T : ℕ} (frame : PaperActiveFrame p x T) : ℕ :=
  frame.boundary.t.size +
    remainderQuotientLength (paperQuotient frame.boundary).size frame.within + 2

def PaperActiveFrame.remainderRight {p x T n : ℕ} (frame : PaperActiveFrame p x T) : ℕ :=
  n + 3 - remainderShiftLength (paperQuotient frame.boundary).size frame.within

def PaperActiveFrame.swapLocation {p x T : ℕ} (frame : PaperActiveFrame p x T) : ℕ :=
  frame.boundary.t.size +
    swapQuotientLength (paperQuotient frame.boundary).size frame.within + 1

/-- Full prefix endpoint prepared for coefficient arithmetic.  Phase 3 uses `ell_t + 1`;
Phase 4 uses `n + 3 - ell_r' - ell_s`, with the pre-arithmetic shift value inherited from the
preceding microstep. -/
def PaperActiveFrame.coefficientRight {p x T n : ℕ} (frame : PaperActiveFrame p x T) : ℕ :=
  if frame.within ≤ 3 * (paperQuotient frame.boundary).size then
    frame.boundary.t.size + 1
  else
    n + 3 - frame.boundary.rPrime.size -
      (4 * (paperQuotient frame.boundary).size - frame.within + 1)

def PaperActiveFrame.lengthTRight {p x T n : ℕ} (frame : PaperActiveFrame p x T) : ℕ :=
  n + 3 - frame.boundary.rPrime.size

def PaperActiveFrame.lengthRPrimeLeft {p x T : ℕ} (frame : PaperActiveFrame p x T) : ℕ :=
  (paperStep frame.boundary).t.size + 2

theorem PaperActiveFrame.quotientSize_pos {p x T : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p) :
    1 ≤ (paperQuotient frame.boundary).size := by
  have hinvariant := frame.reachable.invariant hp hx hxp
  have hrpPos : 0 < frame.boundary.rPrime := Nat.pos_of_ne_zero frame.nonterminal
  apply Nat.size_pos.mpr
  exact Nat.div_pos (le_of_lt hinvariant.remainder_decreases) hrpPos

theorem PaperActiveFrame.tSize_pos {p x T : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p) :
    1 ≤ frame.boundary.t.size := by
  apply Nat.size_pos.mpr
  exact lt_of_le_of_lt (Nat.zero_le _)
    (frame.reachable.invariant hp hx hxp).coefficient_increases

theorem remainderQuotientLength_add_shift_le {quotientSize within : ℕ}
    (hactive : within ≤ 2 * quotientSize) :
    remainderQuotientLength quotientSize within +
        remainderShiftLength quotientSize within ≤ quotientSize := by
  simp only [remainderQuotientLength, remainderShiftLength]
  split_ifs <;> omega

theorem paperQuotientLength_le_remainderQuotientLength_add_one
    {quotientSize within : ℕ} (hactive : within ≤ 2 * quotientSize) :
    paperQuotientLength quotientSize within ≤
      remainderQuotientLength quotientSize within + 1 := by
  simp only [paperQuotientLength, remainderQuotientLength]
  split_ifs <;> omega

private theorem remainderWindow_core {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n)
    (hactive : frame.within ≤ 2 * (paperQuotient frame.boundary).size) :
    ((T : ℚ) - n - 1 - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 1) ≤
      frame.boundary.t.size +
        paperQuotientLength (paperQuotient frame.boundary).size frame.within := by
  have hprefix := frame.reachable.spent_lt_size hp hx hxp
  have hsizes := frame.quotientSize_add_tSize_le hp hx hxp hpN
  have htime : (T : ℚ) = 4 * frame.spent + frame.within := by
    exact_mod_cast frame.time_eq
  have hsizesQ :
      ((paperQuotient frame.boundary).size : ℚ) + frame.boundary.t.size ≤ n + 1 := by
    exact_mod_cast hsizes
  rw [div_le_iff₀ (by norm_num [eeaWindowSlope] : (0 : ℚ) < 4 * eeaWindowSlope - 1)]
  simp only [paperQuotientLength]
  split_ifs with hfirst
  · have hwithinQ : (frame.within : ℚ) ≤
        (paperQuotient frame.boundary).size := by exact_mod_cast hfirst
    have hspent4 : (4 : ℚ) * frame.spent <
        4 * eeaWindowSlope * frame.boundary.t.size + 4 * eeaWindowDelta := by
      linarith
    have hbudget : (frame.within : ℚ) + frame.boundary.t.size ≤ n + 1 := by
      linarith
    simp only [Nat.cast_zero, add_zero]
    linarith
  · have hwithinQ : (frame.within : ℚ) ≤
        2 * (paperQuotient frame.boundary).size := by exact_mod_cast hactive
    have hsizeWithin : (paperQuotient frame.boundary).size ≤ frame.within := by omega
    have hsizeWithinQ : ((paperQuotient frame.boundary).size : ℚ) ≤ frame.within := by
      exact_mod_cast hsizeWithin
    rw [Nat.cast_sub hsizeWithin]
    have hspent4 : (4 : ℚ) * frame.spent <
        4 * eeaWindowSlope * frame.boundary.t.size + 4 * eeaWindowDelta := by
      linarith
    have hcoefficient : (1 : ℚ) ≤ 4 * eeaWindowSlope - 1 := by
      norm_num [eeaWindowSlope]
    have hbudget :
        4 * eeaWindowSlope * frame.boundary.t.size + frame.within ≤
          (4 * eeaWindowSlope - 1) *
              (frame.boundary.t.size +
                (frame.within - (paperQuotient frame.boundary).size)) + n + 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hcoefficient
        (sub_nonneg.mpr hsizeWithinQ)]
    linarith

/-- Every physical lane used by an active remainder add/subtract is inside the certified window.
The one-lane widening from the reference window is needed exactly because this block precedes the
phase-two `l_q` increment. -/
theorem PaperActiveFrame.certifiedRemainderWindow_covers {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n)
    (hactive : frame.within ≤ 2 * (paperQuotient frame.boundary).size) :
    (certifiedRemainderWindow n T).Covers frame.remainderLeft
      (frame.remainderRight (n := n)) := by
  have htPos := frame.tSize_pos hp hx hxp
  have hsizes := frame.quotientSize_add_tSize_le hp hx hxp hpN
  have hlengthShift := remainderQuotientLength_add_shift_le hactive
  have hpostPre := paperQuotientLength_le_remainderQuotientLength_add_one hactive
  have hcore := remainderWindow_core frame hp hx hxp hpN hactive
  have hstartCore :
      ((T : ℚ) - n - 1 - 4 * eeaWindowDelta) /
          (4 * eeaWindowSlope - 1) ≤ (frame.remainderLeft : ℚ) - 1 := by
    have hpostPreQ :
        (paperQuotientLength (paperQuotient frame.boundary).size frame.within : ℚ) ≤
          remainderQuotientLength (paperQuotient frame.boundary).size frame.within + 1 := by
      exact_mod_cast hpostPre
    simp only [PaperActiveFrame.remainderLeft, Nat.cast_add]
    push_cast
    linarith
  constructor
  · apply certifiedRemainderWindow_start_le (by
      simp [PaperActiveFrame.remainderLeft])
    exact hstartCore
  constructor
  · simp only [PaperActiveFrame.remainderLeft, PaperActiveFrame.remainderRight]
    omega
  · simp [PaperActiveFrame.remainderRight, certifiedRemainderWindow]

theorem swapQuotientLength_pos {quotientSize within : ℕ}
    (hstart : quotientSize < within) :
    1 ≤ swapQuotientLength quotientSize within := by
  simp only [swapQuotientLength]
  split_ifs <;> omega

theorem swapQuotientLength_le {quotientSize within : ℕ}
    (hstart : quotientSize < within) (hstop : within ≤ 3 * quotientSize) :
    swapQuotientLength quotientSize within ≤ quotientSize := by
  simp only [swapQuotientLength]
  split_ifs <;> omega

theorem swapQuotientLength_twice_le {quotientSize within : ℕ}
    (hstart : quotientSize < within) (hstop : within ≤ 3 * quotientSize) :
    2 * swapQuotientLength quotientSize within ≤ within := by
  simp only [swapQuotientLength]
  split_ifs <;> omega

private theorem quotientSwapWindow_core {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n)
    (hstop : frame.within ≤ 3 * (paperQuotient frame.boundary).size) :
    ((T : ℚ) - 3 * (n + 1) - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 3) ≤
      frame.boundary.t.size +
        swapQuotientLength (paperQuotient frame.boundary).size frame.within := by
  have hprefix := frame.reachable.spent_lt_size hp hx hxp
  have hsizes := frame.quotientSize_add_tSize_le hp hx hxp hpN
  have htime : (T : ℚ) = 4 * frame.spent + frame.within := by
    exact_mod_cast frame.time_eq
  have hsizesQ :
      ((paperQuotient frame.boundary).size : ℚ) + frame.boundary.t.size ≤ n + 1 := by
    exact_mod_cast hsizes
  have hwithinQ : (frame.within : ℚ) ≤
      3 * (paperQuotient frame.boundary).size := by exact_mod_cast hstop
  have hlengthNonneg : (0 : ℚ) ≤
      swapQuotientLength (paperQuotient frame.boundary).size frame.within := by positivity
  rw [div_le_iff₀ (by norm_num [eeaWindowSlope] : (0 : ℚ) < 4 * eeaWindowSlope - 3)]
  norm_num [eeaWindowSlope] at *
  nlinarith

/-- Every active quotient/sign selector is inside the exact static swap window. -/
theorem PaperActiveFrame.quotientSwapWindow_contains {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n) (hstart : (paperQuotient frame.boundary).size < frame.within)
    (hstop : frame.within ≤ 3 * (paperQuotient frame.boundary).size) :
    (quotientSwapWindow n T).Contains frame.swapLocation := by
  have hqPos := frame.quotientSize_pos hp hx hxp
  have htPos := frame.tSize_pos hp hx hxp
  have hqLengthPos := swapQuotientLength_pos hstart
  have hqLengthLe := swapQuotientLength_le hstart hstop
  have hqLengthTwice := swapQuotientLength_twice_le hstart hstop
  have hsizes := frame.quotientSize_add_tSize_le hp hx hxp hpN
  have htSpent := frame.tSize_le_spent_add_one hp hx hxp
  have hhalfRaw := congrArg (fun value : ℕ => value / 2) frame.time_eq
  have hhalf : T / 2 = 2 * frame.spent + frame.within / 2 := by
    calc
      T / 2 = (4 * frame.spent + frame.within) / 2 := by simpa only using hhalfRaw
      _ = 2 * frame.spent + frame.within / 2 := by
        simpa [show 4 * frame.spent = 2 * (2 * frame.spent) by omega] using
          Nat.mul_add_div (m := 2) (by norm_num) (2 * frame.spent) frame.within
  have hcore := quotientSwapWindow_core frame hp hx hxp hpN hstop
  constructor
  · apply quotientSwapWindow_start_le (by simp [PaperActiveFrame.swapLocation]; omega)
    simpa [PaperActiveFrame.swapLocation, Nat.cast_add] using hcore
  · simp only [PaperActiveFrame.swapLocation, quotientSwapWindow]
    apply le_trans _ (le_max_right 1 _)
    apply le_min
    · omega
    · omega

private theorem PaperActiveFrame.rPrimeSize_add_tSize_le {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n) :
    frame.boundary.rPrime.size + frame.boundary.t.size ≤ n + 1 := by
  have hinvariant := frame.reachable.invariant hp hx hxp
  have hrpPos : 0 < frame.boundary.rPrime := Nat.pos_of_ne_zero frame.nonterminal
  have htPos : 0 < frame.boundary.t :=
    lt_of_le_of_lt (Nat.zero_le _) hinvariant.coefficient_increases
  apply size_add_size_le_of_mul_lt_pow hrpPos htPos
  calc
    frame.boundary.rPrime * frame.boundary.t <
        frame.boundary.r * frame.boundary.t :=
      Nat.mul_lt_mul_of_pos_right hinvariant.remainder_decreases htPos
    _ ≤ frame.boundary.r * frame.boundary.t +
        frame.boundary.rPrime * frame.boundary.tPrime := Nat.le_add_right _ _
    _ = p := hinvariant.magnitude_identity
    _ < 2 ^ n := hpN

private theorem PaperActiveFrame.modulusBits_le_spent_add_quotientSize_add_rPrimeSize
    {p x T n : ℕ} (frame : PaperActiveFrame p x T)
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpLower : 2 ^ (n - 1) < p) :
    n ≤ frame.spent + (paperQuotient frame.boundary).size +
      frame.boundary.rPrime.size := by
  have hinvariant := frame.reachable.invariant hp hx hxp
  have hrpPos : 0 < frame.boundary.rPrime := Nat.pos_of_ne_zero frame.nonterminal
  have hqPos : 0 < paperQuotient frame.boundary :=
    Nat.div_pos (le_of_lt hinvariant.remainder_decreases) hrpPos
  have hremLt : paperRemainder frame.boundary < frame.boundary.rPrime :=
    Nat.mod_lt _ hrpPos
  have hdecomp :
      paperQuotient frame.boundary * frame.boundary.rPrime +
          paperRemainder frame.boundary = frame.boundary.r := by
    simpa [paperQuotient, paperRemainder, Nat.mul_comm] using
      Nat.div_add_mod frame.boundary.r frame.boundary.rPrime
  have hqSucc : paperQuotient frame.boundary + 1 ≤
      2 ^ (paperQuotient frame.boundary).size := by
    have := Nat.lt_size_self (paperQuotient frame.boundary)
    omega
  have hrBound : frame.boundary.r <
      2 ^ (paperQuotient frame.boundary).size * frame.boundary.rPrime := by
    calc
      frame.boundary.r = paperQuotient frame.boundary * frame.boundary.rPrime +
          paperRemainder frame.boundary := hdecomp.symm
      _ < paperQuotient frame.boundary * frame.boundary.rPrime +
          frame.boundary.rPrime := Nat.add_lt_add_left hremLt _
      _ = (paperQuotient frame.boundary + 1) * frame.boundary.rPrime := by ring
      _ ≤ 2 ^ (paperQuotient frame.boundary).size * frame.boundary.rPrime :=
        Nat.mul_le_mul_right _ hqSucc
  have hmodulus := frame.reachable.modulus_le_pow_spent_mul_r hp hx hxp
  have hrpSize : frame.boundary.rPrime < 2 ^ frame.boundary.rPrime.size :=
    Nat.lt_size_self _
  have hpUpper : p <
      2 ^ (frame.spent + (paperQuotient frame.boundary).size +
        frame.boundary.rPrime.size) := by
    calc
      p ≤ 2 ^ frame.spent * frame.boundary.r := hmodulus
      _ < 2 ^ frame.spent *
          (2 ^ (paperQuotient frame.boundary).size * frame.boundary.rPrime) :=
        Nat.mul_lt_mul_of_pos_left hrBound (by positivity)
      _ < 2 ^ frame.spent *
          (2 ^ (paperQuotient frame.boundary).size *
            2 ^ frame.boundary.rPrime.size) := by
        gcongr
      _ = 2 ^ (frame.spent + (paperQuotient frame.boundary).size +
          frame.boundary.rPrime.size) := by rw [pow_add, pow_add]; ring
  have hpowers : 2 ^ (n - 1) <
      2 ^ (frame.spent + (paperQuotient frame.boundary).size +
        frame.boundary.rPrime.size) := hpLower.trans hpUpper
  have hexponents := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpowers
  omega

/-- Every active coefficient add/subtract prefix is inside its exact static window, including the
phase-4 endpoint selected from `n + 3 - ell_r' - ell_s`. -/
theorem PaperActiveFrame.coefficientWindow_covers {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpLower : 2 ^ (n - 1) < p) (hpN : p < 2 ^ n) :
    (coefficientWindow n T).Covers 1 (frame.coefficientRight (n := n)) := by
  have hinvariant := frame.reachable.invariant hp hx hxp
  have hqPos := frame.quotientSize_pos hp hx hxp
  have hrpPos : 1 ≤ frame.boundary.rPrime.size :=
    Nat.size_pos.mpr (Nat.pos_of_ne_zero frame.nonterminal)
  have htPos := frame.tSize_pos hp hx hxp
  have htN := frame.tSize_le_modulusBits hp hx hxp hpN
  have htSpent := frame.tSize_le_spent_add_one hp hx hxp
  have hqRp : (paperQuotient frame.boundary).size + frame.boundary.rPrime.size ≤ n + 1 := by
    apply size_add_size_le_of_mul_lt_pow (Nat.size_pos.mp hqPos)
      (Nat.size_pos.mp hrpPos)
    calc
      paperQuotient frame.boundary * frame.boundary.rPrime ≤ frame.boundary.r := by
        simpa [paperQuotient] using Nat.div_mul_le_self frame.boundary.r frame.boundary.rPrime
      _ ≤ p := hinvariant.r_le
      _ < 2 ^ n := hpN
  have hbits := frame.modulusBits_le_spent_add_quotientSize_add_rPrimeSize
    hp hx hxp hpLower
  have hquarterRaw := congrArg (fun value : ℕ => value / 4) frame.time_eq
  have hquarter : T / 4 = frame.spent + frame.within / 4 := by
    calc
      T / 4 = (4 * frame.spent + frame.within) / 4 := by simpa only using hquarterRaw
      _ = frame.spent + frame.within / 4 := by
        simpa using Nat.mul_add_div (m := 4) (by norm_num) frame.spent frame.within
  simp only [ActiveWindow.Covers, coefficientWindow, PaperActiveFrame.coefficientRight]
  split_ifs with hphaseThree
  · constructor
    · simp
    constructor
    · omega
    · apply le_trans _ (le_max_right 1 _)
      apply le_min <;> omega
  · have hphaseFour : 3 * (paperQuotient frame.boundary).size < frame.within := by omega
    have hshiftPos : 1 ≤
        4 * (paperQuotient frame.boundary).size - frame.within + 1 := by omega
    have hshiftLe :
        4 * (paperQuotient frame.boundary).size - frame.within + 1 ≤
          (paperQuotient frame.boundary).size := by omega
    constructor
    · simp
    constructor
    · omega
    · apply le_trans _ (le_max_right 1 _)
      apply le_min <;> omega

private theorem lengthTWindow_core {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n)
    (hend : frame.within = 4 * (paperQuotient frame.boundary).size) :
    ((T : ℚ) - 4 * (n + 1) - 4 * eeaWindowDelta) /
        (4 * eeaWindowSlope - 4) ≤ frame.boundary.t.size := by
  have hprefix := frame.reachable.spent_lt_size hp hx hxp
  have hsizes := frame.quotientSize_add_tSize_le hp hx hxp hpN
  have htime : (T : ℚ) = 4 * frame.spent + frame.within := by
    exact_mod_cast frame.time_eq
  have hendQ : (frame.within : ℚ) =
      4 * (paperQuotient frame.boundary).size := by exact_mod_cast hend
  have hsizesQ :
      ((paperQuotient frame.boundary).size : ℚ) + frame.boundary.t.size ≤ n + 1 := by
    exact_mod_cast hsizes
  rw [div_le_iff₀ (by norm_num [eeaWindowSlope] : (0 : ℚ) < 4 * eeaWindowSlope - 4)]
  norm_num [eeaWindowSlope] at *
  nlinarith

/-- At an iteration endpoint, every bit position inspected by the old/new `l_t` update lies in
the exact static length window. -/
theorem PaperActiveFrame.lengthTWindow_covers {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpLower : 2 ^ (n - 1) < p) (hpN : p < 2 ^ n)
    (hend : frame.within = 4 * (paperQuotient frame.boundary).size) :
    (lengthTWindow n T).Covers frame.boundary.t.size (frame.lengthTRight (n := n)) := by
  have htPos := frame.tSize_pos hp hx hxp
  have hrpPos : 1 ≤ frame.boundary.rPrime.size :=
    Nat.size_pos.mpr (Nat.pos_of_ne_zero frame.nonterminal)
  have hpair := frame.rPrimeSize_add_tSize_le hp hx hxp hpN
  have hbits := frame.modulusBits_le_spent_add_quotientSize_add_rPrimeSize
    hp hx hxp hpLower
  have hcore := lengthTWindow_core frame hp hx hxp hpN hend
  have hquarterRaw := congrArg (fun value : ℕ => value / 4) frame.time_eq
  have hquarter : T / 4 =
      frame.spent + (paperQuotient frame.boundary).size := by
    calc
      T / 4 = (4 * frame.spent + frame.within) / 4 := by simpa only using hquarterRaw
      _ = (4 * frame.spent + 4 * (paperQuotient frame.boundary).size) / 4 := by
        rw [hend]
      _ = frame.spent + (paperQuotient frame.boundary).size := by
        omega
  simp only [ActiveWindow.Covers, PaperActiveFrame.lengthTRight]
  constructor
  · apply lengthTWindow_start_le htPos
    exact hcore
  constructor
  · omega
  · simp only [lengthTWindow]
    apply le_trans _ (le_max_right 1 _)
    apply le_min <;> omega

private theorem lengthRPrimeWindow_core {p x T : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hend : frame.within = 4 * (paperQuotient frame.boundary).size) :
    ((T : ℚ) - 4 * eeaWindowDelta) / (4 * eeaWindowSlope) ≤
      (paperStep frame.boundary).t.size := by
  have hnext := frame.reachable.step frame.nonterminal
  have hprefix := hnext.spent_lt_size hp hx hxp
  have htime : (T : ℚ) = 4 * frame.spent + frame.within := by
    exact_mod_cast frame.time_eq
  have hendQ : (frame.within : ℚ) =
      4 * (paperQuotient frame.boundary).size := by exact_mod_cast hend
  rw [div_le_iff₀ (by norm_num [eeaWindowSlope] : (0 : ℚ) < 4 * eeaWindowSlope)]
  norm_num [eeaWindowSlope] at *
  nlinarith

/-- At an iteration endpoint, every bit position inspected by the updated `l_r'` decoder lies in
the exact static length window. -/
theorem PaperActiveFrame.lengthRPrimeWindow_covers {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpN : p < 2 ^ n)
    (hend : frame.within = 4 * (paperQuotient frame.boundary).size) :
    (lengthRPrimeWindow n T).Covers frame.lengthRPrimeLeft (n + 3) := by
  have hnextInvariant := paperStep_preservesInvariant (frame.reachable.invariant hp hx hxp)
  have hnextSize : (paperStep frame.boundary).t.size ≤ n := by
    apply Nat.size_le.mpr
    exact hnextInvariant.t_le.trans_lt hpN
  have hnextPos : 1 ≤ (paperStep frame.boundary).t.size := by
    apply Nat.size_pos.mpr
    exact lt_of_le_of_lt (Nat.zero_le _) hnextInvariant.coefficient_increases
  have hcore := lengthRPrimeWindow_core frame hp hx hxp hend
  simp only [ActiveWindow.Covers, PaperActiveFrame.lengthRPrimeLeft]
  constructor
  · apply lengthRPrimeWindow_start_le (by omega)
    simpa [Nat.cast_add] using hcore
  constructor
  · omega
  · simp [lengthRPrimeWindow]

/-- The complete pruning certificate for one indexed active microstep.  Each implication mirrors
the corresponding phase control in the concrete schedule; inactive blocks impose no data-lane
obligation. -/
structure PaperActiveWindowCertificate {p x T : ℕ} (n : ℕ)
    (frame : PaperActiveFrame p x T) : Prop where
  remainder : frame.within ≤ 2 * (paperQuotient frame.boundary).size →
    (certifiedRemainderWindow n T).Covers frame.remainderLeft
      (frame.remainderRight (n := n))
  quotientSwap : (paperQuotient frame.boundary).size < frame.within →
    frame.within ≤ 3 * (paperQuotient frame.boundary).size →
    (quotientSwapWindow n T).Contains frame.swapLocation
  coefficient : 2 * (paperQuotient frame.boundary).size < frame.within →
    (coefficientWindow n T).Covers 1 (frame.coefficientRight (n := n))
  lengthT : frame.within = 4 * (paperQuotient frame.boundary).size →
    (lengthTWindow n T).Covers frame.boundary.t.size (frame.lengthTRight (n := n))
  lengthRPrime : frame.within = 4 * (paperQuotient frame.boundary).size →
    (lengthRPrimeWindow n T).Covers frame.lengthRPrimeLeft (n + 3)

theorem PaperActiveFrame.windowCertificate {p x T n : ℕ}
    (frame : PaperActiveFrame p x T) (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hpLower : 2 ^ (n - 1) < p) (hpN : p < 2 ^ n) :
    PaperActiveWindowCertificate n frame where
  remainder hactive := frame.certifiedRemainderWindow_covers hp hx hxp hpN hactive
  quotientSwap hstart hstop :=
    frame.quotientSwapWindow_contains hp hx hxp hpN hstart hstop
  coefficient _ := frame.coefficientWindow_covers hp hx hxp hpLower hpN
  lengthT hend := frame.lengthTWindow_covers hp hx hxp hpLower hpN hend
  lengthRPrime hend := frame.lengthRPrimeWindow_covers hp hx hxp hpN hend

/-- Every active secp256k1 schedule index carries all five static-window certificates. -/
theorem secp256k1_activeWindowCertificate_of_le {x T : ℕ}
    (hx : 1 ≤ x) (hxp : x < ShorECDLP.p) (hTPos : 1 ≤ T)
    (hTLe : T ≤ paperMicrosteps (paperInitial ShorECDLP.p x)) :
    Nonempty { frame : PaperActiveFrame ShorECDLP.p x T //
      PaperActiveWindowCertificate 256 frame } := by
  obtain ⟨frame⟩ := paperActiveFrame_of_le ShorECDLP.Secp256k1.p_prime hx hxp hTPos hTLe
  refine ⟨⟨frame, frame.windowCertificate ShorECDLP.Secp256k1.p_prime hx hxp ?_ ?_⟩⟩
  · norm_num [ShorECDLP.p]
  · norm_num [ShorECDLP.p]

/-! ## Physical representability of the four noncanonical phase frames -/

private theorem size_add_size_le_of_mul_le_size {a b p : ℕ}
    (ha : a ≤ p) (hb : b ≤ p) (hab : a * b ≤ p) :
    a.size + b.size ≤ p.size + 1 := by
  by_cases ha0 : a = 0
  · subst a
    have hsize := Nat.size_le_size hb
    simpa only [Nat.size_zero, Nat.zero_add] using
      le_trans hsize (Nat.le_add_right _ _)
  by_cases hb0 : b = 0
  · subst b
    have hsize := Nat.size_le_size ha
    simpa only [Nat.size_zero, Nat.add_zero] using
      le_trans hsize (Nat.le_add_right _ _)
  have haSizePos : 0 < a.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero ha0)
  have hbSizePos : 0 < b.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hb0)
  have haPow : 2 ^ (a.size - 1) ≤ a := Nat.lt_size.mp (by omega)
  have hbPow : 2 ^ (b.size - 1) ≤ b := Nat.lt_size.mp (by omega)
  by_contra hsize
  have hexponent : p.size ≤ (a.size - 1) + (b.size - 1) := by omega
  have hpow : 2 ^ p.size ≤ 2 ^ ((a.size - 1) + (b.size - 1)) :=
    Nat.pow_le_pow_right (by decide) hexponent
  rw [pow_add] at hpow
  have htooLarge : 2 ^ p.size ≤ p :=
    (hpow.trans (Nat.mul_le_mul haPow hbPow)).trans hab
  exact (Nat.not_lt_of_ge htooLarge) (Nat.lt_size_self p)

private theorem size_add_size_add_size_le_of_mul_lt_pow {a b c n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c < 2 ^ n) :
    a.size + b.size + c.size ≤ n + 2 := by
  have haSizePos : 0 < a.size := Nat.size_pos.mpr ha
  have hbSizePos : 0 < b.size := Nat.size_pos.mpr hb
  have hcSizePos : 0 < c.size := Nat.size_pos.mpr hc
  have haPow : 2 ^ (a.size - 1) ≤ a := Nat.lt_size.mp (by omega)
  have hbPow : 2 ^ (b.size - 1) ≤ b := Nat.lt_size.mp (by omega)
  have hcPow : 2 ^ (c.size - 1) ≤ c := Nat.lt_size.mp (by omega)
  by_contra hsize
  have hexponent : n ≤ (a.size - 1) + (b.size - 1) + (c.size - 1) := by omega
  have hpow : 2 ^ n ≤
      2 ^ ((a.size - 1) + (b.size - 1) + (c.size - 1)) :=
    Nat.pow_le_pow_right (by decide) hexponent
  rw [pow_add, pow_add] at hpow
  have hproduct :
      2 ^ (a.size - 1) * 2 ^ (b.size - 1) * 2 ^ (c.size - 1) ≤ a * b * c :=
    Nat.mul_le_mul (Nat.mul_le_mul haPow hbPow) hcPow
  exact (not_lt_of_ge (hpow.trans hproduct)) habc

private theorem packedFields_of_capacity {p : ℕ} {s : EEAState}
    (hlt : s.lT = s.t.size) (hlq : s.lQ = s.q.size)
    (hlrp : s.lRPrime = s.rPrime.size)
    (hwork1 : s.t.size + s.q.size + s.r.size ≤ p.size + 2)
    (hwork2 : s.tPrime.size + s.rPrime.size ≤ p.size + 3) :
    (packedView p s).FieldsNonoverlap := by
  simp only [packedView, PackedView.FieldsNonoverlap, BitSpan.Carries, BitSpan.Disjoint,
    EEAState.work1, EEAState.work2]
  rw [hlt, hlq, hlrp]
  have hwidth : 0 < p.size + 3 := by omega
  have hshiftBound : s.shift % (p.size + 3) < p.size + 3 := Nat.mod_lt _ hwidth
  constructor
  · exact hshiftBound
  constructor
  · trivial
  omega

/-- Every frame of the paper's four-phase quotient trace—not just its canonical endpoints—has
actual values that fit the two `(p.size+3)`-bit packed work registers.  In particular, the full
quotient and remainder coexist in Work1 and the updated coefficient and old remainder coexist in
the circularly shifted Work2 frame. -/
theorem paperPhaseTrace_fieldsNonoverlap {p x : ℕ} {s frame : EEAState}
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hreach : ∃ spent, PaperBoundaryReachable p x spent s)
    (hnonterminal : s.rPrime ≠ 0) (hframe : frame ∈ paperPhaseTrace s) :
    (packedView p frame).FieldsNonoverlap := by
  obtain ⟨spent, hreach⟩ := hreach
  have hinvariant := hreach.invariant hp hx hxp
  have hrpPos : 0 < s.rPrime := Nat.pos_of_ne_zero hnonterminal
  have htPos : 0 < s.t :=
    lt_of_le_of_lt (Nat.zero_le _) hinvariant.coefficient_increases
  have hqPos : 0 < paperQuotient s :=
    Nat.div_pos (le_of_lt hinvariant.remainder_decreases) hrpPos
  have hqMul : paperQuotient s * s.rPrime ≤ s.r := by
    simpa [paperQuotient] using Nat.div_mul_le_self s.r s.rPrime
  have hrt : s.r * s.t ≤ p := by
    rw [← hinvariant.magnitude_identity]
    exact Nat.le_add_right _ _
  have htriple :
      (paperQuotient s).size + s.rPrime.size + s.t.size ≤ p.size + 2 := by
    apply size_add_size_add_size_le_of_mul_lt_pow hqPos hrpPos htPos
    calc
      paperQuotient s * s.rPrime * s.t ≤ s.r * s.t :=
        Nat.mul_le_mul_right _ hqMul
      _ ≤ p := hrt
      _ < 2 ^ p.size := Nat.lt_size_self _
  have hremSize : (paperRemainder s).size ≤ s.rPrime.size := by
    apply Nat.size_le_size
    exact (Nat.mod_lt _ hrpPos).le
  have hwork1 :
      s.t.size + (paperQuotient s).size + (paperRemainder s).size ≤ p.size + 2 := by
    omega
  have hwork2Old : s.tPrime.size + s.rPrime.size ≤ p.size + 1 := by
    apply size_add_size_le_of_mul_le_size hinvariant.tPrime_le hinvariant.rPrime_le
    calc
      s.tPrime * s.rPrime = s.rPrime * s.tPrime := by ring
      _ ≤ p := by
        rw [← hinvariant.magnitude_identity]
        exact Nat.le_add_left _ _
  have hnextProduct : s.rPrime * (s.tPrime + paperQuotient s * s.t) ≤ p := by
    calc
      s.rPrime * (s.tPrime + paperQuotient s * s.t) =
          s.rPrime * s.tPrime + (paperQuotient s * s.rPrime) * s.t := by ring
      _ ≤ s.rPrime * s.tPrime + s.r * s.t :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hqMul) _
      _ = p := by rw [add_comm, hinvariant.magnitude_identity]
  have hnextTLe : s.tPrime + paperQuotient s * s.t ≤ p := by
    obtain ⟨ht, _⟩ := paperStep_coefficients hnonterminal
    rw [← ht]
    exact (paperStep_preservesInvariant hinvariant).t_le
  have hwork2New :
      (s.tPrime + paperQuotient s * s.t).size + s.rPrime.size ≤ p.size + 1 := by
    apply size_add_size_le_of_mul_le_size hnextTLe hinvariant.rPrime_le
    simpa [Nat.mul_comm] using hnextProduct
  rw [paperPhaseTrace_nonterminal hnonterminal] at hframe
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hframe
  rcases hframe with rfl | rfl | rfl | rfl
  · exact packedFields_nonoverlap hinvariant
  · apply packedFields_of_capacity
    · exact hinvariant.canonical.2.2.2.2.2.1
    · rfl
    · exact hinvariant.canonical.2.2.2.2.2.2
    · exact hwork1
    · have : s.tPrime.size + s.rPrime.size ≤ p.size + 3 := by omega
      simpa using this
  · apply packedFields_of_capacity
    · exact hinvariant.canonical.2.2.2.2.2.1
    · rfl
    · exact hinvariant.canonical.2.2.2.2.2.2
    · exact hwork1
    · have : (s.tPrime + paperQuotient s * s.t).size + s.rPrime.size ≤
          p.size + 3 := by omega
      simpa using this
  · have hnextInvariant := paperStep_preservesInvariant hinvariant
    simpa [packedView, EEAState.work1, EEAState.work2] using
      packedFields_nonoverlap hnextInvariant

/-! ## Pinned secp256k1 rows -/

example : activeWindows 256 1 =
    ⟨⟨3, 259⟩, ⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 3⟩, ⟨3, 259⟩⟩ := by
  norm_num [activeWindows, remainderWindow, quotientSwapWindow, coefficientWindow,
    lengthTWindow, lengthRPrimeWindow, ceilDivAtLeastOne, ceilDiv, rWindowNumerator,
    swapWindowNumerator, lengthTWindowNumerator, lengthRPrimeWindowNumerator, Int.toNat]

example : activeWindows 256 256 =
    ⟨⟨3, 259⟩, ⟨2, 130⟩, ⟨1, 66⟩, ⟨1, 67⟩, ⟨43, 259⟩⟩ := by
  norm_num [activeWindows, remainderWindow, quotientSwapWindow, coefficientWindow,
    lengthTWindow, lengthRPrimeWindow, ceilDivAtLeastOne, ceilDiv, rWindowNumerator,
    swapWindowNumerator, lengthTWindowNumerator, lengthRPrimeWindowNumerator, Int.toNat]

example : activeWindows 256 512 =
    ⟨⟨50, 259⟩, ⟨2, 258⟩, ⟨1, 130⟩, ⟨1, 131⟩, ⟨83, 259⟩⟩ := by
  norm_num [activeWindows, remainderWindow, quotientSwapWindow, coefficientWindow,
    lengthTWindow, lengthRPrimeWindow, ceilDivAtLeastOne, ceilDiv, rWindowNumerator,
    swapWindowNumerator, lengthTWindowNumerator, lengthRPrimeWindowNumerator, Int.toNat]

example : activeWindows 256 1024 =
    ⟨⟨146, 259⟩, ⟨77, 258⟩, ⟨1, 257⟩, ⟨1, 258⟩, ⟨164, 259⟩⟩ := by
  norm_num [activeWindows, remainderWindow, quotientSwapWindow, coefficientWindow,
    lengthTWindow, lengthRPrimeWindow, ceilDivAtLeastOne, ceilDiv, rWindowNumerator,
    swapWindowNumerator, lengthTWindowNumerator, lengthRPrimeWindowNumerator, Int.toNat]

example : activeWindows 256 1536 =
    ⟨⟨243, 259⟩, ⟨231, 258⟩, ⟨1, 257⟩, ⟨219, 258⟩, ⟨245, 259⟩⟩ := by
  norm_num [activeWindows, remainderWindow, quotientSwapWindow, coefficientWindow,
    lengthTWindow, lengthRPrimeWindow, ceilDivAtLeastOne, ceilDiv, rWindowNumerator,
    swapWindowNumerator, lengthTWindowNumerator, lengthRPrimeWindowNumerator, Int.toNat]

example : activeWindows 256 1620 =
    ⟨⟨258, 259⟩, ⟨257, 258⟩, ⟨1, 257⟩, ⟨255, 258⟩, ⟨259, 259⟩⟩ := by
  norm_num [activeWindows, remainderWindow, quotientSwapWindow, coefficientWindow,
    lengthTWindow, lengthRPrimeWindow, ceilDivAtLeastOne, ceilDiv, rWindowNumerator,
    swapWindowNumerator, lengthTWindowNumerator, lengthRPrimeWindowNumerator, Int.toNat]

/- The review witness which caught the Phase-4 endpoint distinction: for input one, the first
256-bit quotient's last microstep selects lane 257, not the Phase-3 endpoint at lane two. -/
private theorem secp256k1PSize : ShorECDLP.p.size = 256 := by
  apply Nat.le_antisymm
  · exact Nat.size_le.mpr (by norm_num [ShorECDLP.p])
  · have : 255 < ShorECDLP.p.size :=
      Nat.lt_size.mpr (by norm_num [ShorECDLP.p])
    omega

private theorem secp256k1OneQuotientSize :
    (paperQuotient (paperInitial ShorECDLP.p 1)).size = 256 := by
  rw [show paperQuotient (paperInitial ShorECDLP.p 1) = ShorECDLP.p by
    norm_num [paperQuotient, paperInitial, correctedInput, ShorECDLP.p]]
  exact secp256k1PSize

private def secp256k1OnePhaseFourFrame : PaperActiveFrame ShorECDLP.p 1 1024 where
  spent := 0
  boundary := paperInitial ShorECDLP.p 1
  reachable := PaperBoundaryReachable.initial
  nonterminal := by norm_num [paperInitial, correctedInput, ShorECDLP.p]
  within := 1024
  within_pos := by norm_num
  within_le := by
    rw [secp256k1OneQuotientSize]
  time_eq := by norm_num

private theorem secp256k1OnePhaseFourEndpoint :
    secp256k1OnePhaseFourFrame.coefficientRight (n := 256) = 257 := by
  rw [PaperActiveFrame.coefficientRight]
  dsimp only [secp256k1OnePhaseFourFrame]
  rw [secp256k1OneQuotientSize]
  norm_num [paperInitial, correctedInput, ShorECDLP.p]

example : (coefficientWindow 256 1024).Covers 1
    (secp256k1OnePhaseFourFrame.coefficientRight (n := 256)) := by
  rw [secp256k1OnePhaseFourEndpoint]
  norm_num [ActiveWindow.Covers, coefficientWindow]

end ShorECDLP.Paper2607_13816
