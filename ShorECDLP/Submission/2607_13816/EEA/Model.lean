import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Pure model of the paper EEA

This file is the circuit-free specification for Sections 3.1--3.3 of arXiv:2607.13816v2.
`paperStep` is one complete Euclidean quotient iteration.  `paperPhaseTrace` exposes the four
logical phases which the later bit-serial circuit refines; the exact 1,620-microstep schedule is
deliberately deferred to `EEA.Bounds` and `EEA.Windows`.

The packed-view theorem applies at canonical quotient boundaries and certifies both span geometry
and value capacity.  Intermediate-frame packing, indexed reachability, and the borrowed epoch bit
which makes terminal padding reversible belong to the Phase-4/5 refinement.  Accordingly, this
file proves a left inverse only for active nonterminal quotient steps; its total logical step
stutters after termination and is not claimed to be injective.

The coefficients are stored as nonnegative magnitudes.  `iter` records their alternating sign,
exactly as in the supplemental generator.  At a canonical iteration boundary we maintain

* `r * t + r' * t' = p`;
* coprimality of the two remainders;
* strict decrease of both remainder and coefficient pairs; and
* the two parity-dependent congruences modulo `p`.

These invariants prove the terminal modular inverse; the pinned Python model is used only for the
small executable examples at the end of the file.
-/

namespace ShorECDLP.Paper2607_13816

/-- The four logical phases encoded by the paper's two phase bits. -/
inductive EEAPhase where
  | remainder
  | quotient
  | coefficient
  | swap
  deriving DecidableEq, Repr

/-- The paper's `(phase1, phase2)` encoding. -/
def EEAPhase.bits : EEAPhase → Bool × Bool
  | .remainder => (false, false)
  | .quotient => (false, true)
  | .coefficient => (true, false)
  | .swap => (true, true)

@[simp] theorem EEAPhase.bits_injective {a b : EEAPhase} :
    a.bits = b.bits ↔ a = b := by
  constructor
  · cases a <;> cases b <;> simp [EEAPhase.bits]
  · exact congrArg EEAPhase.bits

/-- Logical values and the metadata carried by the packed EEA registers. -/
structure EEAState where
  t : ℕ
  q : ℕ
  r : ℕ
  tPrime : ℕ
  rPrime : ℕ
  lT : ℕ
  lQ : ℕ
  lRPrime : ℕ
  shift : ℕ
  phase : EEAPhase
  sign : Bool
  iter : Bool
  deriving DecidableEq, Repr

/-- Logical contents sharing the first `(n+3)`-bit register. -/
structure Work1Value where
  t : ℕ
  q : ℕ
  r : ℕ
  deriving DecidableEq, Repr

/-- Logical contents sharing the circularly shifted second `(n+3)`-bit register. -/
structure Work2Value where
  tPrime : ℕ
  rPrime : ℕ
  shift : ℕ
  deriving DecidableEq, Repr

def EEAState.work1 (s : EEAState) : Work1Value := ⟨s.t, s.q, s.r⟩

def EEAState.work2 (s : EEAState) : Work2Value := ⟨s.tPrime, s.rPrime, s.shift⟩

/-- The quotient bits in the big-endian order used by Work1. -/
def quotientBits (q : ℕ) : List Bool := q.bits.reverse

@[simp] theorem quotientBits_zero : quotientBits 0 = [] := by
  rfl

@[simp] theorem quotientBits_length (q : ℕ) : (quotientBits q).length = q.size := by
  simpa [quotientBits] using Nat.size_eq_bits_len q

/-- The input representative selected by the paper before entering the EEA. -/
def correctedInput (p x : ℕ) : ℕ :=
  if p / 2 < x then p - x else x

/-- The sign correction is remembered by the initial iteration-parity bit. -/
def correctedInputIter (p x : ℕ) : Bool :=
  decide (p / 2 < x)

/-- Canonical metadata at a quotient-iteration boundary. -/
def EEAState.Canonical (s : EEAState) : Prop :=
  s.q = 0 ∧
    s.lQ = 0 ∧
    s.shift = 0 ∧
    s.phase = .remainder ∧
    s.sign = false ∧
    s.lT = s.t.size ∧
    s.lRPrime = s.rPrime.size

/-- Logical initial state.  Work1 is `(1,0,p)` and Work2 is `(0,correctedInput p x)`. -/
def paperInitial (p x : ℕ) : EEAState where
  t := 1
  q := 0
  r := p
  tPrime := 0
  rPrime := correctedInput p x
  lT := 1
  lQ := 0
  lRPrime := (correctedInput p x).size
  shift := 0
  phase := .remainder
  sign := false
  iter := correctedInputIter p x

/-- One ordinary Euclidean quotient. -/
def paperQuotient (s : EEAState) : ℕ := s.r / s.rPrime

/-- The corresponding Euclidean remainder. -/
def paperRemainder (s : EEAState) : ℕ := s.r % s.rPrime

/-- The next canonical boundary, used when `rPrime != 0`. -/
private def nextBoundary (s : EEAState) : EEAState where
  t := s.tPrime + paperQuotient s * s.t
  q := 0
  r := s.rPrime
  tPrime := s.t
  rPrime := paperRemainder s
  lT := (s.tPrime + paperQuotient s * s.t).size
  lQ := 0
  lRPrime := (paperRemainder s).size
  shift := 0
  phase := .remainder
  sign := false
  iter := !s.iter

/-- One complete logical EEA quotient step.  Terminal states are fixed points. -/
def paperStep (s : EEAState) : EEAState :=
  if s.rPrime = 0 then s else nextBoundary s

/-- Four conceptual frames refined by the later bit-serial circuit.

The quotient/remainder frame fills Work1's shared quotient field, the coefficient frame performs
the magnitude update in shifted Work2, and the final frame swaps back to a canonical boundary.
-/
def paperPhaseTrace (s : EEAState) : List EEAState :=
  if s.rPrime = 0 then [s, s, s, s]
  else
    let q := paperQuotient s
    let rem := paperRemainder s
    let quotientFrame :=
      { s with q := q, r := rem, lQ := q.size, phase := .quotient }
    let coefficientFrame :=
      { quotientFrame with
        tPrime := s.tPrime + q * s.t
        phase := .coefficient
        shift := q.size }
    [s, quotientFrame, coefficientFrame,
      { nextBoundary s with phase := .swap }]

@[simp] theorem paperPhaseTrace_length (s : EEAState) :
    (paperPhaseTrace s).length = 4 := by
  simp only [paperPhaseTrace]
  split <;> rfl

theorem paperPhaseTrace_phases {s : EEAState} (hcanonical : s.Canonical)
    (hnonterminal : s.rPrime ≠ 0) :
    (paperPhaseTrace s).map EEAState.phase =
      [.remainder, .quotient, .coefficient, .swap] := by
  rcases hcanonical with ⟨_, _, _, hphase, _, _, _⟩
  simp [paperPhaseTrace, hnonterminal, hphase]

theorem paperPhaseTrace_final {s : EEAState} (hnonterminal : s.rPrime ≠ 0) :
    (paperPhaseTrace s)[3]? = some { paperStep s with phase := .swap } := by
  simp [paperPhaseTrace, hnonterminal, paperStep]

/-- Public expansion of the four logical frames of an active quotient step. -/
theorem paperPhaseTrace_nonterminal {s : EEAState} (hnonterminal : s.rPrime ≠ 0) :
    paperPhaseTrace s =
      [s,
        { s with
          q := paperQuotient s
          r := paperRemainder s
          lQ := (paperQuotient s).size
          phase := .quotient },
        { s with
          q := paperQuotient s
          r := paperRemainder s
          tPrime := s.tPrime + paperQuotient s * s.t
          lQ := (paperQuotient s).size
          phase := .coefficient
          shift := (paperQuotient s).size },
        { paperStep s with phase := .swap }] := by
  simp [paperPhaseTrace, hnonterminal, paperStep]

/-- A half-open physical bit interval. -/
structure BitSpan where
  start : ℕ
  stop : ℕ
  deriving DecidableEq, Repr

/-- Two half-open spans do not overlap. -/
def BitSpan.Disjoint (a b : BitSpan) : Prop :=
  a.stop ≤ b.start ∨ b.stop ≤ a.start

/-- A natural value fits in a well-formed half-open span inside a register of the given width. -/
def BitSpan.Carries (a : BitSpan) (width value : ℕ) : Prop :=
  a.start ≤ a.stop ∧ a.stop ≤ width ∧ a.start + value.size ≤ a.stop

/-- The two `(n+3)`-bit packed work-register views.

Work1 stores little-endian `t`, a separator bit, big-endian `q`, and big-endian `r`.  Work2 stores
little-endian `t'` beside big-endian `r'`; `work2Shift` records the circular rotation and does not
change either field's logical extent.
-/
structure PackedView where
  width : ℕ
  work1Value : Work1Value
  work2Value : Work2Value
  work1T : BitSpan
  work1Q : BitSpan
  work1R : BitSpan
  work2TPrime : BitSpan
  work2RPrime : BitSpan
  work2Shift : ℕ
  deriving DecidableEq, Repr

/-- Derive the paper packing from logical lengths. -/
def packedView (p : ℕ) (s : EEAState) : PackedView :=
  let width := p.size + 3
  { width := width
    work1Value := s.work1
    work2Value := s.work2
    work1T := ⟨0, s.lT⟩
    work1Q := ⟨s.lT + 1, s.lT + 1 + s.lQ⟩
    work1R := ⟨s.lT + 1 + s.lQ, width⟩
    work2TPrime := ⟨0, width - s.lRPrime⟩
    work2RPrime := ⟨width - s.lRPrime, width⟩
    work2Shift := s.shift % width }

/-- At a canonical quotient boundary, all live values fit in well-formed spans and the two logical
partitions are pairwise disjoint.  Intermediate `paperPhaseTrace` frames are only conceptual in
Phase 3; their physical representability belongs to the indexed Phase-4/5 refinement. -/
def PackedView.FieldsNonoverlap (v : PackedView) : Prop :=
  v.work2Shift < v.width ∧
    v.work2Value.shift % v.width = v.work2Shift ∧
    v.work1T.Carries v.width v.work1Value.t ∧
    v.work1Q.Carries v.width v.work1Value.q ∧
    v.work1R.Carries v.width v.work1Value.r ∧
    v.work2TPrime.Carries v.width v.work2Value.tPrime ∧
    v.work2RPrime.Carries v.width v.work2Value.rPrime ∧
    v.work1T.Disjoint v.work1Q ∧
    v.work1T.Disjoint v.work1R ∧
    v.work1Q.Disjoint v.work1R ∧
    v.work2TPrime.Disjoint v.work2RPrime

/-- The complete boundary invariant, parameterized by the original (uncorrected) input. -/
structure PaperInvariant (p x : ℕ) (s : EEAState) : Prop where
  canonical : s.Canonical
  remainder_decreases : s.rPrime < s.r
  coefficient_increases : s.tPrime < s.t
  zero_coefficient_balance : s.tPrime = 0 → 2 * s.rPrime ≤ s.r
  magnitude_identity : s.r * s.t + s.rPrime * s.tPrime = p
  coprime : s.r.Coprime s.rPrime
  r_le : s.r ≤ p
  rPrime_le : s.rPrime ≤ p
  t_le : s.t ≤ p
  tPrime_le : s.tPrime ≤ p
  even_relations : s.iter = false →
    (s.t : ZMod p) * (x : ZMod p) = (s.rPrime : ZMod p) ∧
      (s.tPrime : ZMod p) * (x : ZMod p) + (s.r : ZMod p) = 0
  odd_relations : s.iter = true →
    (s.t : ZMod p) * (x : ZMod p) + (s.rPrime : ZMod p) = 0 ∧
      (s.tPrime : ZMod p) * (x : ZMod p) = (s.r : ZMod p)

@[simp] theorem paperStep_terminal {s : EEAState} (h : s.rPrime = 0) :
    paperStep s = s := by
  simp [paperStep, h]

@[simp] theorem paperStep_nonterminal {s : EEAState} (h : s.rPrime ≠ 0) :
    paperStep s = nextBoundary s := by
  simp [paperStep, h]

/-- An active quotient step strictly decreases the second remainder.  This public projection is
the well-founded clock used by the weighted bit-serial schedule. -/
theorem paperStep_rPrime_lt {s : EEAState} (h : s.rPrime ≠ 0) :
    (paperStep s).rPrime < s.rPrime := by
  rw [paperStep_nonterminal h]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- Public remainder projection of an active quotient step. -/
theorem paperStep_remainders {s : EEAState} (h : s.rPrime ≠ 0) :
    (paperStep s).r = s.rPrime ∧ (paperStep s).rPrime = paperRemainder s := by
  rw [paperStep_nonterminal h]
  exact ⟨rfl, rfl⟩

@[simp] theorem nextBoundary_canonical (s : EEAState) :
    (nextBoundary s).Canonical := by
  simp [nextBoundary, EEAState.Canonical]

private theorem quotient_remainder_eq {s : EEAState} :
    s.rPrime * paperQuotient s + paperRemainder s = s.r := by
  simpa [paperQuotient, paperRemainder] using Nat.div_add_mod s.r s.rPrime

theorem correctedInput_pos {p x : ℕ} (hx : 0 < x) (hxp : x < p) :
    0 < correctedInput p x := by
  simp only [correctedInput]
  split <;> omega

theorem correctedInput_lt {p x : ℕ} (hx : 0 < x) (hxp : x < p) :
    correctedInput p x < p := by
  simp only [correctedInput]
  split <;> omega

private theorem prime_coprime_of_pos_of_lt {p y : ℕ} (hp : p.Prime)
    (hy : 0 < y) (hyp : y < p) : p.Coprime y := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have : y = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hyp
  omega

/-- The `x > p/2` branch stores `p-x` and flips the parity bit; both branches satisfy the same
signed congruence used by the EEA invariant. -/
theorem paperInitial_correction {p x : ℕ} (hxp : x < p) :
    (correctedInputIter p x = false →
        (correctedInput p x : ZMod p) = (x : ZMod p)) ∧
      (correctedInputIter p x = true →
        (correctedInput p x : ZMod p) + (x : ZMod p) = 0) := by
  by_cases hlarge : p / 2 < x
  · constructor
    · simp [correctedInputIter, correctedInput, hlarge]
    · intro _
      simp only [correctedInput, hlarge, if_pos]
      rw [Nat.cast_sub (le_of_lt hxp)]
      simp
  · constructor
    · intro _
      simp [correctedInput, hlarge]
    · simp [correctedInputIter, hlarge]

/-- Every nonzero residue below a prime starts in the boundary invariant. -/
theorem paperInitial_invariant {p x : ℕ} (hp : p.Prime) (hx : 0 < x) (hxp : x < p) :
    PaperInvariant p x (paperInitial p x) := by
  have hcorrPos : 0 < correctedInput p x := correctedInput_pos hx hxp
  have hcorrLt : correctedInput p x < p := correctedInput_lt hx hxp
  have hcop : p.Coprime (correctedInput p x) :=
    prime_coprime_of_pos_of_lt hp hcorrPos hcorrLt
  have hcorrection := paperInitial_correction (p := p) (x := x) hxp
  refine
    { canonical := ?_
      remainder_decreases := hcorrLt
      coefficient_increases := by simp [paperInitial]
      zero_coefficient_balance := by
        intro _
        simp only [paperInitial]
        simp only [correctedInput]
        split <;> omega
      magnitude_identity := by simp [paperInitial]
      coprime := hcop
      r_le := by simp [paperInitial]
      rPrime_le := le_of_lt hcorrLt
      t_le := by have := hp.two_le; simp [paperInitial]; omega
      tPrime_le := by simp [paperInitial]
      even_relations := ?_
      odd_relations := ?_ }
  · simp [paperInitial, EEAState.Canonical]
  · intro heven
    have hc := hcorrection.1 heven
    constructor
    · simpa [paperInitial] using hc.symm
    · simp [paperInitial]
  · intro hodd
    have hc := hcorrection.2 hodd
    constructor
    · simpa [paperInitial, add_comm] using hc
    · simp [paperInitial]

private theorem coprime_remainder {a b : ℕ} (h : a.Coprime b) :
    b.Coprime (a % b) := by
  rw [Nat.Coprime] at h ⊢
  calc
    b.gcd (a % b) = (a % b).gcd b := Nat.gcd_comm _ _
    _ = b.gcd a := (Nat.gcd_rec b a).symm
    _ = a.gcd b := Nat.gcd_comm _ _
    _ = 1 := h

/-- A quotient slot preserves the mathematical boundary invariant; terminal slots stutter. -/
theorem paperStep_preservesInvariant {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) : PaperInvariant p x (paperStep s) := by
  by_cases hterminal : s.rPrime = 0
  · simpa [paperStep_terminal hterminal] using h
  rw [paperStep_nonterminal hterminal]
  have hrpPos : 0 < s.rPrime := Nat.pos_of_ne_zero hterminal
  have htPos : 0 < s.t := lt_of_le_of_lt (Nat.zero_le _) h.coefficient_increases
  have hremLt : paperRemainder s < s.rPrime := by
    exact Nat.mod_lt _ hrpPos
  have hqPos : 0 < paperQuotient s := by
    exact Nat.div_pos (le_of_lt h.remainder_decreases) hrpPos
  have hdecomp :
      s.rPrime * paperQuotient s + paperRemainder s = s.r :=
    quotient_remainder_eq
  have hdecompZ :
      (s.rPrime : ZMod p) * (paperQuotient s : ZMod p) +
          (paperRemainder s : ZMod p) = (s.r : ZMod p) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun n : ℕ => (n : ZMod p)) hdecomp
  have hdecompZ' :
      (paperQuotient s : ZMod p) * (s.rPrime : ZMod p) +
          (paperRemainder s : ZMod p) = (s.r : ZMod p) := by
    simpa [mul_comm] using hdecompZ
  have hcoefficient : s.t < s.tPrime + paperQuotient s * s.t := by
    by_cases htpZero : s.tPrime = 0
    · have hqTwo : 2 ≤ paperQuotient s := by
        apply (Nat.le_div_iff_mul_le hrpPos).2
        simpa [paperQuotient] using h.zero_coefficient_balance htpZero
      have htwice : 2 * s.t ≤ paperQuotient s * s.t :=
        Nat.mul_le_mul_right s.t hqTwo
      omega
    · have htpPos : 0 < s.tPrime := Nat.pos_of_ne_zero htpZero
      have htle : s.t ≤ paperQuotient s * s.t :=
        Nat.le_mul_of_pos_left s.t hqPos
      omega
  have hmagnitude :
      s.rPrime * (s.tPrime + paperQuotient s * s.t) +
          paperRemainder s * s.t = p := by
    calc
      s.rPrime * (s.tPrime + paperQuotient s * s.t) +
            paperRemainder s * s.t =
          s.rPrime * s.tPrime +
            (s.rPrime * paperQuotient s + paperRemainder s) * s.t := by ring
      _ = s.rPrime * s.tPrime + s.r * s.t := by rw [hdecomp]
      _ = p := by simpa [Nat.add_comm] using h.magnitude_identity
  have hnextT : s.tPrime + paperQuotient s * s.t ≤ p := by
    calc
      s.tPrime + paperQuotient s * s.t ≤
          s.rPrime * (s.tPrime + paperQuotient s * s.t) :=
        Nat.le_mul_of_pos_left _ hrpPos
      _ ≤ s.rPrime * (s.tPrime + paperQuotient s * s.t) +
          paperRemainder s * s.t := Nat.le_add_right _ _
      _ = p := hmagnitude
  refine
    { canonical := nextBoundary_canonical s
      remainder_decreases := hremLt
      coefficient_increases := hcoefficient
      zero_coefficient_balance := ?_
      magnitude_identity := hmagnitude
      coprime := coprime_remainder h.coprime
      r_le := h.rPrime_le
      rPrime_le := le_trans (le_of_lt hremLt) h.rPrime_le
      t_le := hnextT
      tPrime_le := h.t_le
      even_relations := ?_
      odd_relations := ?_ }
  · intro hz
    change s.t = 0 at hz
    omega
  · intro hnewEven
    have holdOdd : s.iter = true := by
      cases hs : s.iter <;> simp [nextBoundary, hs] at hnewEven ⊢
    obtain ⟨holdT, holdTPrime⟩ := h.odd_relations holdOdd
    have htx : (s.t : ZMod p) * (x : ZMod p) = -(s.rPrime : ZMod p) :=
      eq_neg_of_add_eq_zero_left holdT
    constructor
    · change
        ((s.tPrime + paperQuotient s * s.t : ℕ) : ZMod p) * (x : ZMod p) =
          (paperRemainder s : ZMod p)
      calc
        ((s.tPrime + paperQuotient s * s.t : ℕ) : ZMod p) * (x : ZMod p) =
            (s.tPrime : ZMod p) * (x : ZMod p) +
              (paperQuotient s : ZMod p) * ((s.t : ZMod p) * (x : ZMod p)) := by
                simp only [Nat.cast_add, Nat.cast_mul]
                ring
        _ = (s.r : ZMod p) +
              (paperQuotient s : ZMod p) * (-(s.rPrime : ZMod p)) := by
                rw [holdTPrime, htx]
        _ = (paperRemainder s : ZMod p) := by
                rw [← hdecompZ]
                ring
    · change (s.t : ZMod p) * (x : ZMod p) + (s.rPrime : ZMod p) = 0
      exact holdT

  · intro hnewOdd
    have holdEven : s.iter = false := by
      cases hs : s.iter <;> simp [nextBoundary, hs] at hnewOdd ⊢
    obtain ⟨holdT, holdTPrime⟩ := h.even_relations holdEven
    constructor
    · change
        ((s.tPrime + paperQuotient s * s.t : ℕ) : ZMod p) * (x : ZMod p) +
            (paperRemainder s : ZMod p) = 0
      calc
        ((s.tPrime + paperQuotient s * s.t : ℕ) : ZMod p) * (x : ZMod p) +
              (paperRemainder s : ZMod p) =
            (s.tPrime : ZMod p) * (x : ZMod p) +
              (paperQuotient s : ZMod p) *
                ((s.t : ZMod p) * (x : ZMod p)) +
              (paperRemainder s : ZMod p) := by
                simp only [Nat.cast_add, Nat.cast_mul]
                ring
        _ = (s.tPrime : ZMod p) * (x : ZMod p) +
              ((paperQuotient s : ZMod p) * (s.rPrime : ZMod p) +
                (paperRemainder s : ZMod p)) := by
                  rw [holdT]
                  ring
        _ = (s.tPrime : ZMod p) * (x : ZMod p) + (s.r : ZMod p) := by
              rw [hdecompZ']
        _ = 0 := holdTPrime
    · change (s.t : ZMod p) * (x : ZMod p) = (s.rPrime : ZMod p)
      exact holdT

/-- If two factors and their product are bounded by `p`, their binary lengths fit together with one
guard bit. -/
private theorem size_add_size_le_of_mul_le {a b p : ℕ} (ha : a ≤ p) (hb : b ≤ p)
    (hab : a * b ≤ p) : a.size + b.size ≤ p.size + 1 := by
  by_cases ha0 : a = 0
  · subst a
    have hsize := Nat.size_le_size hb
    simpa only [Nat.size_zero, Nat.zero_add] using le_trans hsize (Nat.le_add_right _ _)
  by_cases hb0 : b = 0
  · subst b
    have hsize := Nat.size_le_size ha
    simpa only [Nat.size_zero, Nat.add_zero] using le_trans hsize (Nat.le_add_right _ _)
  have haSize : 0 < a.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero ha0)
  have hbSize : 0 < b.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hb0)
  have haPow : 2 ^ (a.size - 1) ≤ a :=
    Nat.lt_size.mp (by omega)
  have hbPow : 2 ^ (b.size - 1) ≤ b :=
    Nat.lt_size.mp (by omega)
  by_contra hsize
  have hexponent : p.size ≤ (a.size - 1) + (b.size - 1) := by omega
  have hpow : 2 ^ p.size ≤ 2 ^ ((a.size - 1) + (b.size - 1)) :=
    Nat.pow_le_pow_right (by decide) hexponent
  rw [pow_add] at hpow
  have htooLarge : 2 ^ p.size ≤ p :=
    le_trans hpow (le_trans (Nat.mul_le_mul haPow hbPow) hab)
  exact (Nat.not_lt_of_ge htooLarge) (Nat.lt_size_self p)

/-- The dynamic lengths in every invariant canonical boundary give a valid `(n+3)`-bit packing:
every span is ordered and in range, every logical value fits its span, and the live fields are
disjoint.  The Work2 rotation is represented by its reduced circular offset. -/
theorem packedFields_nonoverlap {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) : (packedView p s).FieldsNonoverlap := by
  have hrt : s.r * s.t ≤ p := by
    rw [← h.magnitude_identity]
    exact Nat.le_add_right _ _
  have hrptp : s.rPrime * s.tPrime ≤ p := by
    rw [← h.magnitude_identity]
    exact Nat.le_add_left _ _
  have hwork1Capacity : s.r.size + s.t.size ≤ p.size + 1 :=
    size_add_size_le_of_mul_le h.r_le h.t_le hrt
  have hwork2Capacity : s.rPrime.size + s.tPrime.size ≤ p.size + 1 :=
    size_add_size_le_of_mul_le h.rPrime_le h.tPrime_le hrptp
  rcases h.canonical with ⟨hq, hlq, hshift, _, _, hlt, hlrp⟩
  simp only [packedView, PackedView.FieldsNonoverlap, BitSpan.Carries, BitSpan.Disjoint,
    EEAState.work1, EEAState.work2]
  rw [hq, hlt, hlrp, hlq, hshift]
  have hwidth : 0 < p.size + 3 := by omega
  have hshiftBound : 0 % (p.size + 3) < p.size + 3 := Nat.mod_lt _ hwidth
  simp only [Nat.zero_mod]
  simp
  omega

/-- The inverse boundary transformation.  On reachable states the old quotient and coefficient
are recovered by Euclidean division of the new coefficient pair, so no quotient history is kept. -/
def paperUnstep (s : EEAState) : EEAState :=
  let oldQ := s.t / s.tPrime
  let oldT := s.tPrime
  let oldTPrime := s.t % s.tPrime
  let oldRPrime := s.r
  let oldR := oldQ * s.r + s.rPrime
  { t := oldT
    q := 0
    r := oldR
    tPrime := oldTPrime
    rPrime := oldRPrime
    lT := oldT.size
    lQ := 0
    lRPrime := oldRPrime.size
    shift := 0
    phase := .remainder
    sign := false
    iter := !s.iter }

/-- On a nonterminal invariant boundary, `paperUnstep` is a concrete left inverse of the active
quotient step.  This does not assert injectivity of total `paperStep`: its final active step and a
terminal stuttering slot collide.  Phase 4/5 must add the indexed reachability and borrowed padding
epoch used by the paper before refining this abstraction to a reversible fixed-horizon circuit. -/
theorem paperStep_reversible_onInvariant {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) (hnonterminal : s.rPrime ≠ 0) :
    paperUnstep (paperStep s) = s := by
  rw [paperStep_nonterminal hnonterminal]
  have htPos : 0 < s.t := lt_of_le_of_lt (Nat.zero_le _) h.coefficient_increases
  have hquotientRecover :
      (s.tPrime + paperQuotient s * s.t) / s.t = paperQuotient s := by
    calc
      (s.tPrime + paperQuotient s * s.t) / s.t =
          (s.tPrime + s.t * paperQuotient s) / s.t := by rw [Nat.mul_comm]
      _ = s.tPrime / s.t + paperQuotient s :=
        Nat.add_mul_div_left _ _ htPos
      _ = paperQuotient s := by
        rw [Nat.div_eq_of_lt h.coefficient_increases]
        simp
  have hremainderRecover :
      (s.tPrime + paperQuotient s * s.t) % s.t = s.tPrime := by
    calc
      (s.tPrime + paperQuotient s * s.t) % s.t =
          (s.tPrime + s.t * paperQuotient s) % s.t := by rw [Nat.mul_comm]
      _ = s.tPrime % s.t := Nat.add_mul_mod_self_left _ _ _
      _ = s.tPrime := Nat.mod_eq_of_lt h.coefficient_increases
  have hremainderDecomp :
      paperQuotient s * s.rPrime + paperRemainder s = s.r := by
    simpa [Nat.mul_comm] using (quotient_remainder_eq (s := s))
  rcases h.canonical with ⟨hq, hlq, hshift, hphase, hsign, hlt, hlrp⟩
  cases s
  simp_all [paperUnstep, nextBoundary]

/-- Run quotient iterations to the first state with zero second remainder. -/
def paperRun (s : EEAState) : EEAState :=
  if s.rPrime = 0 then s else paperRun (paperStep s)
termination_by s.rPrime
decreasing_by
  rename_i h
  simp only [paperStep, h, if_false, nextBoundary, paperRemainder]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem paperRun_of_terminal {s : EEAState} (h : s.rPrime = 0) :
    paperRun s = s := by
  rw [paperRun]
  simp [h]

theorem paperRun_of_nonterminal {s : EEAState} (h : s.rPrime ≠ 0) :
    paperRun s = paperRun (paperStep s) := by
  rw [paperRun]
  simp [h]

/-- The unbounded mathematical run always reaches a zero second remainder. -/
theorem paperRun_zero_remainder (s : EEAState) : (paperRun s).rPrime = 0 := by
  by_cases hterminal : s.rPrime = 0
  · rw [paperRun_of_terminal hterminal]
    exact hterminal
  · rw [paperRun_of_nonterminal hterminal]
    exact paperRun_zero_remainder (paperStep s)
termination_by s.rPrime
decreasing_by
  simp only [paperStep, hterminal, if_false, nextBoundary, paperRemainder]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hterminal)

/-- Every invariant along the mathematical run follows from the direct step theorem. -/
theorem paperRun_preservesInvariant {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) : PaperInvariant p x (paperRun s) := by
  by_cases hterminal : s.rPrime = 0
  · simpa [paperRun_of_terminal hterminal] using h
  · rw [paperRun_of_nonterminal hterminal]
    exact paperRun_preservesInvariant (paperStep_preservesInvariant h)
termination_by s.rPrime
decreasing_by
  simp only [paperStep, hterminal, if_false, nextBoundary, paperRemainder]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hterminal)

/-- Execute a fixed number of logical quotient slots.  Phase 4 will prove a concrete sufficient
fuel and refine each logical slot to the paper's bit-serial microsteps. -/
def paperRunFor : ℕ → EEAState → EEAState
  | 0, s => s
  | fuel + 1, s => paperRunFor fuel (paperStep s)

/-- At quotient-boundary level, once terminal every remaining fixed-horizon slot stutters.  This is
not yet a reversible padded-step contract; the indexed borrowed-epoch refinement is a Phase-4/5
obligation. -/
theorem paperRun_padding_is_id {s : EEAState} (hterminal : s.rPrime = 0) (padding : ℕ) :
    paperRunFor padding s = s := by
  induction padding with
  | zero => rfl
  | succ padding ih =>
      simp only [paperRunFor, paperStep_terminal hterminal, ih]

/-- The sign-corrected coefficient represented by a terminal state. -/
def paperExtract (p : ℕ) (s : EEAState) : ℕ :=
  if s.iter = true then s.tPrime else p - s.tPrime

theorem terminal_remainder_eq_one {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) (hterminal : s.rPrime = 0) : s.r = 1 := by
  have hcop : s.r.Coprime 0 := by simpa [hterminal] using h.coprime
  exact (Nat.coprime_zero_right s.r).mp hcop

private theorem terminal_t_eq_modulus {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) (hterminal : s.rPrime = 0) : s.t = p := by
  have hr : s.r = 1 := terminal_remainder_eq_one h hterminal
  simpa [hr, hterminal] using h.magnitude_identity

/-- The complete run from a valid prime-field input reaches the canonical terminal boundary
`(r,r',t) = (1,0,p)`. -/
theorem paperRun_terminal {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p) :
    let s := paperRun (paperInitial p x)
    s.rPrime = 0 ∧ s.r = 1 ∧ s.t = p ∧ s.Canonical := by
  let s := paperRun (paperInitial p x)
  have hInitial : PaperInvariant p x (paperInitial p x) :=
    paperInitial_invariant hp (by omega) hxp
  have hInvariant : PaperInvariant p x s := paperRun_preservesInvariant hInitial
  have hTerminal : s.rPrime = 0 := paperRun_zero_remainder _
  exact ⟨hTerminal, terminal_remainder_eq_one hInvariant hTerminal,
    terminal_t_eq_modulus hInvariant hTerminal, hInvariant.canonical⟩

/-- At an invariant terminal boundary, parity chooses the positive or negative coefficient whose
product with the original input is one modulo `p`. -/
theorem paperTerminal_inverse {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) (hterminal : s.rPrime = 0) :
    (paperExtract p s : ZMod p) * (x : ZMod p) = 1 := by
  have hr : s.r = 1 := terminal_remainder_eq_one h hterminal
  by_cases hiter : s.iter = true
  · obtain ⟨_, htPrime⟩ := h.odd_relations hiter
    simpa [paperExtract, hiter, hr] using htPrime
  · have heven : s.iter = false := by
      cases hs : s.iter <;> simp_all
    obtain ⟨_, htPrime⟩ := h.even_relations heven
    have htNeg : (s.tPrime : ZMod p) * (x : ZMod p) = -1 := by
      rw [hr] at htPrime
      norm_num at htPrime
      exact eq_neg_of_add_eq_zero_left htPrime
    rw [paperExtract, if_neg hiter]
    rw [Nat.cast_sub h.tPrime_le]
    simp only [ZMod.natCast_self, zero_sub]
    calc
      (-(s.tPrime : ZMod p)) * (x : ZMod p) =
          -((s.tPrime : ZMod p) * (x : ZMod p)) := by ring
      _ = 1 := by rw [htNeg]; simp

/-- The extracted result of the complete mathematical run. -/
def paperInverse (p x : ℕ) : ℕ :=
  paperExtract p (paperRun (paperInitial p x))

/-- Direct Phase-3 correctness theorem: every nonzero residue below a prime is inverted modulo
that prime by the paper recurrence. -/
theorem paperRun_inverse_mod_prime {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p) :
    (paperInverse p x : ZMod p) * (x : ZMod p) = 1 := by
  let s := paperRun (paperInitial p x)
  have hInitial : PaperInvariant p x (paperInitial p x) :=
    paperInitial_invariant hp (by omega) hxp
  have hInvariant : PaperInvariant p x s := paperRun_preservesInvariant hInitial
  have hTerminal : s.rPrime = 0 := paperRun_zero_remainder _
  exact paperTerminal_inverse hInvariant hTerminal

/-! ## Kernel-reduced cross-checks

These examples pin the three terminal rows in `REFERENCE.md`.  They use definitional reduction
only and are deliberately not used anywhere in the general proofs above.
-/

example : paperRun (paperInitial 13 5) =
    { t := 13, q := 0, r := 1, tPrime := 5, rPrime := 0
      lT := 4, lQ := 0, lRPrime := 0, shift := 0
      phase := .remainder, sign := false, iter := false } := by
  norm_num [paperRun, paperStep, nextBoundary, paperInitial, correctedInput,
    correctedInputIter, paperQuotient, paperRemainder, Nat.size]
  decide

example : paperRun (paperInitial 17 7) =
    { t := 17, q := 0, r := 1, tPrime := 5, rPrime := 0
      lT := 5, lQ := 0, lRPrime := 0, shift := 0
      phase := .remainder, sign := false, iter := true } := by
  norm_num [paperRun, paperStep, nextBoundary, paperInitial, correctedInput,
    correctedInputIter, paperQuotient, paperRemainder, Nat.size]
  decide

example : paperRun (paperInitial 31 12) =
    { t := 31, q := 0, r := 1, tPrime := 13, rPrime := 0
      lT := 5, lQ := 0, lRPrime := 0, shift := 0
      phase := .remainder, sign := false, iter := true } := by
  norm_num [paperRun, paperStep, nextBoundary, paperInitial, correctedInput,
    correctedInputIter, paperQuotient, paperRemainder, Nat.size]
  decide

/-- A concrete large-half input exercises the `p-x` parity correction. -/
example : paperInverse 13 8 = 5 := by
  norm_num [paperInverse, paperExtract, paperRun, paperStep, nextBoundary, paperInitial,
    correctedInput, correctedInputIter, paperQuotient, paperRemainder]

end ShorECDLP.Paper2607_13816
