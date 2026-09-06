import ShorECDLP.Math.BitcoinPrimes
import ShorECDLP.Submission.«2607_13816».EEA.Model

/-!
# Exact weighted EEA bound

The paper's bit-serial schedule spends four microsteps for every bit of an ordinary Euclidean
quotient.  This file connects that weighted clock to `paperStep` and proves the concrete
secp256k1 horizon without trusting floating-point logarithms.

The proof uses the rational base `155113 / 100000`, which is slightly smaller than
`(2 + sqrt 3)^(1/3)`, together with a four-row rational polyhedral antinorm certificate.  Every
certificate comparison is checked by the Lean kernel.  The deliberately weaker rational base is
still strong enough to show that weighted cost `406` would force a modulus larger than `2^256`.
-/

namespace ShorECDLP.Paper2607_13816

/-- Exact rational growth base used by the finite certificate. -/
def eeaGrowthBase : ℚ := 155113 / 100000

private def potentialRow0 (a b : ℚ) : ℚ := (2732025414027897 / 1000000000000000) * a + b
private def potentialRow1 (a b : ℚ) : ℚ :=
  (24060042769 / 10000000000) * a + (2732025414027897 / 1551130000000000) * b
private def potentialRow2 (a b : ℚ) : ℚ :=
  (1766012707013948500000 / 578885658046109187361) * a + (100000 / 155113) * b
private def potentialRow3 (a b : ℚ) : ℚ :=
  (213921524841673820000000000 / 89792691076506134379126793) * a +
    (176601270701394850000000000 / 89792691076506134379126793) * b

private def potentialAxisCoefficient : ℚ :=
  213921524841673820000000000 / 89792691076506134379126793

private def potentialDiagCoefficient : ℚ :=
  2139215248416738200000 / 578885658046109187361

/-- The minimum of four exact rational linear forms. -/
def eeaPotential (a b : ℚ) : ℚ :=
  min (potentialRow0 a b)
    (min (potentialRow1 a b) (min (potentialRow2 a b) (potentialRow3 a b)))

private theorem potential_le_row0 (a b : ℚ) :
    eeaPotential a b ≤ potentialRow0 a b := by
  exact min_le_left _ _

private theorem potential_le_row1 (a b : ℚ) :
    eeaPotential a b ≤ potentialRow1 a b := by
  exact (min_le_right _ _).trans (min_le_left _ _)

private theorem potential_le_row2 (a b : ℚ) :
    eeaPotential a b ≤ potentialRow2 a b := by
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

private theorem potential_le_row3 (a b : ℚ) :
    eeaPotential a b ≤ potentialRow3 a b := by
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

private theorem potential_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ eeaPotential a b := by
  simp only [eeaPotential, le_min_iff]
  constructor
  · simp only [potentialRow0]
    positivity
  constructor
  · simp only [potentialRow1]
    positivity
  constructor
  · simp only [potentialRow2]
    positivity
  · simp only [potentialRow3]
    positivity

private theorem potential_mono {a b c d : ℚ} (hac : a ≤ c) (hbd : b ≤ d) :
    eeaPotential a b ≤ eeaPotential c d := by
  apply min_le_min
  · simp only [potentialRow0]
    nlinarith
  apply min_le_min
  · simp only [potentialRow1]
    nlinarith
  apply min_le_min
  · simp only [potentialRow2]
    nlinarith
  · simp only [potentialRow3]
    nlinarith

private theorem potential_transform_size_one {a b q : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 1 ≤ q) :
    eeaGrowthBase * eeaPotential a b ≤ eeaPotential (q * a + b) a := by
  simp only [eeaPotential, le_min_iff]
  have hqmul : a ≤ q * a := by nlinarith [mul_le_mul_of_nonneg_right hq ha]
  have h0 := potential_le_row0 a b
  have h1 := potential_le_row1 a b
  have h3 := potential_le_row3 a b
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith

private theorem potential_transform_size_two {a b q : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hba : b ≤ a) (hq : 2 ≤ q) :
    eeaGrowthBase ^ 2 * eeaPotential a b ≤ eeaPotential (q * a + b) a := by
  simp only [eeaPotential, le_min_iff]
  have hqmul : 2 * a ≤ q * a := by nlinarith [mul_le_mul_of_nonneg_right hq ha]
  have h0 := potential_le_row0 a b
  have h1 := potential_le_row1 a b
  have hmix : eeaPotential a b ≤
      (4 / 5 : ℚ) * potentialRow0 a b + (1 / 5 : ℚ) * potentialRow1 a b := by
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith

private theorem potential_transform_size_three {a b q : ℚ} (ha : 0 ≤ a)
    (hba : b ≤ a) (hq : 4 ≤ q) :
    eeaGrowthBase ^ 3 * eeaPotential a b ≤ eeaPotential (q * a + b) a := by
  simp only [eeaPotential, le_min_iff]
  have hqmul : 4 * a ≤ q * a := by nlinarith [mul_le_mul_of_nonneg_right hq ha]
  have h0 := potential_le_row0 a b
  have h2 := potential_le_row2 a b
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith

private theorem potential_transform_size_four {a b q : ℚ} (ha : 0 ≤ a)
    (hba : b ≤ a) (hq : 8 ≤ q) :
    eeaGrowthBase ^ 4 * eeaPotential a b ≤ eeaPotential (q * a + b) a := by
  simp only [eeaPotential, le_min_iff]
  have hqmul : 8 * a ≤ q * a := by nlinarith [mul_le_mul_of_nonneg_right hq ha]
  have h0 := potential_le_row0 a b
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  constructor
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith
  · simp only [eeaPotential, eeaGrowthBase, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3] at *
    nlinarith

private theorem potential_axis {a : ℚ} (ha : 0 ≤ a) :
    eeaPotential a 0 = potentialAxisCoefficient * a := by
  apply le_antisymm
  · simpa [potentialAxisCoefficient, potentialRow3] using potential_le_row3 a 0
  · simp only [eeaPotential, le_min_iff, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3, potentialAxisCoefficient]
    norm_num
    constructor
    · nlinarith
    constructor
    · nlinarith
    nlinarith

private theorem potential_diag {a : ℚ} (ha : 0 ≤ a) :
    eeaPotential a a = potentialDiagCoefficient * a := by
  have hrow2 : potentialRow2 a a =
      potentialDiagCoefficient * a := by
    simp only [potentialRow2, potentialDiagCoefficient]
    ring
  rw [← hrow2]
  apply le_antisymm
  · exact potential_le_row2 a a
  · simp only [eeaPotential, le_min_iff, potentialRow0, potentialRow1, potentialRow2,
      potentialRow3]
    norm_num
    constructor
    · nlinarith
    constructor
    · nlinarith
    nlinarith

private theorem potential_transform_coarse {a b q : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hba : b ≤ a) (hq : 0 ≤ q) :
    q * eeaPotential a b ≤ eeaGrowthBase * eeaPotential (q * a + b) a := by
  have hin : eeaPotential a b ≤ eeaPotential a a :=
    potential_mono le_rfl hba
  have hqa : q * a ≤ q * a + b := by linarith
  have hout : eeaPotential (q * a) 0 ≤ eeaPotential (q * a + b) a :=
    potential_mono hqa ha
  have hqin := mul_le_mul_of_nonneg_left hin hq
  rw [potential_diag ha] at hin
  rw [potential_diag ha] at hqin
  rw [potential_axis (mul_nonneg hq ha)] at hout
  norm_num [eeaGrowthBase, potentialAxisCoefficient, potentialDiagCoefficient] at hqin hout ⊢
  nlinarith

private theorem growth_pow_bound (k : ℕ) :
    eeaGrowthBase ^ (6 + k) ≤ (2 : ℚ) ^ (4 + k) := by
  induction k with
  | zero => norm_num [eeaGrowthBase]
  | succ k ih =>
      simp only [Nat.add_succ, pow_succ]
      calc
        eeaGrowthBase ^ (6 + k) * eeaGrowthBase ≤
            (2 : ℚ) ^ (4 + k) * eeaGrowthBase :=
          mul_le_mul_of_nonneg_right ih (by norm_num [eeaGrowthBase])
        _ ≤ (2 : ℚ) ^ (4 + k) * 2 :=
          mul_le_mul_of_nonneg_left (by norm_num [eeaGrowthBase]) (by positivity)

/-- The exact rational certificate grows by one base factor for every quotient bit. -/
theorem eeaPotential_step {a b q : ℕ} (hba : b ≤ a) (hq : 0 < q) :
    eeaGrowthBase ^ q.size * eeaPotential a b ≤
      eeaPotential (q * a + b) a := by
  have haQ : (0 : ℚ) ≤ a := by positivity
  have hbQ : (0 : ℚ) ≤ b := by positivity
  have hbaQ : (b : ℚ) ≤ a := by exact_mod_cast hba
  have hqQ : (1 : ℚ) ≤ q := by exact_mod_cast hq
  by_cases hsize1 : q.size = 1
  · rw [hsize1, pow_one]
    exact potential_transform_size_one haQ hbQ hqQ
  by_cases hsize2 : q.size = 2
  · have hq2 : 2 ≤ q := by
      exact (Nat.lt_size (m := 1) (n := q)).mp (by omega)
    rw [hsize2]
    exact potential_transform_size_two haQ hbQ hbaQ (by exact_mod_cast hq2)
  by_cases hsize3 : q.size = 3
  · have hq4 : 4 ≤ q := by
      exact (Nat.lt_size (m := 2) (n := q)).mp (by omega)
    rw [hsize3]
    exact potential_transform_size_three haQ hbaQ (by exact_mod_cast hq4)
  by_cases hsize4 : q.size = 4
  · have hq8 : 8 ≤ q := by
      exact (Nat.lt_size (m := 3) (n := q)).mp (by omega)
    rw [hsize4]
    exact potential_transform_size_four haQ hbaQ (by exact_mod_cast hq8)
  · have hsizePos : 0 < q.size := Nat.size_pos.mpr hq
    have hsizeLarge : 5 ≤ q.size := by omega
    let k := q.size - 5
    have hk : q.size = 5 + k := by simp [k, hsizeLarge]
    have hpow := growth_pow_bound k
    have hqNat : 2 ^ (q.size - 1) ≤ q :=
      (Nat.lt_size (m := q.size - 1) (n := q)).mp (by omega)
    have htwoQ : (2 : ℚ) ^ (q.size - 1) ≤ q := by exact_mod_cast hqNat
    have hbaseQ : eeaGrowthBase ^ (q.size + 1) ≤ (q : ℚ) := by
      calc
        eeaGrowthBase ^ (q.size + 1) = eeaGrowthBase ^ (6 + k) := by
          congr 1
          omega
        _ ≤ (2 : ℚ) ^ (4 + k) := hpow
        _ = (2 : ℚ) ^ (q.size - 1) := by
          congr 1
          omega
        _ ≤ (q : ℚ) := htwoQ
    have hpotentialNonneg : 0 ≤ eeaPotential (a : ℚ) b := potential_nonneg haQ hbQ
    have hscaled :
        eeaGrowthBase ^ (q.size + 1) * eeaPotential a b ≤
          (q : ℚ) * eeaPotential a b :=
      mul_le_mul_of_nonneg_right hbaseQ hpotentialNonneg
    have hcoarse := potential_transform_coarse haQ hbQ hbaQ (q := (q : ℚ)) (by positivity)
    have hmuPos : (0 : ℚ) < eeaGrowthBase := by norm_num [eeaGrowthBase]
    apply (mul_le_mul_iff_right₀ hmuPos).mp
    calc
      eeaGrowthBase * (eeaGrowthBase ^ q.size * eeaPotential a b) =
          eeaGrowthBase ^ (q.size + 1) * eeaPotential a b := by
        rw [pow_succ]
        ring
      _ ≤ (q : ℚ) * eeaPotential a b := hscaled
      _ ≤ eeaGrowthBase * eeaPotential ((q : ℚ) * a + b) a := hcoarse

/-- Exact finite-prefix constant for the first nontrivial quotient. -/
def eeaPrefixEta : ℚ :=
  77762669692006134379126793 / 106960762420836910000000000

/-- Exact rational upper slope used for finite step-window arithmetic. -/
def eeaWindowSlope : ℚ := 2089 / 1323

/-- Exact rational finite-prefix correction used for step-window arithmetic. -/
def eeaWindowDelta : ℚ := 727 / 1000

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem window_slope_certificate :
    (2 : ℚ) ^ 1323 ≤ eeaGrowthBase ^ 2089 := by
  rw [eeaGrowthBase, div_pow, le_div_iff₀ (by positivity)]
  norm_num [pow_succ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem window_delta_certificate :
    (1 : ℚ) ≤ eeaPrefixEta ^ 1323 * eeaGrowthBase ^ 962 := by
  rw [eeaPrefixEta, eeaGrowthBase, div_pow, div_pow, div_mul_div_comm,
    one_le_div₀ (by positivity)]
  norm_num [pow_succ]

private theorem potential_first_step {q : ℕ} (hq : 2 ≤ q) :
    eeaGrowthBase ^ q.size * eeaPotential 2 1 ≤
      eeaGrowthBase ^ 2 * eeaPotential q 1 := by
  have hsize : 2 ≤ q.size := by
    have := (Nat.lt_size (m := 1) (n := q)).mpr hq
    omega
  by_cases hsize2 : q.size = 2
  · rw [hsize2]
    apply mul_le_mul_of_nonneg_left
    · exact potential_mono (by exact_mod_cast hq) le_rfl
    · positivity
  by_cases hsize3 : q.size = 3
  · have hq4 : 4 ≤ q :=
      (Nat.lt_size (m := 2) (n := q)).mp (by omega)
    have hmono : eeaPotential (4 : ℚ) 1 ≤ eeaPotential q 1 :=
      potential_mono (by exact_mod_cast hq4) le_rfl
    rw [hsize3, show 3 = 2 + 1 by omega, pow_add]
    have hconcrete :
        eeaGrowthBase * eeaPotential (2 : ℚ) 1 ≤ eeaPotential (4 : ℚ) 1 := by
      norm_num [eeaGrowthBase, eeaPotential, potentialRow0, potentialRow1,
        potentialRow2, potentialRow3, min_def]
    simpa only [pow_one, mul_assoc] using
      mul_le_mul_of_nonneg_left (hconcrete.trans hmono)
        (show (0 : ℚ) ≤ eeaGrowthBase ^ 2 from
          pow_nonneg (by norm_num [eeaGrowthBase]) _)
  · have hsize4 : 4 ≤ q.size := by omega
    let k := q.size - 4
    have hk : q.size = 4 + k := by simp [k, hsize4]
    have hqPowNat : 2 ^ (q.size - 1) ≤ q :=
      (Nat.lt_size (m := q.size - 1) (n := q)).mp (by omega)
    have hqPow : (2 : ℚ) ^ (q.size - 1) ≤ q := by exact_mod_cast hqPowNat
    have hmono :
        eeaPotential ((2 : ℚ) ^ (q.size - 1)) 0 ≤ eeaPotential q 1 :=
      potential_mono hqPow (by norm_num)
    rw [potential_axis (by positivity)] at hmono
    have hbase :
        eeaGrowthBase ^ 2 * eeaPotential (2 : ℚ) 1 ≤
          8 * potentialAxisCoefficient := by
      norm_num [eeaGrowthBase, eeaPotential, potentialRow0, potentialRow1,
        potentialRow2, potentialRow3, potentialAxisCoefficient, min_def]
    have hmuTwo : eeaGrowthBase ≤ (2 : ℚ) := by norm_num [eeaGrowthBase]
    have hpows : eeaGrowthBase ^ k ≤ (2 : ℚ) ^ k :=
      pow_le_pow_left₀ (by norm_num [eeaGrowthBase]) hmuTwo k
    have hconstNonneg : (0 : ℚ) ≤ 8 * potentialAxisCoefficient := by
      norm_num [potentialAxisCoefficient]
    calc
      eeaGrowthBase ^ q.size * eeaPotential 2 1 =
          eeaGrowthBase ^ 2 *
            (eeaGrowthBase ^ k * (eeaGrowthBase ^ 2 * eeaPotential 2 1)) := by
        rw [hk]
        ring
      _ ≤ eeaGrowthBase ^ 2 *
          (eeaGrowthBase ^ k * (8 * potentialAxisCoefficient)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hbase
            (pow_nonneg (by norm_num [eeaGrowthBase]) _)
        · exact pow_nonneg (by norm_num [eeaGrowthBase]) _
      _ ≤ eeaGrowthBase ^ 2 *
          ((2 : ℚ) ^ k * (8 * potentialAxisCoefficient)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hpows hconstNonneg
        · exact pow_nonneg (by norm_num [eeaGrowthBase]) _
      _ = eeaGrowthBase ^ 2 *
          ((2 : ℚ) ^ (q.size - 1) * potentialAxisCoefficient) := by
        rw [hk]
        rw [show 4 + k - 1 = k + 3 by omega, show (8 : ℚ) = 2 ^ 3 by norm_num,
          pow_add (2 : ℚ) k 3]
        ring
      _ ≤ eeaGrowthBase ^ 2 * eeaPotential q 1 := by
        calc
          eeaGrowthBase ^ 2 *
              ((2 : ℚ) ^ (q.size - 1) * potentialAxisCoefficient) ≤
              eeaGrowthBase ^ 2 * eeaPotential q 1 :=
            mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hmono)
              (pow_nonneg (by norm_num [eeaGrowthBase]) _)

theorem paperStep_coefficients {s : EEAState} (h : s.rPrime ≠ 0) :
    (paperStep s).t = s.tPrime + paperQuotient s * s.t ∧
      (paperStep s).tPrime = s.t := by
  rw [paperStep_nonterminal h]
  exact ⟨rfl, rfl⟩

/-! ## Indexed canonical boundaries -/

/-- A canonical quotient boundary reached after exactly `spent` quotient bits. -/
inductive PaperBoundaryReachable (p x : ℕ) : ℕ → EEAState → Prop where
  | initial : PaperBoundaryReachable p x 0 (paperInitial p x)
  | step {spent : ℕ} {s : EEAState} :
      PaperBoundaryReachable p x spent s →
      s.rPrime ≠ 0 →
      PaperBoundaryReachable p x (spent + (paperQuotient s).size) (paperStep s)

theorem PaperBoundaryReachable.invariant {p x spent : ℕ} {s : EEAState}
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hreach : PaperBoundaryReachable p x spent s) : PaperInvariant p x s := by
  induction hreach with
  | initial => exact paperInitial_invariant hp (by omega) hxp
  | step _ _ ih => exact paperStep_preservesInvariant ih

/-- After the first quotient, the strengthened prefix potential keeps the first-quotient endpoint
factor from Appendix A.2. -/
theorem PaperBoundaryReachable.prefixPotential {p x spent : ℕ} {s : EEAState}
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hreach : PaperBoundaryReachable p x spent s) :
    (spent = 0 ∧ s = paperInitial p x) ∨
      eeaGrowthBase ^ spent * eeaPotential 2 1 ≤
        eeaGrowthBase ^ 2 * eeaPotential s.t s.tPrime := by
  induction hreach with
  | initial => exact Or.inl ⟨rfl, rfl⟩
  | @step spent s hreach hnonterminal ih =>
      right
      have hinvariant := hreach.invariant hp hx hxp
      have hrpPos : 0 < s.rPrime := Nat.pos_of_ne_zero hnonterminal
      have hqPos : 0 < paperQuotient s :=
        Nat.div_pos (le_of_lt hinvariant.remainder_decreases) hrpPos
      have hstep := eeaPotential_step hinvariant.coefficient_increases.le hqPos
      rcases ih with hfirst | hprefix
      · obtain ⟨hspent, hs⟩ := hfirst
        subst spent
        subst s
        have hinitial := paperInitial_invariant hp (by omega) hxp
        have hqTwo : 2 ≤ paperQuotient (paperInitial p x) := by
          apply (Nat.le_div_iff_mul_le (correctedInput_pos (by omega) hxp)).2
          simpa [paperInitial] using
            hinitial.zero_coefficient_balance (by simp [paperInitial])
        obtain ⟨ht, htPrime⟩ := paperStep_coefficients hnonterminal
        rw [ht, htPrime]
        simpa [paperInitial, Nat.cast_add, Nat.cast_mul, add_comm] using
          potential_first_step hqTwo
      · rw [pow_add]
        have hpowNonneg : (0 : ℚ) ≤ eeaGrowthBase ^ spent :=
          pow_nonneg (by norm_num [eeaGrowthBase]) _
        calc
          (eeaGrowthBase ^ spent * eeaGrowthBase ^ (paperQuotient s).size) *
                eeaPotential 2 1 =
              eeaGrowthBase ^ (paperQuotient s).size *
                (eeaGrowthBase ^ spent * eeaPotential 2 1) := by ring
          _ ≤ eeaGrowthBase ^ (paperQuotient s).size *
                (eeaGrowthBase ^ 2 * eeaPotential s.t s.tPrime) :=
            mul_le_mul_of_nonneg_left hprefix
              (pow_nonneg (by norm_num [eeaGrowthBase]) _)
          _ = eeaGrowthBase ^ 2 *
                (eeaGrowthBase ^ (paperQuotient s).size *
                  eeaPotential s.t s.tPrime) := by ring
          _ ≤ eeaGrowthBase ^ 2 *
                eeaPotential (paperStep s).t (paperStep s).tPrime := by
            obtain ⟨ht, htPrime⟩ := paperStep_coefficients hnonterminal
            rw [ht, htPrime]
            apply mul_le_mul_of_nonneg_left
            simpa only [Nat.cast_add, Nat.cast_mul, add_comm] using hstep
            exact pow_nonneg (by norm_num [eeaGrowthBase]) _

/-- Exact rational growth bound at every reachable canonical boundary. -/
theorem PaperBoundaryReachable.prefixGrowth {p x spent : ℕ} {s : EEAState}
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hreach : PaperBoundaryReachable p x spent s) :
    eeaPrefixEta * eeaGrowthBase ^ spent ≤ (s.t : ℚ) := by
  have hinvariant := hreach.invariant hp hx hxp
  rcases hreach.prefixPotential hp hx hxp with hfirst | hpotential
  · obtain ⟨hspent, hs⟩ := hfirst
    subst spent
    subst s
    norm_num [eeaPrefixEta, paperInitial]
  · have hmono : eeaPotential (s.t : ℚ) s.tPrime ≤ eeaPotential s.t s.t :=
      potential_mono le_rfl (by exact_mod_cast hinvariant.coefficient_increases.le)
    rw [potential_diag (by positivity)] at hmono
    have hpowNonneg : (0 : ℚ) ≤ eeaGrowthBase ^ 2 :=
      pow_nonneg (by norm_num [eeaGrowthBase]) _
    have hchain := hpotential.trans (mul_le_mul_of_nonneg_left hmono hpowNonneg)
    have heta : eeaPotential (2 : ℚ) 1 =
        eeaPrefixEta * eeaGrowthBase ^ 2 * potentialDiagCoefficient := by
      norm_num [eeaPotential, eeaPrefixEta, eeaGrowthBase, potentialDiagCoefficient,
        potentialRow0, potentialRow1, potentialRow2, potentialRow3, min_def]
    rw [heta] at hchain
    have hcancelPos : (0 : ℚ) < eeaGrowthBase ^ 2 * potentialDiagCoefficient := by
      norm_num [eeaGrowthBase, potentialDiagCoefficient]
    apply (mul_le_mul_iff_left₀ hcancelPos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hchain

/-- Kernel-checked affine form of Appendix A.2: if `spent` quotient bits precede a reachable
boundary, then `spent < c * size(t) + delta` for exact rational `c` and `delta`. -/
theorem PaperBoundaryReachable.spent_lt_size {p x spent : ℕ} {s : EEAState}
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hreach : PaperBoundaryReachable p x spent s) :
    (spent : ℚ) < eeaWindowSlope * s.t.size + eeaWindowDelta := by
  have hgrowth := hreach.prefixGrowth hp hx hxp
  have htPos : 0 < s.t := by
    have hinvariant := hreach.invariant hp hx hxp
    exact lt_of_le_of_lt (Nat.zero_le _) hinvariant.coefficient_increases
  have htSizeNat : s.t < 2 ^ s.t.size := Nat.lt_size_self _
  have htSize : (s.t : ℚ) < (2 : ℚ) ^ s.t.size := by exact_mod_cast htSizeNat
  by_contra hbound
  have hlinearQ :
      eeaWindowSlope * s.t.size + eeaWindowDelta ≤ (spent : ℚ) := le_of_not_gt hbound
  have hlinearNat : 2089 * s.t.size + 962 ≤ 1323 * spent := by
    have hlinearStrictQ :
        (2089 : ℚ) * s.t.size + 961 < 1323 * spent := by
      norm_num [eeaWindowSlope, eeaWindowDelta] at hlinearQ ⊢
      linarith
    have hlinearStrictNat : 2089 * s.t.size + 961 < 1323 * spent := by
      exact_mod_cast hlinearStrictQ
    omega
  have hbaseOne : (1 : ℚ) ≤ eeaGrowthBase := by norm_num [eeaGrowthBase]
  have hexponent : 2089 * s.t.size + 962 ≤ 1323 * spent := hlinearNat
  have hpowExponent :
      eeaGrowthBase ^ (2089 * s.t.size + 962) ≤
        eeaGrowthBase ^ (1323 * spent) :=
    pow_le_pow_right₀ hbaseOne hexponent
  have hetaNonneg : (0 : ℚ) ≤ eeaPrefixEta ^ 1323 :=
    pow_nonneg (by norm_num [eeaPrefixEta]) _
  have hlower : (2 : ℚ) ^ (1323 * s.t.size) ≤
      eeaPrefixEta ^ 1323 * eeaGrowthBase ^ (1323 * spent) := by
    calc
      (2 : ℚ) ^ (1323 * s.t.size) = ((2 : ℚ) ^ 1323) ^ s.t.size := by
        rw [pow_mul]
      _ ≤ (eeaGrowthBase ^ 2089) ^ s.t.size :=
        pow_le_pow_left₀ (by positivity) window_slope_certificate _
      _ = eeaGrowthBase ^ (2089 * s.t.size) := by rw [pow_mul]
      _ ≤ (eeaPrefixEta ^ 1323 * eeaGrowthBase ^ 962) *
          eeaGrowthBase ^ (2089 * s.t.size) := by
        exact le_mul_of_one_le_left (by positivity) window_delta_certificate
      _ = eeaPrefixEta ^ 1323 *
          eeaGrowthBase ^ (2089 * s.t.size + 962) := by
        rw [pow_add]
        ring
      _ ≤ eeaPrefixEta ^ 1323 * eeaGrowthBase ^ (1323 * spent) :=
        mul_le_mul_of_nonneg_left hpowExponent hetaNonneg
  have hgrowthPow :
      (eeaPrefixEta * eeaGrowthBase ^ spent) ^ 1323 ≤ (s.t : ℚ) ^ 1323 :=
    pow_le_pow_left₀ (by
      exact mul_nonneg (by norm_num [eeaPrefixEta])
        (pow_nonneg (by norm_num [eeaGrowthBase]) _)) hgrowth _
  have hsizePow :
      (s.t : ℚ) ^ 1323 < ((2 : ℚ) ^ s.t.size) ^ 1323 :=
    pow_lt_pow_left₀ htSize (by positivity) (by norm_num)
  have hupper :
      eeaPrefixEta ^ 1323 * eeaGrowthBase ^ (1323 * spent) <
        (2 : ℚ) ^ (1323 * s.t.size) := by
    calc
      eeaPrefixEta ^ 1323 * eeaGrowthBase ^ (1323 * spent) =
          (eeaPrefixEta * eeaGrowthBase ^ spent) ^ 1323 := by
        rw [mul_pow]
        congr 1
        rw [← pow_mul]
        simp only [Nat.mul_comm]
      _ ≤ (s.t : ℚ) ^ 1323 := hgrowthPow
      _ < ((2 : ℚ) ^ s.t.size) ^ 1323 := hsizePow
      _ = (2 : ℚ) ^ (1323 * s.t.size) := by
        rw [← pow_mul]
        simp only [Nat.mul_comm]
  exact (not_lt_of_ge hlower) hupper

/-! ## Weighted quotient clock -/

/-- Total quotient-bit weight remaining in the mathematical run. -/
def paperQuotientWeight (s : EEAState) : ℕ :=
  if s.rPrime = 0 then 0
  else (s.r / s.rPrime).size + paperQuotientWeight (paperStep s)
termination_by s.rPrime
decreasing_by
  exact paperStep_rPrime_lt ‹s.rPrime ≠ 0›

/-- The bit-serial paper schedule spends four microsteps per quotient bit. -/
def paperMicrosteps (s : EEAState) : ℕ := 4 * paperQuotientWeight s

@[simp] theorem paperQuotientWeight_terminal {s : EEAState} (h : s.rPrime = 0) :
    paperQuotientWeight s = 0 := by
  rw [paperQuotientWeight]
  simp [h]

theorem paperQuotientWeight_nonterminal {s : EEAState} (h : s.rPrime ≠ 0) :
    paperQuotientWeight s =
      (paperQuotient s).size + paperQuotientWeight (paperStep s) := by
  rw [paperQuotientWeight]
  simp [h, paperQuotient]

/-- Splitting the run at a reachable boundary partitions the exact quotient-bit clock. -/
theorem PaperBoundaryReachable.spent_add_remaining {p x spent : ℕ} {s : EEAState}
    (hreach : PaperBoundaryReachable p x spent s) :
    spent + paperQuotientWeight s = paperQuotientWeight (paperInitial p x) := by
  induction hreach with
  | initial => simp
  | @step spent s hreach hnonterminal ih =>
      rw [paperQuotientWeight_nonterminal hnonterminal] at ih
      omega

private theorem paperStep_t_le_pow_quotient_size {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) (hnonterminal : s.rPrime ≠ 0) :
    (paperStep s).t ≤ 2 ^ (paperQuotient s).size * s.t := by
  obtain ⟨ht, _⟩ := paperStep_coefficients hnonterminal
  rw [ht]
  have hrpPos : 0 < s.rPrime := Nat.pos_of_ne_zero hnonterminal
  have hqPos : 0 < paperQuotient s :=
    Nat.div_pos (le_of_lt h.remainder_decreases) hrpPos
  have hqSize : paperQuotient s + 1 ≤ 2 ^ (paperQuotient s).size := by
    have := Nat.lt_size_self (paperQuotient s)
    omega
  calc
    s.tPrime + paperQuotient s * s.t ≤
        s.t + paperQuotient s * s.t :=
      Nat.add_le_add_right h.coefficient_increases.le _
    _ = (paperQuotient s + 1) * s.t := by ring
    _ ≤ 2 ^ (paperQuotient s).size * s.t := Nat.mul_le_mul_right _ hqSize

/-- The current coefficient is bounded by the quotient-bit clock already spent. -/
theorem PaperBoundaryReachable.t_le_pow_spent {p x spent : ℕ} {s : EEAState}
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hreach : PaperBoundaryReachable p x spent s) : s.t ≤ 2 ^ spent := by
  induction hreach with
  | initial => simp [paperInitial]
  | @step spent s hreach hnonterminal ih =>
      have hinvariant := hreach.invariant hp hx hxp
      have hstep := paperStep_t_le_pow_quotient_size hinvariant hnonterminal
      calc
        (paperStep s).t ≤ 2 ^ (paperQuotient s).size * s.t := hstep
        _ ≤ 2 ^ (paperQuotient s).size * 2 ^ spent :=
          Nat.mul_le_mul_left _ ih
        _ = 2 ^ (spent + (paperQuotient s).size) := by
          rw [pow_add]
          ring

/-- The current remainder cannot shrink faster than one binary digit per spent quotient bit. -/
theorem PaperBoundaryReachable.modulus_le_pow_spent_mul_r {p x spent : ℕ} {s : EEAState}
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hreach : PaperBoundaryReachable p x spent s) : p ≤ 2 ^ spent * s.r := by
  induction hreach with
  | initial => simp [paperInitial]
  | @step spent s hreach hnonterminal ih =>
      have hinvariant := hreach.invariant hp hx hxp
      have hrpPos : 0 < s.rPrime := Nat.pos_of_ne_zero hnonterminal
      have hremLt : paperRemainder s < s.rPrime := Nat.mod_lt _ hrpPos
      have hdecomp :
          paperQuotient s * s.rPrime + paperRemainder s = s.r := by
        simpa [paperQuotient, paperRemainder, Nat.mul_comm] using
          Nat.div_add_mod s.r s.rPrime
      have hqSize : paperQuotient s + 1 ≤ 2 ^ (paperQuotient s).size := by
        have := Nat.lt_size_self (paperQuotient s)
        omega
      have hrBound : s.r ≤ 2 ^ (paperQuotient s).size * s.rPrime := by
        calc
          s.r = paperQuotient s * s.rPrime + paperRemainder s := hdecomp.symm
          _ ≤ paperQuotient s * s.rPrime + s.rPrime :=
            Nat.add_le_add_left hremLt.le _
          _ = (paperQuotient s + 1) * s.rPrime := by ring
          _ ≤ 2 ^ (paperQuotient s).size * s.rPrime :=
            Nat.mul_le_mul_right _ hqSize
      obtain ⟨hr, _⟩ := paperStep_remainders hnonterminal
      rw [hr]
      calc
        p ≤ 2 ^ spent * s.r := ih
        _ ≤ 2 ^ spent * (2 ^ (paperQuotient s).size * s.rPrime) :=
          Nat.mul_le_mul_left _ hrBound
        _ = 2 ^ (spent + (paperQuotient s).size) * s.rPrime := by
          rw [pow_add]
          ring

/-- The coefficient reached at termination is at most one power of two per quotient bit.  This is
the complementary (upper-growth) clock used to bound the amount of terminal padding. -/
theorem paperRun_t_le_pow_quotientWeight {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) :
    (paperRun s).t ≤ 2 ^ paperQuotientWeight s * s.t := by
  by_cases hterminal : s.rPrime = 0
  · simp [paperRun_of_terminal hterminal, paperQuotientWeight_terminal hterminal]
  · rw [paperRun_of_nonterminal hterminal, paperQuotientWeight_nonterminal hterminal, pow_add]
    have hnext := paperRun_t_le_pow_quotientWeight (paperStep_preservesInvariant h)
    have hstep := paperStep_t_le_pow_quotient_size h hterminal
    calc
      (paperRun (paperStep s)).t ≤
          2 ^ paperQuotientWeight (paperStep s) * (paperStep s).t := hnext
      _ ≤ 2 ^ paperQuotientWeight (paperStep s) *
          (2 ^ (paperQuotient s).size * s.t) :=
        Nat.mul_le_mul_left _ hstep
      _ = (2 ^ (paperQuotient s).size *
          2 ^ paperQuotientWeight (paperStep s)) * s.t := by ring
termination_by s.rPrime
decreasing_by
  exact paperStep_rPrime_lt hterminal

/-- The exact quotient-bit weight is large enough to encode the modulus reached as the final
coefficient. -/
theorem modulus_le_pow_paperQuotientWeight {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x)
    (hxp : x < p) :
    p ≤ 2 ^ paperQuotientWeight (paperInitial p x) := by
  have hinvariant := paperInitial_invariant hp (by omega) hxp
  have hrun := paperRun_t_le_pow_quotientWeight hinvariant
  have hterminal := paperRun_terminal hp hx hxp
  rw [hterminal.2.2.1] at hrun
  simpa [paperInitial] using hrun

/-- Iterating the exact rational certificate lower-bounds the final coefficient potential by the
full quotient-bit weight. -/
theorem paperQuotientWeight_potential {p x : ℕ} {s : EEAState}
    (h : PaperInvariant p x s) :
    eeaGrowthBase ^ paperQuotientWeight s * eeaPotential s.t s.tPrime ≤
      eeaPotential (paperRun s).t (paperRun s).tPrime := by
  by_cases hterminal : s.rPrime = 0
  · simp [paperQuotientWeight_terminal hterminal, paperRun_of_terminal hterminal]
  · rw [paperQuotientWeight_nonterminal hterminal, paperRun_of_nonterminal hterminal, pow_add]
    have hrpPos : 0 < s.rPrime := Nat.pos_of_ne_zero hterminal
    have hqPos : 0 < paperQuotient s :=
      Nat.div_pos (le_of_lt h.remainder_decreases) hrpPos
    have hstep := eeaPotential_step h.coefficient_increases.le hqPos
    have hnextInvariant := paperStep_preservesInvariant h
    have ih := paperQuotientWeight_potential hnextInvariant
    obtain ⟨ht, htPrime⟩ := paperStep_coefficients hterminal
    rw [ht, htPrime] at ih
    have hpowNonneg : (0 : ℚ) ≤ eeaGrowthBase ^ paperQuotientWeight (paperStep s) := by
      exact pow_nonneg (by norm_num [eeaGrowthBase]) _
    calc
      (eeaGrowthBase ^ (paperQuotient s).size *
            eeaGrowthBase ^ paperQuotientWeight (paperStep s)) *
          eeaPotential s.t s.tPrime =
          eeaGrowthBase ^ paperQuotientWeight (paperStep s) *
            (eeaGrowthBase ^ (paperQuotient s).size * eeaPotential s.t s.tPrime) := by
        ring
      _ ≤ eeaGrowthBase ^ paperQuotientWeight (paperStep s) *
          eeaPotential
            ((paperQuotient s : ℚ) * s.t + s.tPrime) s.t :=
        mul_le_mul_of_nonneg_left (by simpa [add_comm] using hstep) hpowNonneg
      _ ≤ eeaPotential (paperRun (paperStep s)).t (paperRun (paperStep s)).tPrime := by
        simpa only [Nat.cast_add, Nat.cast_mul, add_comm] using ih
termination_by s.rPrime
decreasing_by
  exact paperStep_rPrime_lt hterminal

private theorem growth_base_pow_405_gt :
    (2 : ℚ) ^ 256 < eeaGrowthBase ^ 405 := by
  rw [eeaGrowthBase, div_pow, lt_div_iff₀ (by positivity)]
  norm_num [pow_succ]

/-- Any prime modulus below `2^256` has quotient-bit weight at most `405`.  The proof is uniform
over every nonzero input and does not enumerate inputs or trust the supplemental generator. -/
theorem paperQuotientWeight_le_405 {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x)
    (hxp : x < p) (hp256 : p < 2 ^ 256) :
    paperQuotientWeight (paperInitial p x) ≤ 405 := by
  let initial := paperInitial p x
  let final := paperRun initial
  change paperQuotientWeight initial ≤ 405
  have hinvariant : PaperInvariant p x initial :=
    paperInitial_invariant hp (by omega) hxp
  have hfinalInvariant : PaperInvariant p x final :=
    paperRun_preservesInvariant hinvariant
  have hterminal := paperRun_terminal hp hx hxp
  have hfinalT : final.t = p := hterminal.2.2.1
  have hpotential := paperQuotientWeight_potential hinvariant
  have hfinalMono : eeaPotential final.t final.tPrime ≤ eeaPotential (p : ℚ) p := by
    apply potential_mono
    · exact_mod_cast hfinalT.le
    · exact_mod_cast hfinalInvariant.tPrime_le
  rw [potential_diag (by positivity)] at hfinalMono
  have hinitialPotential : eeaPotential (initial.t : ℚ) initial.tPrime =
      (213921524841673820000000000 / 89792691076506134379126793 : ℚ) := by
    simp [initial, paperInitial, potential_axis, potentialAxisCoefficient]
  rw [hinitialPotential] at hpotential
  have hfinalMono' :
      eeaPotential (paperRun initial).t (paperRun initial).tPrime ≤
        (2139215248416738200000 / 578885658046109187361 : ℚ) * p := by
    simpa [final] using hfinalMono
  have hscaled := hpotential.trans hfinalMono'
  have hconstantPos : (0 : ℚ) <
      213921524841673820000000000 / 89792691076506134379126793 := by norm_num
  have hpowers : eeaGrowthBase ^ paperQuotientWeight initial ≤ eeaGrowthBase * p := by
    apply (mul_le_mul_iff_left₀ hconstantPos).mp
    calc
      eeaGrowthBase ^ paperQuotientWeight initial *
          (213921524841673820000000000 / 89792691076506134379126793 : ℚ) ≤
          (2139215248416738200000 / 578885658046109187361 : ℚ) * p := hscaled
      _ = (eeaGrowthBase * p) *
          (213921524841673820000000000 / 89792691076506134379126793 : ℚ) := by
        norm_num [eeaGrowthBase]
        ring
  by_contra hweight
  have h406 : 406 ≤ paperQuotientWeight initial := by omega
  have hbaseOne : (1 : ℚ) ≤ eeaGrowthBase := by norm_num [eeaGrowthBase]
  have hpowMono : eeaGrowthBase ^ 406 ≤
      eeaGrowthBase ^ paperQuotientWeight initial :=
    pow_le_pow_right₀ hbaseOne h406
  have hcancel : eeaGrowthBase ^ 405 ≤ (p : ℚ) := by
    apply (mul_le_mul_iff_right₀ (by norm_num [eeaGrowthBase] : (0 : ℚ) < eeaGrowthBase)).mp
    calc
      eeaGrowthBase * eeaGrowthBase ^ 405 = eeaGrowthBase ^ 406 := by
        rw [show 406 = 405 + 1 by omega, pow_succ]
        ring
      _ ≤ eeaGrowthBase ^ paperQuotientWeight initial := hpowMono
      _ ≤ eeaGrowthBase * p := hpowers
  have hp256Q : (p : ℚ) < (2 : ℚ) ^ 256 := by exact_mod_cast hp256
  exact (not_lt_of_ge hcancel) (hp256Q.trans growth_base_pow_405_gt)

/-- Every valid 256-bit input finishes within the paper's fixed 1,620-microstep horizon. -/
theorem paperMicrosteps_le_1620 {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x)
    (hxp : x < p) (hp256 : p < 2 ^ 256) :
    paperMicrosteps (paperInitial p x) ≤ 1620 := by
  unfold paperMicrosteps
  have := paperQuotientWeight_le_405 hp hx hxp hp256
  omega

/-- Concrete secp256k1 specialization of the uniform fixed-horizon theorem. -/
theorem secp256k1_paperMicrosteps_le_1620 {x : ℕ} (hx : 1 ≤ x) (hxp : x < ShorECDLP.p) :
    paperMicrosteps (paperInitial ShorECDLP.p x) ≤ 1620 := by
  apply paperMicrosteps_le_1620 ShorECDLP.Secp256k1.p_prime hx hxp
  norm_num [ShorECDLP.p]

/-- A secp256k1 EEA run necessarily consumes at least 256 quotient bits. -/
theorem secp256k1_paperQuotientWeight_ge_256 {x : ℕ} (hx : 1 ≤ x)
    (hxp : x < ShorECDLP.p) :
    256 ≤ paperQuotientWeight (paperInitial ShorECDLP.p x) := by
  have hpBound := modulus_le_pow_paperQuotientWeight
    ShorECDLP.Secp256k1.p_prime hx hxp
  have hpLower : 2 ^ 255 < ShorECDLP.p := by norm_num [ShorECDLP.p]
  have hpowers : 2 ^ 255 <
      2 ^ paperQuotientWeight (paperInitial ShorECDLP.p x) :=
    hpLower.trans_le hpBound
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpowers
  omega

/-- Number of terminal microsteps used to fill the fixed 1,620-step schedule. -/
def paperPadding (s : EEAState) : ℕ := 4 * (405 - paperQuotientWeight s)

theorem paperMicrosteps_add_padding {s : EEAState} (h : paperQuotientWeight s ≤ 405) :
    paperMicrosteps s + paperPadding s = 1620 := by
  simp only [paperMicrosteps, paperPadding]
  omega

theorem paperPadding_eq_sub {s : EEAState} (h : paperQuotientWeight s ≤ 405) :
    paperPadding s = 1620 - paperMicrosteps s := by
  have := paperMicrosteps_add_padding h
  omega

theorem paperPadding_dvd_four (s : EEAState) : 4 ∣ paperPadding s := by
  exact dvd_mul_right _ _

/-- The terminal padding of every valid secp256k1 input is at most 596 microsteps. -/
theorem secp256k1_paperPadding_le_596 {x : ℕ} (hx : 1 ≤ x)
    (hxp : x < ShorECDLP.p) :
    paperPadding (paperInitial ShorECDLP.p x) ≤ 596 := by
  unfold paperPadding
  have := secp256k1_paperQuotientWeight_ge_256 hx hxp
  omega

/-! ## Indexed active/padding discriminator -/

/-- Whether a one-based fixed-horizon index is still inside the mathematical EEA run. -/
inductive PaperIndexedMode where
  | active
  | padding
  deriving DecidableEq, Repr

def paperIndexedMode (initial : EEAState) (T : ℕ) : PaperIndexedMode :=
  if T ≤ paperMicrosteps initial then .active else .padding

@[simp] theorem paperIndexedMode_eq_active {initial : EEAState} {T : ℕ} :
    paperIndexedMode initial T = .active ↔ T ≤ paperMicrosteps initial := by
  simp [paperIndexedMode]

@[simp] theorem paperIndexedMode_eq_padding {initial : EEAState} {T : ℕ} :
    paperIndexedMode initial T = .padding ↔ paperMicrosteps initial < T := by
  simp [paperIndexedMode]

/-- A one-based microstep inside one particular reachable Euclidean quotient iteration. -/
structure PaperActiveFrame (p x T : ℕ) where
  spent : ℕ
  boundary : EEAState
  reachable : PaperBoundaryReachable p x spent boundary
  nonterminal : boundary.rPrime ≠ 0
  within : ℕ
  within_pos : 1 ≤ within
  within_le : within ≤ 4 * (paperQuotient boundary).size
  time_eq : T = 4 * spent + within

theorem PaperActiveFrame.start_lt {p x T : ℕ} (frame : PaperActiveFrame p x T) :
    4 * frame.spent < T := by
  calc
    4 * frame.spent < 4 * frame.spent + frame.within := by
      have hpos := frame.within_pos
      omega
    _ = T := frame.time_eq.symm

theorem PaperActiveFrame.le_iteration_end {p x T : ℕ} (frame : PaperActiveFrame p x T) :
    T ≤ 4 * (frame.spent + (paperQuotient frame.boundary).size) := by
  calc
    T = 4 * frame.spent + frame.within := frame.time_eq
    _ ≤ 4 * frame.spent + 4 * (paperQuotient frame.boundary).size :=
      Nat.add_le_add_left frame.within_le _
    _ = 4 * (frame.spent + (paperQuotient frame.boundary).size) := by ring

theorem PaperActiveFrame.mode_eq_active {p x T : ℕ} (frame : PaperActiveFrame p x T) :
    paperIndexedMode (paperInitial p x) T = .active := by
  rw [paperIndexedMode_eq_active]
  rw [paperMicrosteps]
  have hsplit := frame.reachable.spent_add_remaining
  have hsizeRemaining : (paperQuotient frame.boundary).size ≤
      paperQuotientWeight frame.boundary := by
    rw [paperQuotientWeight_nonterminal frame.nonterminal]
    omega
  calc
    T = 4 * frame.spent + frame.within := frame.time_eq
    _ ≤ 4 * frame.spent + 4 * (paperQuotient frame.boundary).size :=
      Nat.add_le_add_left frame.within_le _
    _ ≤ 4 * frame.spent + 4 * paperQuotientWeight frame.boundary :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hsizeRemaining) _
    _ = 4 * (frame.spent + paperQuotientWeight frame.boundary) := by ring
    _ = 4 * paperQuotientWeight (paperInitial p x) := by rw [hsplit]

private theorem paperActiveFrame_exists_from {p x spent T offset : ℕ} {s : EEAState}
    (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hreach : PaperBoundaryReachable p x spent s)
    (htime : T = 4 * spent + offset) (hoffsetPos : 1 ≤ offset)
    (hoffsetLe : offset ≤ 4 * paperQuotientWeight s) :
    Nonempty (PaperActiveFrame p x T) := by
  by_cases hterminal : s.rPrime = 0
  · rw [paperQuotientWeight_terminal hterminal] at hoffsetLe
    omega
  · have hinvariant := hreach.invariant hp hx hxp
    have hrpPos : 0 < s.rPrime := Nat.pos_of_ne_zero hterminal
    have hqPos : 0 < paperQuotient s :=
      Nat.div_pos (le_of_lt hinvariant.remainder_decreases) hrpPos
    have hqSizePos : 1 ≤ (paperQuotient s).size := Nat.size_pos.mpr hqPos
    by_cases hcurrent : offset ≤ 4 * (paperQuotient s).size
    · exact ⟨{
          spent := spent
          boundary := s
          reachable := hreach
          nonterminal := hterminal
          within := offset
          within_pos := hoffsetPos
          within_le := hcurrent
          time_eq := htime }⟩
    · have hremaining : offset - 4 * (paperQuotient s).size ≤
          4 * paperQuotientWeight (paperStep s) := by
        rw [paperQuotientWeight_nonterminal hterminal] at hoffsetLe
        omega
      have hremainingPos : 1 ≤ offset - 4 * (paperQuotient s).size := by omega
      apply paperActiveFrame_exists_from hp hx hxp (hreach.step hterminal)
        (offset := offset - 4 * (paperQuotient s).size)
      · omega
      · exact hremainingPos
      · exact hremaining
termination_by s.rPrime
decreasing_by
  exact paperStep_rPrime_lt hterminal

/-- Every one-based index before termination has a unique-kind active witness at a reachable
canonical boundary.  Phase 5 will refine this witness to the corresponding circuit frame. -/
theorem paperActiveFrame_of_le {p x T : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hTPos : 1 ≤ T) (hTLe : T ≤ paperMicrosteps (paperInitial p x)) :
    Nonempty (PaperActiveFrame p x T) := by
  apply paperActiveFrame_exists_from hp hx hxp PaperBoundaryReachable.initial
      (offset := T)
  · omega
  · exact hTPos
  · simpa [paperMicrosteps] using hTLe

/-- A fixed-horizon index strictly after the mathematical run. -/
structure PaperPaddingFrame (p x T : ℕ) where
  padding : ℕ
  padding_pos : 1 ≤ padding
  time_eq : T = paperMicrosteps (paperInitial p x) + padding

def PaperPaddingFrame.endpoint {p x T : ℕ} (_ : PaperPaddingFrame p x T) : EEAState :=
  paperRun (paperInitial p x)

theorem PaperPaddingFrame.endpoint_terminal {p x T : ℕ} (frame : PaperPaddingFrame p x T) :
    frame.endpoint.rPrime = 0 := paperRun_zero_remainder _

theorem paperPaddingFrame_of_lt {p x T : ℕ}
    (hafter : paperMicrosteps (paperInitial p x) < T) :
    Nonempty (PaperPaddingFrame p x T) := by
  refine ⟨{
    padding := T - paperMicrosteps (paperInitial p x)
    padding_pos := by omega
    time_eq := by omega }⟩

/-- Complete indexed domain used by the reversible fixed-horizon refinement. -/
inductive PaperIndexedFrame (p x T : ℕ) where
  | active (frame : PaperActiveFrame p x T)
  | padding (frame : PaperPaddingFrame p x T)

/-- Every positive schedule index is classified as active or padding; there is no unindexed
terminal-stuttering ambiguity in this domain. -/
theorem paperIndexedFrame_exists {p x T : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (hxp : x < p)
    (hTPos : 1 ≤ T) : Nonempty (PaperIndexedFrame p x T) := by
  by_cases hactive : T ≤ paperMicrosteps (paperInitial p x)
  · obtain ⟨frame⟩ := paperActiveFrame_of_le hp hx hxp hTPos hactive
    exact ⟨.active frame⟩
  · obtain ⟨frame⟩ := paperPaddingFrame_of_lt (by omega :
        paperMicrosteps (paperInitial p x) < T)
    exact ⟨.padding frame⟩

/-! ## Borrowed terminal shift epoch -/

/-- Low nine-bit truth-minus-one shift code after `padding` terminal rotations. -/
def terminalShiftLow (padding : ℕ) : ℕ := (511 + padding) % 512

/-- The borrowed epoch bit after `padding` terminal rotations.  On the only reachable range it is
set exactly between the first and second wraps of the nine-bit low word. -/
def terminalShiftEpoch (padding : ℕ) : Bool := decide (1 ≤ padding ∧ padding ≤ 512)

/-- The three-bit endpoint transposition used to return the borrowed epoch bit. -/
def compressBorrowedEpoch (code : Bool × ℕ) : Bool × ℕ :=
  if code.1 = true ∧ code.2 % 4 = 3 then (false, code.2 - 3)
  else if code.1 = false ∧ code.2 % 4 = 0 then (true, code.2 + 3)
  else code

theorem compressBorrowedEpoch_involutive (code : Bool × ℕ) :
    compressBorrowedEpoch (compressBorrowedEpoch code) = code := by
  rcases code with ⟨epoch, low⟩
  cases epoch with
  | false =>
      by_cases hmod : low % 4 = 0
      · have haddmod : (low + 3) % 4 = 3 := by omega
        simp [compressBorrowedEpoch, hmod, haddmod]
      · simp [compressBorrowedEpoch, hmod]
  | true =>
      by_cases hmod : low % 4 = 3
      · have hlow : 3 ≤ low := by omega
        have hsubmod : (low - 3) % 4 = 0 := by omega
        simp [compressBorrowedEpoch, hmod, hsubmod, Nat.sub_add_cancel hlow]
      · simp [compressBorrowedEpoch, hmod]

/-- At every reachable fixed-horizon endpoint the compression clears the borrowed epoch bit. -/
theorem compress_terminalShiftEpoch_fst {padding : ℕ} (hpadding : padding ≤ 596)
    (hfour : 4 ∣ padding) :
    (compressBorrowedEpoch (terminalShiftEpoch padding, terminalShiftLow padding)).1 = false := by
  obtain ⟨k, rfl⟩ := hfour
  by_cases hk0 : k = 0
  · subst k
    simp [compressBorrowedEpoch, terminalShiftEpoch, terminalShiftLow]
  by_cases hk128 : k ≤ 128
  · have hpos : 1 ≤ 4 * k := by omega
    have hle : 4 * k ≤ 512 := by omega
    have hlow : terminalShiftLow (4 * k) = 4 * k - 1 := by
      simp only [terminalShiftLow]
      omega
    have hlowmod : (4 * k - 1) % 4 = 3 := by omega
    simp [compressBorrowedEpoch, terminalShiftEpoch, hpos, hle, hlow, hlowmod]
  · have hgt : 512 < 4 * k := by omega
    have hnot : ¬(1 ≤ 4 * k ∧ 4 * k ≤ 512) := by omega
    have hlt : 4 * k < 1024 := by omega
    have hlow : terminalShiftLow (4 * k) = 4 * k - 513 := by
      simp only [terminalShiftLow]
      omega
    have hlowmod : (4 * k - 513) % 4 = 3 := by omega
    simp [compressBorrowedEpoch, terminalShiftEpoch, hnot, hlow, hlowmod]

/-- Applying the same endpoint transposition before reverse traversal restores the literal borrowed
epoch/low-word pair. -/
theorem compress_terminalShiftEpoch_restore {padding : ℕ} :
    compressBorrowedEpoch
        (compressBorrowedEpoch (terminalShiftEpoch padding, terminalShiftLow padding)) =
      (terminalShiftEpoch padding, terminalShiftLow padding) :=
  compressBorrowedEpoch_involutive _

/-- Same-term secp256k1 endpoint certificate: the mathematical run plus padding is exactly the
fixed horizon, the endpoint transposition clears the borrowed epoch bit, and applying it again
restores the literal epoch/low-word pair for reverse traversal. -/
theorem secp256k1_terminalPadding_certificate {x : ℕ} (hx : 1 ≤ x)
    (hxp : x < ShorECDLP.p) :
    let initial := paperInitial ShorECDLP.p x
    let padding := paperPadding initial
    paperMicrosteps initial + padding = 1620 ∧
      (compressBorrowedEpoch (terminalShiftEpoch padding, terminalShiftLow padding)).1 = false ∧
      compressBorrowedEpoch
          (compressBorrowedEpoch (terminalShiftEpoch padding, terminalShiftLow padding)) =
        (terminalShiftEpoch padding, terminalShiftLow padding) := by
  dsimp only
  have hweight := paperQuotientWeight_le_405 ShorECDLP.Secp256k1.p_prime hx hxp (by
    norm_num [ShorECDLP.p])
  exact ⟨paperMicrosteps_add_padding hweight,
    compress_terminalShiftEpoch_fst (secp256k1_paperPadding_le_596 hx hxp)
      (paperPadding_dvd_four _),
    compress_terminalShiftEpoch_restore⟩

end ShorECDLP.Paper2607_13816
