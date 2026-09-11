import ShorECDLP.Submission.«2607_13816».Fourier.Semiclassical
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum
noncomputable section
/-- The dyadic Fourier kernel, with the sign carried by the phase direction. -/
def dyadicFourierKernel (dir : PhaseDir) (n x y : Nat) : ℂ :=
  phaseCoeff dir n ^ (x*y)
theorem dyadicFourierKernel_exp (dir : PhaseDir) (n x y : Nat) :
    dyadicFourierKernel dir n x y =
      Complex.exp (Complex.I * ((phaseAngle dir n * (x:ℝ) * (y:ℝ) : ℝ) : ℂ)) := by
  rw [dyadicFourierKernel, phaseCoeff, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
private theorem phaseAngle_double (dir : PhaseDir) (k : Nat) :
    2 * phaseAngle dir (k+1) = phaseAngle dir k := by
  cases dir <;> simp only [phaseAngle, pow_succ] <;> field_simp

theorem dyadicPhase_square (dir : PhaseDir) (k : Nat) :
    phaseCoeff dir (k+1)^2 = phaseCoeff dir k := by
  rw [phaseCoeff, ← Complex.exp_nat_mul, phaseCoeff]
  congr 1
  have h := congrArg (fun r : ℝ => (r:ℂ)) (phaseAngle_double dir k)
  push_cast at h
  push_cast
  rw [mul_left_comm, h]

theorem dyadicPhase_power (dir : PhaseDir) (k m : Nat) :
    phaseCoeff dir (k+m) ^ (2^m) = phaseCoeff dir k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_mul]
    rw [show k+(m+1)=(k+m)+1 by omega]
    rw [← pow_mul, Nat.mul_comm (2^m) 2, pow_mul, dyadicPhase_square, ih]

private theorem dyadicPhase_zero (dir : PhaseDir) : phaseCoeff dir 0 = 1 := by
  cases dir <;> simp [phaseCoeff, phaseAngle, mul_comm Complex.I, Complex.exp_neg, Complex.exp_two_pi_mul_I]
private theorem dyadicPhase_one (dir : PhaseDir) : phaseCoeff dir 1 = -1 := by
  cases dir <;> simp [phaseCoeff, phaseAngle, mul_comm Complex.I, Complex.exp_neg, Complex.exp_pi_mul_I]

theorem dyadicPhase_period (dir : PhaseDir) (n : Nat) : phaseCoeff dir n ^ (2^n) = 1 := by
  simpa only [Nat.zero_add, dyadicPhase_zero] using dyadicPhase_power dir 0 n

theorem dyadicPhase_half_period (dir : PhaseDir) (n : Nat) :
    phaseCoeff dir (n+1) ^ (2^n) = -1 := by
  simpa only [Nat.add_comm 1 n, dyadicPhase_one] using dyadicPhase_power dir 1 n

/-- Split the input's high digit and output's low digit, making bit order explicit. -/
theorem dyadicFourierKernel_split (dir : PhaseDir) (n x y b c : Nat) :
    dyadicFourierKernel dir (n+1) (2^n*b+x) (2*y+c) =
      dyadicFourierKernel dir n x y * phaseCoeff dir (n+1)^(x*c) * (-1:ℂ)^(b*c) := by
  unfold dyadicFourierKernel
  have he : (2^n*b+x)*(2*y+c) = 2^(n+1)*(b*y) + 2*(x*y) + x*c + 2^n*(b*c) := by
    rw [pow_succ]; ring
  rw [he, pow_add, pow_add, pow_add, pow_mul, dyadicPhase_period, one_pow, one_mul,
    pow_mul, dyadicPhase_square]
  rw [pow_mul (phaseCoeff dir (n+1)) (2^n) (b*c), dyadicPhase_half_period]
private theorem fourierHistoryAngle_double (dir : PhaseDir) (bs : List Bool) (k : Nat) :
    2 * fourierHistoryAngle dir bs (k+1) = fourierHistoryAngle dir bs k := by
  induction bs generalizing k with
  | nil => simp [fourierHistoryAngle]
  | cons b bs ih =>
    cases b <;> simp only [fourierHistoryAngle, Bool.false_eq_true, if_false, if_true, zero_add]
    · exact ih (k+1)
    · rw [mul_add, phaseAngle_double, ih]

theorem fourierHistoryAngle_scale (dir : PhaseDir) (bs : List Bool) (k m : Nat) :
    (2:ℝ)^m * fourierHistoryAngle dir bs (k+m) = fourierHistoryAngle dir bs k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, show k+(m+1)=(k+m)+1 by omega,
      fourierHistoryAngle_double, ih]

def fourierWordMSB : List Bool → Nat
  | [] => 0
  | b :: bs => 2^bs.length * b.toNat + fourierWordMSB bs
def fourierWordLSB : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * fourierWordLSB bs
/-- Fourier row obtained by successive Hadamard outcomes and their classical phases. -/
def fourierBitAmplitude (dir : PhaseDir) : List Bool → List Bool → List Bool → ℂ
  | [], _, [] => 1
  | a :: xs, prior, b :: bs =>
      (if a then Complex.exp (Complex.I * (fourierHistoryAngle dir prior 2 : ℂ)) else 1) *
        xResetCoeff b a * fourierBitAmplitude dir xs (b :: prior) bs
  | _, _, _ => 0
def fourierHistoryPhase (dir : PhaseDir) (prior : List Bool) (k x : Nat) : ℂ :=
  Complex.exp (Complex.I * ((fourierHistoryAngle dir prior k * (x:ℝ) : ℝ) : ℂ))
private theorem historyPhase_cons (dir : PhaseDir) (prior : List Bool) (b : Bool) (k x : Nat) :
    fourierHistoryPhase dir (b::prior) k x =
      phaseCoeff dir k ^ (x*b.toNat) * fourierHistoryPhase dir prior (k+1) x := by
  cases b <;> simp only [fourierHistoryPhase, fourierHistoryAngle,
    Bool.false_eq_true, if_false, if_true, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_zero, Nat.mul_one, pow_zero, one_mul, zero_add]
  rw [phaseCoeff, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring
private theorem historyPhase_split (dir : PhaseDir) (prior : List Bool) (n x : Nat) (b : Bool) :
    fourierHistoryPhase dir prior (n+2) (2^n*b.toNat+x) =
      (if b then Complex.exp (Complex.I*(fourierHistoryAngle dir prior 2 : ℂ)) else 1) *
        fourierHistoryPhase dir prior (n+2) x := by
  cases b with
  | false => simp [fourierHistoryPhase]
  | true =>
    simp only [Bool.toNat_true, Nat.mul_one, if_true, fourierHistoryPhase]
    rw [← Complex.exp_add]
    congr 1
    have h := fourierHistoryAngle_scale dir prior 2 n
    rw [Nat.add_comm 2 n] at h
    have hc := congrArg (fun r : ℝ => (r:ℂ)) h
    push_cast at hc ⊢
    rw [mul_add]
    linear_combination Complex.I * hc
private theorem resetCoeff_power (a b : Bool) :
    xResetCoeff b a = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (-1:ℂ)^(a.toNat*b.toNat) := by
  cases a <;> cases b <;> simp [xResetCoeff]
/-- Closed Fourier kernel for each emitted output string, including any earlier history. -/
theorem fourierBitAmplitude_eq (dir : PhaseDir) (xs prior bs : List Bool) (hlen : bs.length=xs.length) :
    fourierBitAmplitude dir xs prior bs =
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^xs.length) *
        dyadicFourierKernel dir xs.length (fourierWordMSB xs) (fourierWordLSB bs) *
        fourierHistoryPhase dir prior (xs.length+1) (fourierWordMSB xs) := by
  induction xs generalizing prior bs with
  | nil =>
    have hb : bs=[] := List.length_eq_zero_iff.mp hlen
    subst bs
    simp [fourierBitAmplitude, fourierWordMSB, fourierWordLSB, dyadicFourierKernel, fourierHistoryPhase]
  | cons a xs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hl : bs.length=xs.length := by simpa using hlen
      rw [fourierBitAmplitude, ih _ bs hl, resetCoeff_power]
      simp only [fourierWordMSB, fourierWordLSB, List.length_cons]
      rw [Nat.add_comm b.toNat (2*fourierWordLSB bs), dyadicFourierKernel_split,
        historyPhase_cons, historyPhase_split, pow_succ]
      ring
private theorem branchCoeff_eq_bitAmplitude (dir : PhaseDir) (ws : List Wire)
    (hws : ws.Nodup) (prior bs : List Bool) (s : BasisState) :
    fourierBranchCoeff dir ws prior bs s = fourierBitAmplitude dir (ws.map s) prior bs := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [fourierBranchCoeff, List.map_cons, fourierBitAmplitude]
      rw [ih hws.tail]
      have hm : ws.map (s[w ↦ false]) = ws.map s := by
        apply List.map_congr_left
        intro v hv
        have hvw : v ≠ w := by intro he; subst v; exact (List.nodup_cons.mp hws).1 hv
        simp [upd, hvw]
      rw [hm]
/-- Physical Kraus branch equals the mathematical dyadic Fourier row on every basis input. -/
theorem fourierBranch_ket_kernel (dir : PhaseDir) (ws : List Wire) (hws : ws.Nodup)
    (bs : List Bool) (hlen : bs.length=ws.length) (s : BasisState) :
    fourierBranch dir ws List.nil bs (ket s) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^ws.length) *
        dyadicFourierKernel dir ws.length (fourierWordMSB (ws.map s)) (fourierWordLSB bs)) •
        ket (fourierClear ws s) := by
  rw [fourierBranch_ket, branchCoeff_eq_bitAmplitude dir ws hws,
    fourierBitAmplitude_eq dir (ws.map s) List.nil bs (by simpa using hlen)]
  simp [fourierHistoryPhase, fourierHistoryAngle]
/-- Mathematical Fourier row followed by measuring and clearing its register.
The linear extension sums amplitudes before taking any Born probabilities. -/
def measuredFourierKernel (dir : PhaseDir) (ws : List Wire) (bs : List Bool) : State →ₗ[ℂ] State :=
  Finsupp.linearCombination ℂ (fun s =>
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^ws.length) *
      dyadicFourierKernel dir ws.length (fourierWordMSB (ws.map s)) (fourierWordLSB bs)) •
      ket (fourierClear ws s))

theorem fourierBranch_eq_kernel (dir : PhaseDir) (ws : List Wire) (hws : ws.Nodup)
    (bs : List Bool) (hlen : bs.length=ws.length) :
    fourierBranch dir ws List.nil bs = measuredFourierKernel dir ws bs := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change fourierBranch dir ws List.nil bs (ket s) = measuredFourierKernel dir ws bs (ket s)
  rw [fourierBranch_ket_kernel dir ws hws bs hlen]
  simp [measuredFourierKernel, ket]
/-- Equality of the complete instruments, retaining all output strings and all interference. -/
theorem semiclassicalFourier_run_kernel (dir : PhaseDir) (ws : List Wire) (hws : ws.Nodup) :
    (semiclassicalFourier dir ws List.nil).run =
      (fourierOutcomes ws.length).map (fun bs => ⟨bs, measuredFourierKernel dir ws bs⟩) := by
  rw [semiclassicalFourier_run]
  apply List.map_congr_left
  intro bs hbs
  rw [fourierBranch_eq_kernel dir ws hws bs ((fourierOutcomes_mem _ _).mp hbs)]

theorem fourierWordLSB_lt (bs : List Bool) : fourierWordLSB bs < 2^bs.length := by
  induction bs with
  | nil => simp [fourierWordLSB]
  | cons b bs ih => cases b <;> simp only [fourierWordLSB, List.length_cons, pow_succ,
      Bool.toNat_false, Bool.toNat_true] <;> omega

theorem fourierWordMSB_lt (bs : List Bool) : fourierWordMSB bs < 2^bs.length := by
  induction bs with
  | nil => simp [fourierWordMSB]
  | cons b bs ih => cases b <;> simp only [fourierWordMSB, List.length_cons, pow_succ,
      Bool.toNat_false, Bool.toNat_true] <;> omega
/-- The product of Hadamard normalizations is the usual inverse square root of the dimension. -/
theorem fourierNormalization (n : Nat) :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^n = ((Real.sqrt ((2:ℝ)^n))⁻¹ : ℝ) := by
  have h : Real.sqrt ((2:ℝ)^n) = Real.sqrt 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  simp [h]

theorem fourierWordLSB_injective (xs ys : List Bool) (hlen : xs.length=ys.length)
    (hv : fourierWordLSB xs=fourierWordLSB ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => simpa using (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hl : xs.length=ys.length := by simpa using hlen
      simp only [fourierWordLSB] at hv
      cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv
      · exact congrArg (false :: ·) (ih ys hl (by omega))
      · omega
      · omega
      · exact congrArg (true :: ·) (ih ys hl (by omega))

theorem fourierWordLSB_surjective (n y : Nat) (hy : y<2^n) :
    ∃ bs : List Bool, bs.length=n ∧ fourierWordLSB bs=y := by
  induction n generalizing y with
  | zero =>
    have h : y=0 := by simpa using hy
    exact ⟨[], rfl, h.symm⟩
  | succ n ih =>
    have hd : y/2<2^n := by rw [pow_succ] at hy; omega
    obtain ⟨bs, hlen, hval⟩ := ih (y/2) hd
    refine ⟨(y%2==1)::bs, by simp [hlen], ?_⟩
    simp only [fourierWordLSB, hval]
    have hm : y%2<2 := Nat.mod_lt _ (by omega)
    by_cases h : y%2=1
    · simp [h, Bool.toNat_true]; omega
    · have hz : y%2=0 := by omega
      simp [hz, Bool.toNat_false]; omega
end
end ShorECDLP.Paper2607_13816
