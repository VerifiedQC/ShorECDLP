import ShorECDLP.Submission.Naive.QFT.Proofs.Step
import ShorECDLP.Submission.Naive.QFT.Proofs.Swap
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Zip

/-
# Q3 — the QFT Fourier correctness theorem (setup + base cases)

The goal (`run_qft_ket`): for an `r.Nodup` register `r` with a clean ancilla `anc ∉ r`,
```
run (qft r anc) (ket s)
  = (√N)⁻¹ • ∑ y ∈ range N, exp(2πi·x·y/N) • ket (setReg r y s)
```
where `N = 2^(r.length)`, `x = regValue r s`. This file pins the statement (`setReg`,
`qftPhase`, `fourierState`) and proves the base cases; the induction is layered on top.
-/

namespace ShorECDLP.Quantum

open scoped Classical

/-- Write the low `r.length` bits of `y` (LSB-first) into the wires of `r`. -/
def setReg : List Wire → Nat → BasisState → BasisState
  | [],      _, s => s
  | w :: ws, y, s => setReg ws (y / 2) (s[w ↦ (y % 2 == 1)])

/-- The QFT phase `ω^(x·y)` with `ω = exp(2πi/N)`. -/
noncomputable def qftPhase (N x y : Nat) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * (x : ℝ) * (y : ℝ) / (N : ℝ) : ℂ))

/-- The QFT Fourier target state for register `r` in basis state `s`. -/
noncomputable def fourierState (r : List Wire) (s : BasisState) : State :=
  (((Real.sqrt (2 ^ r.length))⁻¹ : ℝ) : ℂ) •
    ∑ y ∈ Finset.range (2 ^ r.length),
      qftPhase (2 ^ r.length) (regValue r s) y • ket (setReg r y s)

@[simp] theorem setReg_nil (y : Nat) (s : BasisState) : setReg [] y s = s := rfl

@[simp] theorem qftPhase_zero_right (N x : Nat) : qftPhase N x 0 = 1 := by
  simp [qftPhase]

/-- **Base case `n = 0`.** The empty register: `qft` is the identity and the Fourier sum has
its single `y = 0` term with phase `1`. -/
theorem run_qft_ket_nil (anc : Wire) (s : BasisState) :
    run (qft [] anc) (ket s) = fourierState [] s := by
  simp [qft, qftCore, qftCoreMSB, bitReverse, fourierState]

/-! ============================================================
    Q3a — one Fourier digit
============================================================ -/



private theorem regValue_append (xs ys : List Wire) (s : BasisState) :
    regValue (xs ++ ys) s = regValue xs s + 2 ^ xs.length * regValue ys s := by
  induction xs with
  | nil => simp [regValue]
  | cons x xs ih =>
      simp only [List.cons_append, regValue_cons, List.length_cons, ih, pow_succ]
      ring

private theorem regValue_reverse_cons (w : Wire) (ws : List Wire) (s : BasisState) :
    regValue (w :: ws).reverse s =
      regValue ws.reverse s + 2 ^ ws.length * (if s w then 1 else 0) := by
  rw [List.reverse_cons, regValue_append]
  simp [regValue]

private theorem layerExponent_succ_eq_regValue (s : BasisState) :
    ∀ (cs : List Wire) (k : Nat),
      layerExponent s cs (k + 1) =
        Complex.I * ((2 * Real.pi * (regValue cs.reverse s : ℝ) /
          (2 : ℝ) ^ (k + cs.length) : ℝ) : ℂ) := by
  intro cs
  induction cs with
  | nil =>
      intro k
      simp [layerExponent]
  | cons c cs ih =>
      intro k
      rw [layerExponent, ih (k + 1), regValue_reverse_cons]
      simp only [List.length_cons]
      have h : k + (cs.length + 1) = (k + 1) + cs.length := by omega
      rw [h, pow_add]
      cases hc : s c
      · simp
      · simp only [if_true]
        push_cast
        field_simp
        ring

private theorem layerExponent_two_eq_regValue (s : BasisState) (cs : List Wire) :
    layerExponent s cs 2 =
      Complex.I * ((2 * Real.pi * (regValue cs.reverse s : ℝ) /
        (2 : ℝ) ^ (cs.length + 1) : ℝ) : ℂ) := by
  simpa [Nat.add_comm] using layerExponent_succ_eq_regValue s cs 1

/--
The Fourier phase contributed by one output qubit of `qftCoreMSB`.
-/
noncomputable def qftDigitPhase
    (qs : List Wire)
    (s : BasisState) : ℂ :=
  qftPhase (2 ^ qs.length) (regValue qs.reverse s) 1

theorem qftExponent_cons (target : Wire) (rest : List Wire) (s : BasisState) :
    Complex.I * ((2 * Real.pi * (regValue (target :: rest).reverse s : ℝ) /
      (2 : ℝ) ^ (target :: rest).length : ℝ) : ℂ) =
    layerExponent s rest 2 +
      if s target then (Real.pi : ℂ) * Complex.I else 0 := by
  rw [layerExponent_two_eq_regValue, regValue_reverse_cons]
  simp only [List.length_cons]
  cases ht : s target
  · simp
  · simp only [if_true]
    push_cast
    rw [pow_succ]
    field_simp

theorem qftStep_phase_eq_digitPhase
    (target : Wire) (rest : List Wire) (s : BasisState)
    (htrest : target ∉ rest) :
    (if s target then (-1 : ℂ) else 1) *
        layerPhase (s[target ↦ true]) target rest 2 =
      qftDigitPhase (target :: rest) s := by
  rw [layerPhase_set_target_true s target rest 2 htrest]
  unfold qftDigitPhase qftPhase
  simp [Nat.cast_pow]
  have harg :
      Complex.I *
          (2 * (Real.pi : ℂ) *
              ((regValue (rest.reverse ++ [target]) s : Nat) : ℂ) /
            (2 : ℂ) ^ (rest.length + 1)) =
        Complex.I *
          ((2 * Real.pi * (regValue (target :: rest).reverse s : ℝ) /
            (2 : ℝ) ^ (target :: rest).length : ℝ) : ℂ) := by
    simp [List.reverse_cons]
  rw [harg]
  rw [qftExponent_cons target rest s]
  cases ht : s target
  · simp
  · simp [Complex.exp_add_pi_mul_I]

/-! ============================================================
    Q3b — product form of the QFT core
============================================================ -/

/--
The textbook product-form QFT state, with output wires still in the
reversed order produced by `qftCoreMSB`.

For `target :: rest`, the target contributes

    1/√2 (|0⟩ + phase · |1⟩),

and the remaining wires recursively contribute the remaining QFT digits.
-/
noncomputable def qftProductMSB :
    List Wire → BasisState → State
  | [], s =>
      ket s

  | target :: rest, s =>
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          qftProductMSB rest (s[target ↦ false])
        +
      (
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
          qftDigitPhase (target :: rest) s
      ) •
          qftProductMSB rest (s[target ↦ true])

theorem run_qftCoreMSB_ket_product
    (qs : List Wire) (anc : Wire) (s : BasisState)
    (hanc : anc ∉ qs) (hnd : qs.Nodup) (hsanc : s anc = false) :
    run (qftCoreMSB anc qs) (ket s) = qftProductMSB qs s := by
  induction qs generalizing s with
  | nil =>
      simp [qftCoreMSB, qftProductMSB]
  | cons target rest ih =>
      simp only [List.mem_cons, not_or] at hanc
      obtain ⟨hancTarget, hancRest⟩ := hanc
      have htanc : target ≠ anc := Ne.symm hancTarget
      have htrest : target ∉ rest := (List.nodup_cons.mp hnd).1
      have hndRest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hclean0 : (s[target ↦ false]) anc = false := by
        rw [upd_other s target false hancTarget]
        exact hsanc
      have hclean1 : (s[target ↦ true]) anc = false := by
        rw [upd_other s target true hancTarget]
        exact hsanc

      rw [qftCoreMSB, run_append]
      rw [run_qftStep_ket target anc rest 2 s htanc hancRest hsanc]
      rw [run_add, run_smul, run_smul]
      rw [ih (s := s[target ↦ false]) hancRest hndRest hclean0]
      rw [ih (s := s[target ↦ true]) hancRest hndRest hclean1]
      rw [qftProductMSB, mul_assoc]
      rw [qftStep_phase_eq_digitPhase target rest s htrest]

/-! ============================================================
    Q3c — Fourier sum before bit reversal
============================================================ -/

/--
The Fourier state produced before the final SWAP network.

The Fourier coefficient is already the standard one; only the output
bits are written into `r.reverse`.
-/
noncomputable def reverseFourierState
    (r : List Wire)
    (s : BasisState) : State :=
  (((Real.sqrt (2 ^ r.length))⁻¹ : ℝ) : ℂ) •
    ∑ y ∈ Finset.range (2 ^ r.length),
      qftPhase (2 ^ r.length) (regValue r s) y
        •
      ket (setReg r.reverse y s)

private noncomputable def qftNorm (n : Nat) : ℂ :=
  (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ) : ℂ)

private theorem qftNorm_succ (n : Nat) :
    qftNorm (n + 1) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * qftNorm n := by
  unfold qftNorm
  norm_cast
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
  rw [hpow]
  rw [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.sqrt_mul (by positivity)]
  field_simp

private theorem setReg_cons_even (w : Wire) (ws : List Wire) (y : Nat) (s : BasisState) :
    setReg (w :: ws) (2 * y) s = setReg ws y (s[w ↦ false]) := by
  simp only [setReg]
  have hdiv : 2 * y / 2 = y := by omega
  have hmod : 2 * y % 2 = 0 := by omega
  rw [hdiv, hmod]
  rfl

private theorem setReg_cons_odd (w : Wire) (ws : List Wire) (y : Nat) (s : BasisState) :
    setReg (w :: ws) (2 * y + 1) s = setReg ws y (s[w ↦ true]) := by
  simp only [setReg]
  have hdiv : (2 * y + 1) / 2 = y := by omega
  have hmod : (2 * y + 1) % 2 = 1 := by omega
  rw [hdiv, hmod]
  rfl

private theorem qftPhase_add_right (N x y z : Nat) :
    qftPhase N x (y + z) = qftPhase N x y * qftPhase N x z := by
  unfold qftPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem qftPhase_double (N x y : Nat) (hN : N ≠ 0) :
    qftPhase (2 * N) x (2 * y) = qftPhase N x y := by
  unfold qftPhase
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  apply congrArg Complex.exp
  apply congrArg (fun z : ℂ => Complex.I * z)
  norm_cast
  field_simp [hNR]
  push_cast
  ring

private theorem qftPhase_add_period_left (N x y q : Nat) (hN : N ≠ 0) :
    qftPhase N (x + q * N) y = qftPhase N x y := by
  unfold qftPhase
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h :
      2 * (Real.pi : ℂ) * (((x + q * N : Nat) : ℝ) : ℂ) *
          (((y : Nat) : ℝ) : ℂ) / (((N : Nat) : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * (((x : Nat) : ℝ) : ℂ) *
            (((y : Nat) : ℝ) : ℂ) / (((N : Nat) : ℝ) : ℂ) +
          (((q * y : Nat) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) := by
    norm_cast
    push_cast
    field_simp [hNR]
  rw [h]
  push_cast
  rw [mul_add, Complex.exp_add]
  have hturn :
      Complex.exp
          (Complex.I * ((((q : Nat) : ℂ) * ((y : Nat) : ℂ)) *
            (2 * (Real.pi : ℂ)))) = 1 := by
    convert Complex.exp_nat_mul_two_pi_mul_I (q * y) using 1 ; push_cast ; ring_nf
  rw [hturn, mul_one]

private theorem qftPhase_cons_even (target : Wire) (rest : List Wire)
    (s : BasisState) (y : Nat) :
    qftPhase (2 ^ (target :: rest).length) (regValue (target :: rest).reverse s) (2 * y) =
      qftPhase (2 ^ rest.length) (regValue rest.reverse s) y := by
  have hp : 2 ^ rest.length ≠ 0 := pow_ne_zero _ (by decide)
  rw [show 2 ^ (target :: rest).length = 2 * 2 ^ rest.length by
    simp [pow_succ, Nat.mul_comm]]
  rw [qftPhase_double (2 ^ rest.length) _ y hp, regValue_reverse_cons]
  cases ht : s target
  · simp
  · simp only [if_true, mul_one]
    simpa [Nat.mul_comm] using
      qftPhase_add_period_left (2 ^ rest.length) (regValue rest.reverse s) y 1 hp

private theorem qftPhase_cons_odd (target : Wire) (rest : List Wire)
    (s : BasisState) (y : Nat) :
    qftPhase (2 ^ (target :: rest).length) (regValue (target :: rest).reverse s) (2 * y + 1) =
      qftDigitPhase (target :: rest) s *
        qftPhase (2 ^ rest.length) (regValue rest.reverse s) y := by
  rw [qftPhase_add_right, qftPhase_cons_even]
  simp [qftDigitPhase, mul_comm]

private theorem sum_range_double_even_odd {α : Type*} [AddCommMonoid α]
    (f : Nat → α) (n : Nat) :
    ∑ y ∈ Finset.range (2 * n), f y =
      ∑ y ∈ Finset.range n, (f (2 * y) + f (2 * y + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ]
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ac_rfl

private theorem fourierSum_cons (target : Wire) (rest : List Wire) (s : BasisState) :
    (∑ y ∈ Finset.range (2 ^ (target :: rest).length),
      qftPhase (2 ^ (target :: rest).length) (regValue (target :: rest).reverse s) y •
        ket (setReg (target :: rest) y s)) =
    (∑ y ∈ Finset.range (2 ^ rest.length),
      qftPhase (2 ^ rest.length) (regValue rest.reverse s) y •
        ket (setReg rest y (s[target ↦ false]))) +
    qftDigitPhase (target :: rest) s •
      (∑ y ∈ Finset.range (2 ^ rest.length),
        qftPhase (2 ^ rest.length) (regValue rest.reverse s) y •
          ket (setReg rest y (s[target ↦ true]))) := by
  let f : Nat → State := fun y =>
    qftPhase (2 ^ (target :: rest).length) (regValue (target :: rest).reverse s) y •
      ket (setReg (target :: rest) y s)
  change (∑ y ∈ Finset.range (2 ^ (target :: rest).length), f y) = _
  have h := sum_range_double_even_odd f (2 ^ rest.length)
  rw [show (∑ y ∈ Finset.range (2 ^ (target :: rest).length), f y) =
      ∑ y ∈  Finset.range (2 ^ rest.length), (f (2 * y) + f (2 * y + 1)) by
    simpa [pow_succ, Nat.mul_comm] using h]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro y hy
    dsimp [f]
    rw [show
        qftPhase (2 ^ (rest.length + 1)) (regValue (target :: rest).reverse s) (2 * y) =
          qftPhase (2 ^ rest.length) (regValue rest.reverse s) y by
      simpa [List.length_cons] using qftPhase_cons_even target rest s y]
    rw [setReg_cons_even]
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [f]
    rw [show
        qftPhase (2 ^ (rest.length + 1)) (regValue (target :: rest).reverse s) (2 * y + 1) =
          qftDigitPhase (target :: rest) s *
            qftPhase (2 ^ rest.length) (regValue rest.reverse s) y by
      simpa [List.length_cons] using qftPhase_cons_odd target rest s y]
    rw [setReg_cons_odd, smul_smul]

private theorem qftProductMSB_eq_fourierSum (qs : List Wire) (s : BasisState)
    (hnd : qs.Nodup) :
    qftProductMSB qs s =
      qftNorm qs.length •
        ∑ y ∈ Finset.range (2 ^ qs.length),
          qftPhase (2 ^ qs.length) (regValue qs.reverse s) y • ket (setReg qs y s) := by
  induction qs generalizing s with
  | nil =>
      simp [qftProductMSB, qftNorm, qftPhase, setReg]
  | cons target rest ih =>
      have htr : target ∉ rest := (List.nodup_cons.mp hnd).1
      have hrnd : rest.Nodup := (List.nodup_cons.mp hnd).2
      have htrrev : target ∉ rest.reverse := by simpa using htr
      have hv0 := regValue_upd_not_mem rest.reverse s target false htrrev
      have hv1 := regValue_upd_not_mem rest.reverse s target true htrrev
      rw [qftProductMSB, ih (s := s[target ↦ false]) hrnd, ih (s := s[target ↦ true]) hrnd]
      rw [hv0, hv1]
      have hnorm :
          qftNorm (target :: rest).length =
            (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * qftNorm rest.length := by
        simpa [List.length_cons] using qftNorm_succ rest.length
      rw [hnorm, fourierSum_cons]
      simp [smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm]
/--
The recursive QFT product form expands to the ordinary Fourier sum,
except that the output bits occur in reversed wire order.

This theorem contains no circuit reasoning. It is the finite-sum /
binary-expansion identity underlying the textbook QFT product formula.
-/
theorem qftProductMSB_reverse_eq_reverseFourier
    (r : List Wire) (s : BasisState) (hnd : r.Nodup) :
    qftProductMSB r.reverse s = reverseFourierState r s := by
  have h := qftProductMSB_eq_fourierSum r.reverse s (by simpa using hnd)
  simpa [reverseFourierState, qftNorm] using h

/-! ============================================================
    Q3d — bit reversal
============================================================ -/

private def swapState (a b : Wire) (s : BasisState) : BasisState :=
  (s[a ↦ s b])[b ↦ s a]

private theorem run_swapPairs_ket
    (ps : List (Wire × Wire)) (s : BasisState)
    (h : ∀ p ∈ ps, p.1 ≠ p.2) :
    run (ps.flatMap fun p => swap p.1 p.2) (ket s) =
      ket (ps.foldl (fun t p => swapState p.1 p.2 t) s) := by
  induction ps generalizing s with
  | nil => simp
  | cons p ps ih =>
      have hp : p.1 ≠ p.2 := h p (by simp)
      have hps : ∀ q ∈ ps, q.1 ≠ q.2 := by
        intro q hq
        exact h q (by simp [hq])
      rw [List.flatMap_cons, run_append, run_swap_ket p.1 p.2 s hp]
      simpa [swapState] using ih (swapState p.1 p.2 s) hps

private def bitPairs (r : List Wire) : List (Wire × Wire) :=
  (r.zip r.reverse).take (r.length / 2)

private theorem zip_append_of_length_eq {α β : Type*}
    (xs : List α) (ys : List β) (xs' : List α) (ys' : List β)
    (h : xs.length = ys.length) :
    (xs ++ xs').zip (ys ++ ys') = xs.zip ys ++ xs'.zip ys' := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [ih ys h]

private theorem take_append_of_le_length' {α : Type*}
    (n : Nat) (xs ys : List α) (h : n ≤ xs.length) :
    (xs ++ ys).take n = xs.take n := by
  exact List.take_append_of_le_length h

private theorem bitPairs_cons_append (a b : Wire) (m : List Wire) :
    bitPairs (a :: (m ++ [b])) = (a, b) :: bitPairs m := by
  have hz : (m ++ [b]).zip (m.reverse ++ [a]) =
      m.zip m.reverse ++ [(b, a)] := by
    simpa using
      zip_append_of_length_eq m m.reverse ([b] : List Wire) ([a] : List Wire) (by simp)
  have hd : (a :: (m ++ [b])).length / 2 = m.length / 2 + 1 := by
    simp
    omega
  have hle : m.length / 2 ≤ (m.zip m.reverse).length := by
    simp
    omega
  unfold bitPairs
  rw [show (a :: (m ++ [b])).reverse = b :: (m.reverse ++ [a]) by simp, hd]
  simp only [List.zip_cons_cons]
  rw [hz]
  change (a, b) :: (m.zip m.reverse ++ [(b, a)]).take (m.length / 2) =
    (a, b) :: (m.zip m.reverse).take (m.length / 2)
  congr 1
  exact take_append_of_le_length' _ _ _ hle

private theorem upd_comm (s : BasisState) (i j : Wire) (bi bj : Bool)
    (h : i ≠ j) : (s[i ↦ bi])[j ↦ bj] = (s[j ↦ bj])[i ↦ bi] := by
  funext x
  by_cases hxi : x = i
  · subst x
    simp [upd, h]
  · by_cases hxj : x = j
    · subst x
      simp [upd, Ne.symm h]
    · simp [upd, hxi, hxj]

private theorem setReg_not_mem (r : List Wire) (y : Nat) (s : BasisState)
    {i : Wire} (hi : i ∉ r) : setReg r y s i = s i := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [setReg]
      rw [ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)]) hi.2]
      exact upd_other s w _ hi.1

private theorem setReg_upd_not_mem (r : List Wire) (y : Nat) (s : BasisState)
    (i : Wire) (b : Bool) (hi : i ∉ r) :
    setReg r y s[i ↦ b] = (setReg r y s)[i ↦ b] := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [setReg]
      rw [upd_comm s i w b (y % 2 == 1) hi.1]
      exact ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)]) hi.2

private theorem div_two_pow (y n : Nat) :
    y / 2 / 2 ^ n = y / 2 ^ (n + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]
  simp [Nat.mul_comm]

private theorem setReg_append (xs ys : List Wire) (y : Nat) (s : BasisState) :
    setReg (xs ++ ys) y s =
      setReg ys (y / 2 ^ xs.length) (setReg xs y s) := by
  induction xs generalizing y s with
  | nil => simp [setReg]
  | cons w ws ih =>
      simp only [List.cons_append, List.length_cons, setReg]
      rw [ih, div_two_pow]

private theorem setReg_cons_append_outer (a b : Wire) (m : List Wire)
    (y : Nat) (s : BasisState) (hb : b ∉ m) :
    setReg (a :: (m ++ [b])) y s =
      setReg m (y / 2)
        ((s[a ↦ (y % 2 == 1)])
          [b ↦ ((y / 2 ^ (m.length + 1)) % 2 == 1)]) := by
  rw [setReg, setReg_append, div_two_pow]
  simp only [setReg]
  exact (setReg_upd_not_mem m (y / 2) (s[a ↦ (y % 2 == 1)]) b
    ((y / 2 ^ (m.length + 1)) % 2 == 1) hb).symm

private theorem setReg_reverse_cons_append_outer (a b : Wire) (m : List Wire)
    (y : Nat) (s : BasisState) (ha : a ∉ m) :
    setReg (a :: (m ++ [b])).reverse y s =
      setReg m.reverse (y / 2)
        ((s[b ↦ (y % 2 == 1)])
          [a ↦ ((y / 2 ^ (m.length + 1)) % 2 == 1)]) := by
  have ha' : a ∉ m.reverse := by simpa using ha
  simpa using setReg_cons_append_outer b a m.reverse y s ha'

private theorem swapState_setReg_not_mem (r : List Wire) (y : Nat)
    (s : BasisState) (a b : Wire) (ha : a ∉ r) (hb : b ∉ r) :
    swapState a b (setReg r y s) = setReg r y (swapState a b s) := by
  unfold swapState
  rw [setReg_not_mem r y s hb, setReg_not_mem r y s ha]
  rw [setReg_upd_not_mem r y (s[a ↦ s b]) b (s a) hb]
  rw [setReg_upd_not_mem r y s a (s b) ha]

private theorem swapState_outer_updates (a b : Wire) (s : BasisState)
    (lo hi : Bool) (hab : a ≠ b) :
    swapState a b ((s[b ↦ lo])[a ↦ hi]) = (s[a ↦ lo])[b ↦ hi] := by
  funext i
  by_cases hia : i = a
  · subst i
    simp [swapState, upd, Ne.symm hab]
  · by_cases hib : i = b
    · subst i
      simp [swapState, upd]
    · simp [swapState, upd, hia, hib]

private theorem swapState_setReg_reverse_outer (a b : Wire) (m : List Wire)
    (y : Nat) (s : BasisState) (ha : a ∉ m) (hb : b ∉ m) (hab : a ≠ b) :
    swapState a b (setReg (a :: (m ++ [b])).reverse y s) =
      setReg m.reverse (y / 2)
        ((s[a ↦ (y % 2 == 1)])
          [b ↦ ((y / 2 ^ (m.length + 1)) % 2 == 1)]) := by
  have ha' : a ∉ m.reverse := by simpa using ha
  have hb' : b ∉ m.reverse := by simpa using hb
  rw [setReg_reverse_cons_append_outer a b m y s ha]
  rw [swapState_setReg_not_mem m.reverse (y / 2) _ a b ha' hb']
  rw [swapState_outer_updates a b s _ _ hab]

private theorem bitReversePairs_distinct (r : List Wire) (hnd : r.Nodup) :
    ∀ p ∈ (r.zip r.reverse).take (r.length / 2), p.1 ≠ p.2 := by
  change ∀ p ∈ bitPairs r, p.1 ≠ p.2
  revert hnd
  induction r using List.bidirectionalRecOn with
  | H0 =>
      intro hnd
      simp [bitPairs]
  | H1 a =>
      intro hnd
      simp [bitPairs]
  | Hn a m b ih =>
      intro hnd
      have haTail : a ∉ m ++ [b] := (List.nodup_cons.mp hnd).1
      have htail : (m ++ [b]).Nodup := (List.nodup_cons.mp hnd).2
      have hndm : m.Nodup := htail.of_append_left
      have hab : a ≠ b := by
        intro h
        subst b
        exact haTail (by simp)
      rw [bitPairs_cons_append]
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hab
      · exact ih hndm p hp

private theorem foldl_bitReversePairs_setReg
    (r : List Wire) (y : Nat) (s : BasisState) (hnd : r.Nodup) :
    ((r.zip r.reverse).take (r.length / 2)).foldl
        (fun t p => swapState p.1 p.2 t) (setReg r.reverse y s) =
      setReg r y s := by
  change (bitPairs r).foldl (fun t p => swapState p.1 p.2 t)
    (setReg r.reverse y s) = setReg r y s
  revert y s hnd
  induction r using List.bidirectionalRecOn with
  | H0 =>
      intro y s hnd
      simp [bitPairs]
  | H1 a =>
      intro y s hnd
      simp [bitPairs]
  | Hn a m b ih =>
      intro y s hnd
      have haTail : a ∉ m ++ [b] := (List.nodup_cons.mp hnd).1
      have htail : (m ++ [b]).Nodup := (List.nodup_cons.mp hnd).2
      have hndm : m.Nodup := htail.of_append_left
      have ha : a ∉ m := by
        intro h
        exact haTail (by simp [h])
      have hb : b ∉ m := by
        have hd : m.Disjoint [b] := (List.nodup_append'.mp htail).2.2
        simpa using hd
      have hab : a ≠ b := by
        intro h
        subst b
        exact haTail (by simp)
      rw [bitPairs_cons_append]
      simp only [List.foldl_cons]
      rw [swapState_setReg_reverse_outer a b m y s ha hb hab]
      rw [ih (y / 2)
        ((s[a ↦ (y % 2 == 1)])
          [b ↦ ((y / 2 ^ (m.length + 1)) % 2 == 1)]) hndm]
      exact (setReg_cons_append_outer a b m y s hb).symm
/--
The final SWAP network turns the reversed output encoding into the
ordinary LSB-first register encoding.

This is the register-level correctness theorem for `bitReverse`.
-/
theorem run_bitReverse_setReg_reverse_ket
    (r : List Wire) (y : Nat) (s : BasisState) (hnd : r.Nodup) :
    run (bitReverse r) (ket (setReg r.reverse y s)) =
      ket (setReg r y s) := by
  rw [bitReverse]
  rw [run_swapPairs_ket _ _ (bitReversePairs_distinct r hnd)]
  rw [foldl_bitReversePairs_setReg r y s hnd]
/--
Applying the final bit-reversal network to the reversed Fourier state
produces the final Fourier state.
-/
theorem run_bitReverse_reverseFourierState
    (r : List Wire)
    (s : BasisState)
    (hnd : r.Nodup) :
    run (bitReverse r) (reverseFourierState r s)
      =
    fourierState r s := by
  unfold reverseFourierState fourierState

  rw [run_smul]

  apply congrArg
    (fun ψ : State =>
      (((Real.sqrt (2 ^ r.length))⁻¹ : ℝ) : ℂ) • ψ)

  rw [map_sum]

  apply Finset.sum_congr rfl
  intro y hy

  rw [run_smul]
  rw [run_bitReverse_setReg_reverse_ket r y s hnd]

/--
**Q3 — exact Fourier correctness of the concrete QFT.**
-/
theorem run_qft_ket
    (r : List Wire)
    (anc : Wire)
    (s : BasisState)
    (hanc : anc ∉ r)
    (hnd : r.Nodup)
    (hsanc : s anc = false) :
    run (qft r anc) (ket s) =
      fourierState r s := by

  have hanc_rev : anc ∉ r.reverse := by
    simpa using hanc

  have hnd_rev : r.reverse.Nodup := by
    simpa using hnd

  rw [qft, run_append]
  rw [qftCore]
  rw [run_qftCoreMSB_ket_product r.reverse anc s hanc_rev hnd_rev hsanc]
  rw [qftProductMSB_reverse_eq_reverseFourier r s hnd]
  exact run_bitReverse_reverseFourierState r s hnd

end ShorECDLP.Quantum
