import ShorECDLP.Submission.QFT.Proofs.Step

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

end ShorECDLP.Quantum
