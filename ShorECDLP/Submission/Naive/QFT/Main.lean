import ShorECDLP.Submission.Naive.QFT.Proofs.Fourier
import ShorECDLP.Submission.Naive.QFT.Proofs.Count

/-
# QFT and inverse QFT — final correctness theorems

The public entry point for the QFT's correctness: the circuit `qft r anc` maps a basis state
`|s⟩` to the normalized Fourier superposition `fourierState r s`. It routes through the Q3
theorem `run_qft_ket`, which proves the product-form QFT core, the Fourier-sum expansion,
and the final bit-reversal step.

The inverse circuit is the generic circuit adjoint of that same `qft` term.
The framework's two-sided adjoint theorem therefore proves exact cancellation
on arbitrary finite-support quantum states, while `iqft_correct` specializes it
to the Fourier state produced by `qft_correct`.
-/

namespace ShorECDLP.Quantum

/-- **QFT correctness.** For a duplicate-free register `r` with a clean ancilla `anc ∉ r`
and `s anc = false`, the QFT circuit produces the Fourier state. -/
theorem qft_correct (r : List Wire) (anc : Wire) (s : BasisState)
    (hanc : anc ∉ r) (hnd : r.Nodup) (hsanc : s anc = false) :
    run (qft r anc) (ket s)
     =
    (((Real.sqrt (2 ^ r.length))⁻¹ : ℝ) : ℂ) •
      ∑ y ∈ Finset.range (2 ^ r.length),
        qftPhase (2 ^ r.length) (regValue r s) y • ket (setReg r y s) :=
  run_qft_ket r anc s hanc hnd hsanc

/-- Applying the inverse QFT after the QFT is the identity on every quantum
state. -/
theorem iqft_qft_cancel
    (r : List Wire) (anc : Wire) (psi : State)
    (hanc : anc ∉ r) (hnd : r.Nodup) :
    run (iqft r anc) (run (qft r anc) psi) = psi := by
  simpa [iqft] using
    run_adjoint_run (qft r anc) (qft_wellFormed r anc hanc hnd) psi

/-- Applying the QFT after the inverse QFT is also the identity on every
quantum state. -/
theorem qft_iqft_cancel
    (r : List Wire) (anc : Wire) (psi : State)
    (hanc : anc ∉ r) (hnd : r.Nodup) :
    run (qft r anc) (run (iqft r anc) psi) = psi := by
  simpa [iqft] using
    run_run_adjoint (qft r anc) (qft_wellFormed r anc hanc hnd) psi

/-- **Inverse-QFT correctness.** The inverse QFT maps the exact Fourier
state produced from `|s⟩` back to `|s⟩`. -/
theorem iqft_correct
    (r : List Wire) (anc : Wire) (s : BasisState)
    (hanc : anc ∉ r) (hnd : r.Nodup) (hsanc : s anc = false) :
    run (iqft r anc) (fourierState r s) = ket s := by
  rw [← run_qft_ket r anc s hanc hnd hsanc]
  exact iqft_qft_cancel r anc (ket s) hanc hnd

end ShorECDLP.Quantum
