import ShorECDLP.Submission.QFT.Proofs.Fourier

/-
# QFT — final correctness theorem

The public entry point for the QFT's correctness: the circuit `qft r anc` maps a basis state
`|s⟩` to the normalized Fourier superposition `fourierState r s`. It routes through the Q3
theorem `run_qft_ket`, which proves the product-form QFT core, the Fourier-sum expansion,
and the final bit-reversal step.
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

end ShorECDLP.Quantum
