import ShorECDLP.Submission.QFT.Proofs.Fourier

/-
# QFT — final correctness theorem

The public entry point for the QFT's correctness: the circuit `qft r anc` maps a basis state
`|s⟩` to the normalized Fourier superposition `fourierState r s`. It routes through the Q3
theorem `run_qft_ket`, whose general induction is in progress on the `QFT-work` branch (see
the WIP-scaffold note there — the `sorry` must be discharged before this reaches `main`).
-/

namespace ShorECDLP.Quantum

/-- **QFT correctness.** For a duplicate-free register `r` with a clean ancilla `anc ∉ r`
and `s anc = false`, the QFT circuit produces the Fourier state. -/
theorem qft_correct (r : List Wire) (anc : Wire) (s : BasisState)
    (hanc : anc ∉ r) (hnd : r.Nodup) (hsanc : s anc = false) :
    run (qft r anc) (ket s) = fourierState r s :=
  run_qft_ket r anc s hanc hnd hsanc

end ShorECDLP.Quantum
