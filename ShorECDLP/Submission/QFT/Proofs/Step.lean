import ShorECDLP.Submission.QFT.Proofs.CPhase

/-
# Q2 — the single-target QFT step

`qftCoreMSB` processes one target qubit at a time: `H target`, then the cascade of controlled
phases from the remaining controls onto `target` (`qftPhaseLayer`). This file proves that
step's action on a computational-basis ket.

- **Q2a** (`run_qftPhaseLayer_ket`): the phase cascade multiplies `|s⟩` by a product of
  controlled phases. The `• ket s` result carries the require-and-restore (the shared clean
  ancilla is back to `|0⟩`), which is exactly what keeps the induction's `s anc = false`
  hypothesis alive at each step.
- **Q2b** (`run_qftStep_ket`): `H` splits `target` into its `|0⟩ ± |1⟩` branches, and Q2a
  evaluates the cascade on each — the `|0⟩` branch picks up no phase, the `|1⟩` branch picks
  up the full product. This is the "one QFT digit" the Fourier induction (Q3) composes.
-/

namespace ShorECDLP.Quantum

open scoped Classical

/-- The phase a single controlled-`P(.forward,k)` contributes to `|s⟩`: `exp(i·2π/2^k)` when both the
control `c` and the shared `target` are set, `1` otherwise. -/
noncomputable def cPhaseFactor (s : BasisState) (target c : Wire) (k : Nat) : ℂ :=
  if s c && s target then Complex.exp (Complex.I * (2 * Real.pi / (2 : ℝ) ^ k : ℂ)) else 1

/-- The product of controlled phases a `qftPhaseLayer` contributes to `|s⟩`. -/
noncomputable def layerPhase (s : BasisState) (target : Wire) :
    List Wire → Nat → ℂ
  | [],      _ => 1
  | c :: cs, k => cPhaseFactor s target c k * layerPhase s target cs (k + 1)

/-- **Q2a.** The controlled-phase cascade multiplies `|s⟩` by `layerPhase`, restoring the
shared ancilla. -/
theorem run_qftPhaseLayer_ket
    (target anc : Wire) (s : BasisState)
    (htanc : target ≠ anc) (hsanc : s anc = false) :
    ∀ (cs : List Wire) (k : Nat), anc ∉ cs →
      run (qftPhaseLayer target anc cs k) (ket s)
        = layerPhase s target cs k • ket s := by
  intro cs
  induction cs with
  | nil =>
      intro k _
      simp [qftPhaseLayer, layerPhase]
  | cons c cs ih =>
      intro k hanc
      simp only [List.mem_cons, not_or] at hanc
      obtain ⟨hac, hacs⟩ := hanc
      rw [qftPhaseLayer, run_append,
        run_cPhase_ket k c target anc s (Ne.symm hac) htanc hsanc,
        run_smul, ih (k + 1) hacs, smul_smul, layerPhase, cPhaseFactor]

/-- The layer contributes no phase when the shared `target` wire is `false`. -/
theorem layerPhase_target_false
    (s : BasisState) (target : Wire) (ht : s target = false) :
    ∀ (cs : List Wire) (k : Nat), layerPhase s target cs k = 1 := by
  intro cs
  induction cs with
  | nil => intro k; rfl
  | cons c cs ih => intro k; simp [layerPhase, cPhaseFactor, ht, ih (k + 1)]

/-- **Q2b.** The single-target QFT step: `H` on `target` then the controlled-phase cascade.
`target` must lie outside the controls and the ancilla, and `anc` must be a clean `|0⟩`. -/
theorem run_qftStep_ket
    (target anc : Wire) (cs : List Wire) (k : Nat) (s : BasisState)
    (htanc : target ≠ anc) (hanc : anc ∉ cs) (hsanc : s anc = false) :
    run ([Gate.H target] ++ qftPhaseLayer target anc cs k) (ket s)
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (s[target ↦ false])
        + ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (if s target then (-1 : ℂ) else 1) *
            layerPhase (s[target ↦ true]) target cs k) • ket (s[target ↦ true]) := by
  have hanc0 : (s[target ↦ false]) anc = false := by
    rw [upd_other s target false (Ne.symm htanc)]; exact hsanc
  have hanc1 : (s[target ↦ true]) anc = false := by
    rw [upd_other s target true (Ne.symm htanc)]; exact hsanc
  have hH := applyGate_H_ket target s
  rw [List.singleton_append, run_cons, hH, run_add, run_smul, run_smul,
    run_qftPhaseLayer_ket target anc _ htanc hanc0 cs k hanc,
    run_qftPhaseLayer_ket target anc _ htanc hanc1 cs k hanc,
    layerPhase_target_false (s[target ↦ false]) target (by simp) cs k]
  simp only [one_smul, smul_smul, mul_assoc]

theorem qftPhaseLayer_wellFormed
    (target anc : Wire)
    (cs : List Wire)
    (k : Nat)
    (htanc : target ≠ anc)
    (htcs : target ∉ cs)
    (hanc : anc ∉ cs) :
    CircuitWellFormed (qftPhaseLayer target anc cs k) := by
  induction cs generalizing k with
  | nil =>
      simp [qftPhaseLayer]

  | cons c cs ih =>
      simp only [List.mem_cons, not_or] at htcs hanc
      obtain ⟨htc, htcs⟩ := htcs
      obtain ⟨hac, hacs⟩ := hanc
      rw [qftPhaseLayer, circuitWellFormed_append]
      constructor
      · exact
          cPhase_wellFormed
            k c target anc
            (Ne.symm htc)
            (Ne.symm hac)
            htanc
      · exact ih (k + 1) htcs hacs

theorem qftStep_wellFormed
    (target anc : Wire)
    (cs : List Wire)
    (k : Nat)
    (htanc : target ≠ anc)
    (htcs : target ∉ cs)
    (hanc : anc ∉ cs) :
    CircuitWellFormed
      ([Gate.H target] ++ qftPhaseLayer target anc cs k) := by
  rw [circuitWellFormed_append]

  constructor
  · simp [CircuitWellFormed, Gate.WellFormed]

  · exact
      qftPhaseLayer_wellFormed
        target anc cs k htanc htcs hanc

/--
The exponent accumulated by a phase layer.

For controls `[c₀,c₁,...]` beginning at phase index `k`, this is

    x(c₀) * i 2π/2^k
  + x(c₁) * i 2π/2^(k+1)
  + ...

where a zero control contributes zero.
-/
noncomputable def layerExponent
    (s : BasisState) :
    List Wire → Nat → ℂ
  | [], _ => 0

  | c :: cs, k =>
      (if s c then
        Complex.I * (2 * Real.pi / (2 : ℝ) ^ k : ℂ)
       else 0)
      +
      layerExponent s cs (k + 1)

/--
When `target` is set to `true`, the product of controlled phases is
exactly the exponential of the sum of their phase angles.
-/
theorem layerPhase_set_target_true
    (s : BasisState)
    (target : Wire) :
    ∀ (cs : List Wire) (k : Nat),
      target ∉ cs →
      layerPhase (s[target ↦ true]) target cs k
        =
      Complex.exp (layerExponent s cs k) := by
  intro cs

  induction cs with
  | nil =>
      intro k _
      simp [layerPhase, layerExponent]

  | cons c cs ih =>
      intro k htc

      simp only [List.mem_cons, not_or] at htc
      obtain ⟨htargetc, htargetcs⟩ := htc

      have hct : c ≠ target :=
        Ne.symm htargetc

      cases hc : s c with

      | false =>
          simp [layerPhase, cPhaseFactor, layerExponent, upd, hc, hct,
            ih (k + 1) htargetcs]

      | true =>
          rw [layerPhase]

          have hcontrol :
              (s[target ↦ true]) c = true := by
            simp [upd, hct, hc]

          have htarget :
              (s[target ↦ true]) target = true := by
            simp
          rw [cPhaseFactor]
          simp only [hcontrol, htarget, Bool.true_and, if_true]
          rw [ih (k + 1) htargetcs]
          rw [← Complex.exp_add]
          congr 1
          simp [layerExponent, hc]

/--
Fourier-ready form of the single-target QFT step.

The `|1⟩` branch acquires one combined exponential phase rather than
a recursive product of phases.
-/
theorem run_qftStep_ket_exp
    (target anc : Wire)
    (cs : List Wire)
    (k : Nat)
    (s : BasisState)
    (htanc : target ≠ anc)
    (htcs : target ∉ cs)
    (hanc : anc ∉ cs)
    (hsanc : s anc = false) :
    run ([Gate.H target] ++
        qftPhaseLayer target anc cs k) (ket s)
      =
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        ket (s[target ↦ false])
      +
    (
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        *
      (if s target then (-1 : ℂ) else 1)
        *
      Complex.exp (layerExponent s cs k)
    ) •
      ket (s[target ↦ true]) := by
  rw [run_qftStep_ket target anc cs k s htanc hanc hsanc]
  rw [layerPhase_set_target_true s target cs k htcs]

end ShorECDLP.Quantum
