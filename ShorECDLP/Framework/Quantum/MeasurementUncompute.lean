import ShorECDLP.Framework.Quantum.CoherentRefinement

/-!
# Measurement-based uncomputation

X-basis measurement resets a computational-basis register, but a transcript
`b` leaves the phase `(-1)^(b · y)` when the old register value was `y`.
This module makes that rule exact for a list of wires and proves the generic
phase-correction interface used by the space-efficient submission.

The correction interface has two layers.  `measureResetWithCorrection_coherent`
accepts any classically selected circuit that supplies the required phase.
`recomputeZCorrection_phase` constructs such a circuit by recomputing the old
register, applying transcript-selected Pauli-Z gates, and uncomputing again.
-/

namespace ShorECDLP.Quantum

noncomputable section

/-- Pauli-Z expressed using the existing Clifford gates. -/
def pauliZ (target : Wire) : Circuit :=
  [.H target, .X target, .H target]

private theorem invSqrtTwo_mul_self :
    ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) =
      (1 / 2 : ℂ) := by
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hr :
      (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    field_simp [hsqrt_ne]
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) :=
      Real.mul_self_sqrt (by norm_num)
    nlinarith
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa using hc

private theorem upd_twice
    (s : BasisState) (target : Wire) (first second : Bool) :
    s[target ↦ first][target ↦ second] = s[target ↦ second] := by
  funext i
  by_cases hi : i = target
  · subst i
    simp
  · simp [upd, hi]

private theorem upd_eq_self
    (s : BasisState) (target : Wire) (bit : Bool)
    (h : s target = bit) :
    s[target ↦ bit] = s := by
  funext i
  by_cases hi : i = target
  · subst i
    simpa using h.symm
  · simp [upd, hi]

/-- Exact action of Pauli-Z on a computational-basis ket. -/
theorem run_pauliZ_ket
    (target : Wire) (s : BasisState) :
    Quantum.run (pauliZ target) (ket s) =
      (if s target then -1 else 1) • ket s := by
  simp only [pauliZ, run_cons, run_nil]
  rw [applyGate_H_ket]
  rw [applyGate_add, applyGate_smul, applyGate_smul]
  rw [applyGate_X_ket, applyGate_X_ket]
  rw [applyGate_add, applyGate_smul, applyGate_smul]
  rw [applyGate_H_ket, applyGate_H_ket]
  cases htarget : s target <;>
    simp [htarget, upd_twice, upd_eq_self, smul_smul]
  <;> rw [invSqrtTwo_mul_self]
  <;> module

@[simp]
theorem pauliZ_wellFormed (target : Wire) :
    CircuitWellFormed (pauliZ target) := by
  simp [pauliZ, CircuitWellFormed, Gate.WellFormed]

/-- Controlled-Z expressed using the existing Clifford gates. -/
def controlledZ (control target : Wire) : Circuit :=
  [.H target, .CX control target, .H target]

/-- Exact action of controlled-Z on a computational-basis ket. -/
theorem run_controlledZ_ket
    (control target : Wire)
    (s : BasisState)
    (hct : control ≠ target) :
    Quantum.run (controlledZ control target) (ket s) =
      (if s control && s target then -1 else 1) • ket s := by
  simp only [controlledZ, run_cons, run_nil]
  rw [applyGate_H_ket]
  rw [applyGate_add, applyGate_smul, applyGate_smul]
  rw [applyGate_CX_ket, applyGate_CX_ket]
  rw [applyGate_add, applyGate_smul, applyGate_smul]
  rw [applyGate_H_ket, applyGate_H_ket]
  by_cases ht : s target
  · have hs1 : s[target ↦ true] = s := upd_eq_self s target true ht
    cases hc : s control <;>
      simp [hc, ht, hct, upd, upd_twice, hs1, smul_smul]
    <;> rw [invSqrtTwo_mul_self]
    <;> module
  · have ht' : s target = false := Bool.eq_false_of_not_eq_true ht
    have hs0 : s[target ↦ false] = s := upd_eq_self s target false ht'
    cases hc : s control <;>
      simp [hc, ht, hct, upd, upd_twice, hs0, smul_smul]
    <;> rw [invSqrtTwo_mul_self]
    <;> module

/-- Controlled-Z is physically well formed when its wires differ. -/
theorem controlledZ_wellFormed
    (control target : Wire)
    (hct : control ≠ target) :
    CircuitWellFormed (controlledZ control target) := by
  simp [controlledZ, CircuitWellFormed, Gate.WellFormed, hct]

/-- Reset every listed wire to `false`, in list order. -/
def clearRegister : List Wire → BasisState → BasisState
  | [], s => s
  | target :: targets, s =>
      clearRegister targets (s[target ↦ false])

/-- Linear extension of computational-basis register clearing.  It is used
only on validity subspaces where the erased value is recoverable. -/
def clearRegisterMap (targets : List Wire) : State →ₗ[ℂ] State :=
  Finsupp.linearCombination ℂ (fun s => ket (clearRegister targets s))

@[simp]
theorem clearRegisterMap_ket
    (targets : List Wire) (s : BasisState) :
    clearRegisterMap targets (ket s) = ket (clearRegister targets s) := by
  classical
  simp [clearRegisterMap, ket]

private theorem clearRegister_apply_not_mem
    (targets : List Wire)
    (s : BasisState)
    (wire : Wire)
    (hwire : wire ∉ targets) :
    clearRegister targets s wire = s wire := by
  induction targets generalizing s with
  | nil => rfl
  | cons target targets ih =>
      simp only [List.mem_cons, not_or] at hwire
      rw [clearRegister, ih (s := s[target ↦ false]) hwire.2]
      exact upd_other s target false hwire.1

private theorem clearRegister_apply_mem
    (targets : List Wire)
    (s : BasisState)
    (wire : Wire)
    (hwire : wire ∈ targets) :
    clearRegister targets s wire = false := by
  induction targets generalizing s with
  | nil => simp at hwire
  | cons target targets ih =>
      rw [clearRegister]
      rcases List.mem_cons.mp hwire with heq | htail
      · subst wire
        by_cases htarget : target ∈ targets
        · exact ih (s := s[target ↦ false]) htarget
        · rw [clearRegister_apply_not_mem targets _ target htarget]
          simp
      · exact ih (s := s[target ↦ false]) htail

/-- Clearing a register makes all its listed wires clean. -/
theorem clearRegister_clean
    (targets : List Wire)
    (s : BasisState) :
    Clean targets (clearRegister targets s) := by
  intro wire hwire
  exact clearRegister_apply_mem targets s wire hwire

/-- The sign `(-1)^(b · y)` for transcript `b` and the old bits `y` read from
`targets`.  Mismatched lists are truncated, like `List.zipWith`. -/
def registerXPhase
    (targets : List Wire) (outcomes : List Bool) (s : BasisState) : ℂ :=
  match targets, outcomes with
  | target :: targets, outcome :: outcomes =>
      (if outcome && s target then -1 else 1) *
        registerXPhase targets outcomes s
  | _, _ => 1

/-- The input-independent magnitude `2^(-m/2)`, represented exactly as
`(1 / sqrt 2)^m`. -/
def registerXResetMagnitude (m : Nat) : ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ m

/-- The raw coefficient of a complete register X-measure/reset branch. -/
def registerXResetCoeff :
    List Wire → List Bool → BasisState → ℂ
  | [], [], _ => 1
  | target :: targets, outcome :: outcomes, s =>
      xResetCoeff outcome (s target) *
        registerXResetCoeff targets outcomes s
  | _, _, _ => 0

/-- The raw register coefficient is exactly
`2^(-m/2) * (-1)^(b · y)`. -/
theorem registerXResetCoeff_eq_magnitude_mul_phase
    (targets : List Wire)
    (outcomes : List Bool)
    (s : BasisState)
    (hlength : outcomes.length = targets.length) :
    registerXResetCoeff targets outcomes s =
      registerXResetMagnitude targets.length *
        registerXPhase targets outcomes s := by
  induction targets generalizing outcomes s with
  | nil =>
      cases outcomes <;> simp_all [registerXResetCoeff,
        registerXResetMagnitude, registerXPhase]
  | cons target targets ih =>
      cases outcomes with
      | nil => simp at hlength
      | cons outcome outcomes =>
          have hlength' : outcomes.length = targets.length := by
            simpa using hlength
          rw [registerXResetCoeff, ih outcomes s hlength']
          simp only [registerXResetMagnitude, registerXPhase,
            List.length_cons, pow_succ, xResetCoeff]
          ring

private theorem registerXPhase_mul_self
    (targets : List Wire)
    (outcomes : List Bool)
    (s : BasisState) :
    registerXPhase targets outcomes s *
        registerXPhase targets outcomes s = 1 := by
  induction targets generalizing outcomes with
  | nil => simp [registerXPhase]
  | cons target targets ih =>
      cases outcomes with
      | nil => simp [registerXPhase]
      | cons outcome outcomes =>
          rw [registerXPhase]
          rw [mul_mul_mul_comm]
          rw [ih]
          cases outcome <;> cases s target <;> norm_num

private theorem registerXResetCoeff_upd_not_mem
    (targets : List Wire)
    (outcomes : List Bool)
    (s : BasisState)
    (wire : Wire)
    (bit : Bool)
    (hwire : wire ∉ targets) :
    registerXResetCoeff targets outcomes s[wire ↦ bit] =
      registerXResetCoeff targets outcomes s := by
  induction targets generalizing outcomes s with
  | nil => cases outcomes <;> rfl
  | cons target targets ih =>
      simp only [List.mem_cons, not_or] at hwire
      cases outcomes with
      | nil => rfl
      | cons outcome outcomes =>
          rw [registerXResetCoeff, registerXResetCoeff]
          rw [upd_other s wire bit (fun h => hwire.1 h.symm)]
          rw [ih outcomes s hwire.2]

/-- Sequential Kraus map for measuring/resetting `targets` with the aligned
outcome list. -/
def xResetRegisterKraus :
    List Wire → List Bool → State →ₗ[ℂ] State
  | [], [] => LinearMap.id
  | target :: targets, outcome :: outcomes =>
      (xResetRegisterKraus targets outcomes).comp
        (xResetKraus target outcome)
  | _, _ => 0

/-- Exact register X-measure/reset rule on a computational-basis ket. -/
theorem xResetRegisterKraus_ket
    (targets : List Wire)
    (outcomes : List Bool)
    (s : BasisState)
    (hlength : outcomes.length = targets.length)
    (hnodup : targets.Nodup) :
    xResetRegisterKraus targets outcomes (ket s) =
      registerXResetCoeff targets outcomes s •
        ket (clearRegister targets s) := by
  induction targets generalizing outcomes s with
  | nil =>
      cases outcomes <;> simp_all [xResetRegisterKraus,
        registerXResetCoeff, clearRegister]
  | cons target targets ih =>
      cases outcomes with
      | nil => simp at hlength
      | cons outcome outcomes =>
          have hlength' : outcomes.length = targets.length := by
            simpa using hlength
          have htarget : target ∉ targets := (List.nodup_cons.mp hnodup).1
          have htargets : targets.Nodup := (List.nodup_cons.mp hnodup).2
          rw [xResetRegisterKraus]
          simp only [LinearMap.comp_apply]
          rw [xResetKraus_ket, map_smul]
          rw [ih outcomes (s[target ↦ false]) hlength' htargets]
          rw [registerXResetCoeff_upd_not_mem targets outcomes
            s target false htarget]
          simp [registerXResetCoeff, clearRegister, smul_smul]

private theorem xResetRegisterKraus_apply_eq_zero_of_not_clean
    (targets : List Wire)
    (outcomes : List Bool)
    (psi : State)
    (hlength : outcomes.length = targets.length)
    (hnodup : targets.Nodup)
    (u : BasisState)
    (hu : ¬ Clean targets u) :
    xResetRegisterKraus targets outcomes psi u = 0 := by
  induction psi using Finsupp.induction_linear with
  | zero => simp
  | add psi phi ihpsi ihphi =>
      rw [map_add]
      simp [ihpsi, ihphi]
  | single s coefficient =>
      have hsingle :
          Finsupp.single s coefficient = coefficient • ket s := by
        ext v
        simp [ket]
      rw [hsingle, map_smul,
        xResetRegisterKraus_ket targets outcomes s hlength hnodup]
      have hne : clearRegister targets s ≠ u := by
        intro h
        apply hu
        rw [← h]
        exact clearRegister_clean targets s
      have hket : ket (clearRegister targets s) u = 0 := ket_ne hne
      simp [hket]

/-- Register X-measure/reset releases every target: for an arbitrary input
state, every basis state with nonzero output amplitude is clean on the whole
measured register. -/
theorem xResetRegisterKraus_clean
    (targets : List Wire)
    (outcomes : List Bool)
    (psi : State)
    (hlength : outcomes.length = targets.length)
    (hnodup : targets.Nodup) :
    ∀ u, xResetRegisterKraus targets outcomes psi u ≠ 0 →
      Clean targets u := by
  intro u hu
  by_contra hclean
  exact hu (xResetRegisterKraus_apply_eq_zero_of_not_clean
    targets outcomes psi hlength hnodup u hclean)

/-- All length-`m` Boolean transcripts, in the interpreter's false-first
branch order. -/
def boolTranscripts : Nat → List (List Bool)
  | 0 => [[]]
  | m + 1 =>
      (boolTranscripts m).map (false :: ·) ++
        (boolTranscripts m).map (true :: ·)

theorem mem_boolTranscripts_length
    {m : Nat} {outcomes : List Bool}
    (hmem : outcomes ∈ boolTranscripts m) :
    outcomes.length = m := by
  induction m generalizing outcomes with
  | zero => simpa [boolTranscripts] using hmem
  | succ m ih =>
      simp only [boolTranscripts, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨tail, htail, rfl⟩ | ⟨tail, htail, rfl⟩ <;>
        simp [ih htail]

@[simp]
theorem boolTranscripts_length (m : Nat) :
    (boolTranscripts m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [boolTranscripts, List.length_append, List.length_map,
        ih, pow_succ]
      omega

/-- Adaptive X-measure/reset of a whole register, followed by a circuit chosen
from the complete chronological transcript. -/
def measureResetWithCorrection :
    List Wire → (List Bool → Circuit) → AdaptiveCircuit
  | [], correction => .unitary (correction []) .done
  | target :: targets, correction =>
      .xMeasureReset target
        (measureResetWithCorrection targets
          (fun outcomes => correction (false :: outcomes)))
        (measureResetWithCorrection targets
          (fun outcomes => correction (true :: outcomes)))

private def correctedRegisterBranch
    (targets : List Wire)
    (correction : List Bool → Circuit)
    (outcomes : List Bool) : InstrumentBranch where
  history := outcomes
  kraus := (Quantum.run (correction outcomes)).comp
    (xResetRegisterKraus targets outcomes)

/-- The interpreter produces one corrected branch for every transcript, in
false-first lexicographic order. -/
theorem run_measureResetWithCorrection
    (targets : List Wire)
    (correction : List Bool → Circuit) :
    (measureResetWithCorrection targets correction).run =
      (boolTranscripts targets.length).map
        (correctedRegisterBranch targets correction) := by
  induction targets generalizing correction with
  | nil =>
      simp [measureResetWithCorrection, boolTranscripts,
        correctedRegisterBranch, xResetRegisterKraus]
  | cons target targets ih =>
      simp only [measureResetWithCorrection, AdaptiveCircuit.run]
      rw [ih, ih]
      simp only [List.length_cons, boolTranscripts,
        List.map_append, List.map_map]
      congr 1

/-- A correction family supplies exactly the transcript-dependent sign on the
surviving basis state after the measured register has been cleared. -/
def RegisterXPhaseCorrectionOn
    (targets : List Wire)
    (correction : List Bool → Circuit)
    (Valid : BasisState → Prop) : Prop :=
  ∀ outcomes, outcomes.length = targets.length →
    ∀ s, Valid s →
      Quantum.run (correction outcomes)
          (ket (clearRegister targets s)) =
        registerXPhase targets outcomes s •
          ket (clearRegister targets s)

private theorem forall₂_map_same
    {α β γ : Type*}
    {relation : β → γ → Prop}
    (f : α → β) (g : α → γ)
    (xs : List α)
    (h : ∀ x ∈ xs, relation (f x) (g x)) :
    List.Forall₂ relation (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      exact .cons (h x (by simp))
        (ih fun y hy => h y (by simp [hy]))

private theorem normSq_registerXResetMagnitude (m : Nat) :
    Complex.normSq (registerXResetMagnitude m) = (1 / 2 : ℝ) ^ m := by
  let h : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  have hnorm : Complex.normSq h = 1 / 2 := by
    have hx := normSq_xResetKraus_ket 0 false zeroBasisState
    have hsmul : normSq (h • ket zeroBasisState) =
        Complex.normSq h * normSq (ket zeroBasisState) := by
      unfold normSq
      rw [inner_smul_smul]
      rw [← Complex.normSq_eq_conj_mul_self]
      simp
    rw [xResetKraus_ket] at hx
    have hzero : zeroBasisState[0 ↦ false] = zeroBasisState := by
      funext i
      simp [zeroBasisState, upd]
    rw [hzero] at hx
    have hx' : normSq (h • ket zeroBasisState) = 1 / 2 := by
      simpa [h, xResetCoeff, zeroBasisState, upd] using hx
    rw [hsmul, normSq_ket, mul_one] at hx'
    exact hx'
  induction m with
  | zero => simp [registerXResetMagnitude]
  | succ m ih =>
      rw [registerXResetMagnitude, pow_succ, Complex.normSq_mul]
      change Complex.normSq (registerXResetMagnitude m) *
          Complex.normSq h = (1 / 2 : ℝ) ^ (m + 1)
      rw [ih, hnorm, pow_succ]

private theorem uniformRegisterCoefficients_mass (m : Nat) :
    (((boolTranscripts m).map fun _ => registerXResetMagnitude m).map
        Complex.normSq).sum = 1 := by
  rw [List.map_map]
  have hmap :
      (boolTranscripts m).map
          (Complex.normSq ∘ fun _ => registerXResetMagnitude m) =
        List.replicate (boolTranscripts m).length
          (Complex.normSq (registerXResetMagnitude m)) := by
    change
      (boolTranscripts m).map
          (Function.const (List Bool)
            (Complex.normSq (registerXResetMagnitude m))) =
        List.replicate (boolTranscripts m).length
          (Complex.normSq (registerXResetMagnitude m))
    exact List.map_const
  rw [hmap]
  simp [boolTranscripts_length, normSq_registerXResetMagnitude]

/-- Exact coherent measurement-uncomputation rule.  Once the selected
correction supplies `(-1)^(b · y)`, each transcript branch has the same
input-independent coefficient `2^(-m/2)` and implements register clearing. -/
theorem measureResetWithCorrection_coherent
    (targets : List Wire)
    (correction : List Bool → Circuit)
    (Valid : BasisState → Prop)
    (hnodup : targets.Nodup)
    (hcorrection : RegisterXPhaseCorrectionOn targets correction Valid) :
    CoherentlyImplementsOn
      (measureResetWithCorrection targets correction)
      (clearRegisterMap targets)
      Valid := by
  let coefficients :=
    (boolTranscripts targets.length).map
      (fun _ => registerXResetMagnitude targets.length)
  refine ⟨coefficients, ?_, uniformRegisterCoefficients_mass targets.length⟩
  rw [run_measureResetWithCorrection]
  apply forall₂_map_same
  intro outcomes houtcomes
  have hlength := mem_boolTranscripts_length houtcomes
  intro s hs
  change
    Quantum.run (correction outcomes)
        (xResetRegisterKraus targets outcomes (ket s)) =
      registerXResetMagnitude targets.length •
        clearRegisterMap targets (ket s)
  rw [xResetRegisterKraus_ket targets outcomes s hlength hnodup]
  rw [registerXResetCoeff_eq_magnitude_mul_phase
    targets outcomes s hlength]
  rw [map_smul]
  rw [hcorrection outcomes hlength s hs]
  rw [clearRegisterMap_ket]
  rw [smul_smul]
  rw [mul_assoc, registerXPhase_mul_self]
  simp

/-- Physical well-formedness of register measurement with selected
corrections. -/
theorem measureResetWithCorrection_wellFormed
    (targets : List Wire)
    (correction : List Bool → Circuit)
    (hcorrection : ∀ outcomes,
      outcomes.length = targets.length →
        CircuitWellFormed (correction outcomes)) :
    (measureResetWithCorrection targets correction).WellFormed := by
  induction targets generalizing correction with
  | nil =>
      simpa [measureResetWithCorrection, AdaptiveCircuit.WellFormed]
        using hcorrection [] rfl
  | cons target targets ih =>
      simp only [measureResetWithCorrection, AdaptiveCircuit.WellFormed]
      constructor
      · apply ih
        intro outcomes hlength
        apply hcorrection (false :: outcomes)
        simp [hlength]
      · apply ih
        intro outcomes hlength
        apply hcorrection (true :: outcomes)
        simp [hlength]

/-- Register measurement performs exactly one measurement/reset per wire. -/
@[simp]
theorem measureResetWithCorrection_measurementCount
    (targets : List Wire)
    (correction : List Bool → Circuit) :
    (measureResetWithCorrection targets correction).measurementCount =
      targets.length := by
  induction targets generalizing correction with
  | nil => rfl
  | cons target targets ih =>
      simp [measureResetWithCorrection, AdaptiveCircuit.measurementCount,
        ih, Nat.add_comm]

/-- Transcript-selected Pauli-Z gates on a register. -/
def registerZCorrection : List Wire → List Bool → Circuit
  | target :: targets, outcome :: outcomes =>
      (if outcome then pauliZ target else []) ++
        registerZCorrection targets outcomes
  | _, _ => []

/-- The selected Z gates contribute exactly `(-1)^(b · y)`. -/
theorem run_registerZCorrection_ket
    (targets : List Wire)
    (outcomes : List Bool)
    (s : BasisState) :
    Quantum.run (registerZCorrection targets outcomes) (ket s) =
      registerXPhase targets outcomes s • ket s := by
  induction targets generalizing outcomes s with
  | nil => simp [registerZCorrection, registerXPhase]
  | cons target targets ih =>
      cases outcomes with
      | nil => simp [registerZCorrection, registerXPhase]
      | cons outcome outcomes =>
          rw [registerZCorrection, Quantum.run_append]
          cases outcome with
          | false =>
              simp [registerXPhase, ih]
          | true =>
              simp only [if_true]
              rw [run_pauliZ_ket]
              by_cases htarget : s target
              · simp [registerXPhase, htarget, ih]
              · simp [registerXPhase, htarget, ih]

theorem registerZCorrection_wellFormed
    (targets : List Wire)
    (outcomes : List Bool) :
    CircuitWellFormed (registerZCorrection targets outcomes) := by
  induction targets generalizing outcomes with
  | nil => simp [registerZCorrection]
  | cons target targets ih =>
      cases outcomes with
      | nil => simp [registerZCorrection]
      | cons outcome outcomes =>
          cases outcome <;>
            simp [registerZCorrection, ih, pauliZ_wellFormed]

/-- Recompute the old register, apply the selected Z phases, and uncompute. -/
def recomputeZCorrection
    (compute : Circuit)
    (targets : List Wire)
    (outcomes : List Bool) : Circuit :=
  compute ++ registerZCorrection targets outcomes ++
    Circuit.adjoint compute

/-- Generic recompute/Z-correct/uncompute phase rule. -/
theorem recomputeZCorrection_phase
    (compute : Circuit)
    (targets : List Wire)
    (outcomes : List Bool)
    (s : BasisState)
    (hcompute : Quantum.run compute
        (ket (clearRegister targets s)) = ket s)
    (hwellFormed : CircuitWellFormed compute) :
    Quantum.run (recomputeZCorrection compute targets outcomes)
        (ket (clearRegister targets s)) =
      registerXPhase targets outcomes s •
        ket (clearRegister targets s) := by
  unfold recomputeZCorrection
  rw [Quantum.run_append, Quantum.run_append]
  rw [hcompute]
  rw [run_registerZCorrection_ket]
  rw [Quantum.run_smul]
  rw [← hcompute]
  rw [run_adjoint_run compute hwellFormed]

/-- The generic recompute correction is physically well formed. -/
theorem recomputeZCorrection_wellFormed
    (compute : Circuit)
    (targets : List Wire)
    (outcomes : List Bool)
    (hcompute : CircuitWellFormed compute) :
    CircuitWellFormed
      (recomputeZCorrection compute targets outcomes) := by
  simp [recomputeZCorrection, hcompute,
    registerZCorrection_wellFormed]

/-- Coherent measurement uncomputation obtained by the generic
recompute/Z-correct/uncompute construction. -/
theorem recomputeMeasurementUncompute_coherent
    (compute : Circuit)
    (targets : List Wire)
    (Valid : BasisState → Prop)
    (hnodup : targets.Nodup)
    (hcompute : ∀ s, Valid s →
      Quantum.run compute (ket (clearRegister targets s)) = ket s)
    (hwellFormed : CircuitWellFormed compute) :
    CoherentlyImplementsOn
      (measureResetWithCorrection targets
        (recomputeZCorrection compute targets))
      (clearRegisterMap targets)
      Valid := by
  apply measureResetWithCorrection_coherent targets _ Valid hnodup
  intro outcomes hlength s hs
  exact recomputeZCorrection_phase compute targets outcomes s
    (hcompute s hs) hwellFormed

/-- Classical reversible computations can use the generic measurement-
uncomputation rule through the established classical-to-quantum agreement
bridge. -/
theorem recomputeMeasurementUncompute_coherent_of_classical
    (compute : Circuit)
    (targets : List Wire)
    (Valid : BasisState → Prop)
    (hnodup : targets.Nodup)
    (hcompute : ∀ s, Valid s →
      Classical.run compute (clearRegister targets s) = s)
    (hHPFree : Classical.HPFree compute)
    (hwellFormed : CircuitWellFormed compute) :
    CoherentlyImplementsOn
      (measureResetWithCorrection targets
        (recomputeZCorrection compute targets))
      (clearRegisterMap targets)
      Valid := by
  apply recomputeMeasurementUncompute_coherent compute targets Valid
    hnodup _ hwellFormed
  intro s hs
  rw [run_ket_agrees_classical compute _ hHPFree]
  rw [hcompute s hs]

/-- Change the ideal map of a coherent implementation when the two maps agree
on every valid basis input. -/
theorem CoherentlyImplementsOn.congrIdeal
    {program : AdaptiveCircuit}
    {firstIdeal secondIdeal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop}
    (hfirst : CoherentlyImplementsOn program firstIdeal Valid)
    (heq : ∀ s, Valid s →
      firstIdeal (ket s) = secondIdeal (ket s)) :
    CoherentlyImplementsOn program secondIdeal Valid := by
  rcases hfirst with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch s hs => by
    rw [hbranch s hs, heq s hs]

end

end ShorECDLP.Quantum
