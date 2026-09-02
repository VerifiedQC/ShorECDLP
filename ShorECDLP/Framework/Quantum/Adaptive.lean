import ShorECDLP.Framework.CostModel
import ShorECDLP.Framework.Quantum.InnerProduct

/-!
# Adaptive quantum programs

Mid-circuit measurement is deliberately kept outside `Gate` and `Circuit`.
Those existing types describe unitary programs and have a total syntactic
adjoint.  An adaptive program instead alternates verified unitary `Circuit`
blocks with X-basis measurement, reset, and two classical continuations.

The semantics is a finite list of unnormalised Kraus branches.  Consequently
each branch remains complex-linear, its squared norm is its Born mass, and
zero-probability branches never require division.
-/

namespace ShorECDLP.Quantum

noncomputable section

/-- Computational-basis projection onto the states whose `target` bit is
`outcome`. -/
def projectZ (target : Wire) (outcome : Bool) : State →ₗ[ℂ] State where
  toFun ψ := Finsupp.filter (fun s => s target = outcome) ψ
  map_add' ψ φ := by
    classical
    ext s
    by_cases h : s target = outcome <;> simp [h]
  map_smul' c ψ := by
    classical
    ext s
    by_cases h : s target = outcome <;> simp [h]

@[simp]
theorem projectZ_apply
    (target : Wire) (outcome : Bool) (ψ : State) :
    projectZ target outcome ψ =
      Finsupp.filter (fun s => s target = outcome) ψ := rfl

@[simp]
theorem projectZ_ket
    (target : Wire) (outcome : Bool) (s : BasisState) :
    projectZ target outcome (ket s) =
      if s target = outcome then ket s else 0 := by
  classical
  rw [projectZ_apply]
  by_cases h : s target = outcome
  · rw [if_pos h]
    apply (Finsupp.filter_eq_self_iff _ _).2
    intro u hu
    have hus : u = s := by
      by_contra hne
      exact hu (ket_ne (Ne.symm hne))
    subst u
    exact h
  · rw [if_neg h]
    apply (Finsupp.filter_eq_zero_iff _ _).2
    intro u hu
    by_cases hus : s = u
    · subst u
      exact (h hu).elim
    · exact ket_ne hus

/-- The unitary reset used after a Z-basis measurement branch.  On outcome
`true`, X maps the projected `|1⟩` wire to `|0⟩`; outcome `false` is already
clean. -/
def resetCircuit (target : Wire) (outcome : Bool) : Circuit :=
  if outcome then [.X target] else []

/-- One branch of X-basis measurement followed by reset to `|0⟩`.

Operationally this is Hadamard, Z-basis projection to `outcome`, and an X on
the true branch. -/
def xResetKraus (target : Wire) (outcome : Bool) : State →ₗ[ℂ] State :=
  (run (resetCircuit target outcome)).comp
    ((projectZ target outcome).comp (applyGate (.H target)))

/-- The scalar produced by one X-measure/reset branch on a computational-basis
bit.  Every branch has magnitude `1 / √2`; the true branch carries the phase
`(-1)` precisely when the original bit was true. -/
def xResetCoeff (outcome input : Bool) : ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
    if outcome && input then -1 else 1

private theorem upd_twice
    (s : BasisState) (target : Wire) (first second : Bool) :
    s[target ↦ first][target ↦ second] = s[target ↦ second] := by
  funext i
  by_cases hi : i = target
  · subst i
    simp
  · simp [upd, hi]

/-- Exact X-basis measurement/reset rule on a computational-basis ket. -/
theorem xResetKraus_ket
    (target : Wire) (outcome : Bool) (s : BasisState) :
    xResetKraus target outcome (ket s) =
      xResetCoeff outcome (s target) • ket (s[target ↦ false]) := by
  unfold xResetKraus
  simp only [LinearMap.comp_apply]
  rw [applyGate_H_ket]
  rw [map_add, map_smul, map_smul, projectZ_ket, projectZ_ket]
  cases outcome with
  | false => simp [resetCircuit, xResetCoeff]
  | true =>
      cases s target <;>
        simp [resetCircuit, xResetCoeff, onKet, upd_twice]

private theorem xResetKraus_apply_eq_zero_of_true
    (target : Wire) (outcome : Bool) (ψ : State)
    (u : BasisState) (hu : u target = true) :
    xResetKraus target outcome ψ u = 0 := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add ψ φ ihψ ihφ =>
      rw [map_add]
      simp [ihψ, ihφ]
  | single s c =>
      have hsingle : Finsupp.single s c = c • ket s := by
        ext v
        simp [ket]
      rw [hsingle, map_smul, xResetKraus_ket]
      have hne : s[target ↦ false] ≠ u := by
        intro h
        have hbit := congrFun h target
        simp [hu] at hbit
      have hket : ket (s[target ↦ false]) u = 0 := ket_ne hne
      simp [hket]

/-- X-measure/reset really releases its target: every nonzero output basis
amplitude has the target wire equal to `false`. -/
theorem xResetKraus_clean
    (target : Wire) (outcome : Bool) (ψ : State) :
    ∀ s, xResetKraus target outcome ψ s ≠ 0 → s target = false := by
  intro u hu
  cases hut : u target with
  | false => rfl
  | true =>
      exact (hu (xResetKraus_apply_eq_zero_of_true
        target outcome ψ u hut)).elim

private theorem normSq_eq_support_sum (ψ : State) :
    normSq ψ = ∑ s ∈ ψ.support, Complex.normSq (ψ s) := by
  classical
  have hinner :
      inner ψ ψ =
        ((∑ s ∈ ψ.support, Complex.normSq (ψ s) : ℝ) : ℂ) := by
    unfold inner
    change
      (∑ s ∈ ψ.support,
        (starRingEnd ℂ) (ψ s) * ψ s) =
      ((∑ s ∈ ψ.support, Complex.normSq (ψ s) : ℝ) : ℂ)
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    exact (Complex.normSq_eq_conj_mul_self).symm
  unfold normSq
  rw [hinner]
  simp

private theorem normSq_smul (c : ℂ) (ψ : State) :
    normSq (c • ψ) = Complex.normSq c * normSq ψ := by
  unfold normSq
  rw [inner_smul_smul]
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

/-- Both X-measure/reset outcomes have input-independent probability `1/2`
on a computational-basis ket. -/
theorem normSq_xResetKraus_ket
    (target : Wire) (outcome : Bool) (s : BasisState) :
    normSq (xResetKraus target outcome (ket s)) = 1 / 2 := by
  rw [xResetKraus_ket, normSq_smul, normSq_ket, mul_one]
  cases outcome <;> cases s target <;>
    simp [xResetCoeff]

private theorem normSq_projectZ_eq_sum
    (target : Wire) (outcome : Bool) (ψ : State) :
    normSq (projectZ target outcome ψ) =
      ∑ s ∈ ψ.support,
        if s target = outcome then Complex.normSq (ψ s) else 0 := by
  classical
  rw [normSq_eq_support_sum, projectZ_apply, Finsupp.support_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : s target = outcome <;> simp [h]

/-- The two computational-basis projectors partition total Born mass. -/
theorem normSq_projectZ_false_add_true
    (target : Wire) (ψ : State) :
    normSq (projectZ target false ψ) +
        normSq (projectZ target true ψ) =
      normSq ψ := by
  classical
  rw [normSq_projectZ_eq_sum, normSq_projectZ_eq_sum,
    normSq_eq_support_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  cases s target <;> simp

private theorem resetCircuit_wellFormed
    (target : Wire) (outcome : Bool) :
    CircuitWellFormed (resetCircuit target outcome) := by
  cases outcome <;> simp [resetCircuit, CircuitWellFormed, Gate.WellFormed]

/-- X-basis measurement followed by reset is trace preserving when both
unnormalised outcome branches are retained. -/
theorem normSq_xResetKraus_false_add_true
    (target : Wire) (ψ : State) :
    normSq (xResetKraus target false ψ) +
        normSq (xResetKraus target true ψ) =
      normSq ψ := by
  unfold xResetKraus
  simp only [LinearMap.comp_apply]
  rw [normSq_run _ (resetCircuit_wellFormed target false)]
  rw [normSq_run _ (resetCircuit_wellFormed target true)]
  rw [normSq_projectZ_false_add_true]
  exact applyGate_preservesNormSq (.H target) trivial ψ

/-- One unnormalised execution branch of an adaptive program. -/
structure InstrumentBranch where
  history : List Bool
  kraus : State →ₗ[ℂ] State

/-- A finite quantum instrument.  A list is used because distinct classical
histories must contribute distinct Born mass even when their maps coincide. -/
abbrev Instrument := List InstrumentBranch

/-- Total Born mass carried by every branch of an instrument. -/
def Instrument.bornMass (instrument : Instrument) (ψ : State) : ℝ :=
  (instrument.map fun branch => normSq (branch.kraus ψ)).sum

/-- Straight-line unitary blocks with X-basis measure/reset and classical
feed-forward.  The two continuations correspond to outcomes `false` and
`true`. -/
inductive AdaptiveCircuit where
  | done
  | unitary (circuit : Circuit) (next : AdaptiveCircuit)
  | xMeasureReset
      (target : Wire)
      (onFalse onTrue : AdaptiveCircuit)

namespace AdaptiveCircuit

private def prefixBranch
    (outcome : Option Bool)
    (before : State →ₗ[ℂ] State)
    (branch : InstrumentBranch) : InstrumentBranch where
  history := outcome.toList ++ branch.history
  kraus := branch.kraus.comp before

/-- Interpret an adaptive program as all of its unnormalised Kraus branches. -/
def run : AdaptiveCircuit → Instrument
  | .done =>
      [{ history := [], kraus := LinearMap.id }]
  | .unitary circuit next =>
      (run next).map (prefixBranch none (Quantum.run circuit))
  | .xMeasureReset target onFalse onTrue =>
      (run onFalse).map
          (prefixBranch (some false) (xResetKraus target false)) ++
        (run onTrue).map
          (prefixBranch (some true) (xResetKraus target true))

/-- A unitary block is well formed in the existing sense; both adaptive
continuations must themselves be well formed. -/
def WellFormed : AdaptiveCircuit → Prop
  | .done => True
  | .unitary circuit next =>
      CircuitWellFormed circuit ∧ WellFormed next
  | .xMeasureReset _ onFalse onTrue =>
      WellFormed onFalse ∧ WellFormed onTrue

/-- Worst-case T count across classical outcomes.  Measurements, reset, and
classical feed-forward are accounted for separately and do not silently enter
the existing unitary T metric. -/
def tCount : AdaptiveCircuit → Nat
  | .done => 0
  | .unitary circuit next => ShorECDLP.tCount circuit + tCount next
  | .xMeasureReset _ onFalse onTrue => max (tCount onFalse) (tCount onTrue)

/-- Worst-case number of measurement/reset events. -/
def measurementCount : AdaptiveCircuit → Nat
  | .done => 0
  | .unitary _ next => measurementCount next
  | .xMeasureReset _ onFalse onTrue =>
      1 + max (measurementCount onFalse) (measurementCount onTrue)

/-- All physical wire labels appearing anywhere in the adaptive tree. -/
def wires : AdaptiveCircuit → List Wire
  | .done => []
  | .unitary circuit next => circuitWires circuit ++ wires next
  | .xMeasureReset target onFalse onTrue =>
      target :: (wires onFalse ++ wires onTrue)

/-- Conservative physical-qubit count: distinct wire labels in the entire
adaptive tree.  A later circuit can reuse a reset wire by using the same label;
no qubit is subtracted merely because a measurement occurred. -/
def qubitCount (program : AdaptiveCircuit) : Nat :=
  program.wires.dedup.length

private theorem bornMass_map_prefixBranch
    (instrument : Instrument)
    (outcome : Option Bool)
    (before : State →ₗ[ℂ] State)
    (ψ : State) :
    Instrument.bornMass
        (instrument.map (prefixBranch outcome before)) ψ =
      Instrument.bornMass instrument (before ψ) := by
  induction instrument with
  | nil => rfl
  | cons branch rest ih =>
      change
        normSq ((prefixBranch outcome before branch).kraus ψ) +
            Instrument.bornMass
              (rest.map (prefixBranch outcome before)) ψ =
          normSq (branch.kraus (before ψ)) +
            Instrument.bornMass rest (before ψ)
      rw [ih]
      rfl

private theorem bornMass_append
    (first second : Instrument) (ψ : State) :
    Instrument.bornMass (first ++ second) ψ =
      Instrument.bornMass first ψ + Instrument.bornMass second ψ := by
  simp [Instrument.bornMass]

/-- Every well-formed adaptive program preserves total Born mass after summing
all of its unnormalised classical branches. -/
theorem run_preservesBornMass
    (program : AdaptiveCircuit)
    (hprogram : program.WellFormed)
    (ψ : State) :
    Instrument.bornMass program.run ψ = normSq ψ := by
  induction program generalizing ψ with
  | done =>
      simp [run, Instrument.bornMass]
  | unitary circuit next ih =>
      rw [run, bornMass_map_prefixBranch]
      rw [ih hprogram.2]
      exact normSq_run circuit hprogram.1 ψ
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      rw [run, bornMass_append]
      rw [bornMass_map_prefixBranch, bornMass_map_prefixBranch]
      rw [ihFalse hprogram.1, ihTrue hprogram.2]
      exact normSq_xResetKraus_false_add_true target ψ

end AdaptiveCircuit

end

end ShorECDLP.Quantum
