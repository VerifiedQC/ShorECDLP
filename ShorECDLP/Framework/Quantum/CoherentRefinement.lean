import ShorECDLP.Framework.Quantum.Adaptive

/-!
# Coherent refinement for adaptive programs

An adaptive program refines a linear ideal map when its finite Kraus branches
are aligned with a list of input-independent complex coefficients.  For every
valid computational-basis input, each branch is that coefficient times the
same ideal output, and the coefficients have total squared magnitude one.

Keeping the coefficients list-aligned with the instrument is important:
distinct classical transcripts continue to contribute distinct Born mass even
when their Kraus maps or histories happen to coincide.
-/

namespace ShorECDLP.Quantum

noncomputable section

/-- A state is supported on the valid computational-basis inputs. -/
def SupportedOn (Valid : BasisState → Prop) (psi : State) : Prop :=
  ∀ s, psi s ≠ 0 → Valid s

@[simp]
theorem supportedOn_zero (Valid : BasisState → Prop) :
    SupportedOn Valid (0 : State) := by
  intro s hs
  exact (hs rfl).elim

theorem supportedOn_ket
    (Valid : BasisState → Prop) (s : BasisState)
    (hs : Valid s) :
    SupportedOn Valid (ket s) := by
  intro u hu
  have hus : s = u := by
    by_contra hne
    exact hu (ket_ne hne)
  subst u
  exact hs

/-- One branch agrees coherently with `ideal` on every valid basis input. -/
def BranchCoherentOn
    (ideal : State →ₗ[ℂ] State)
    (Valid : BasisState → Prop)
    (branch : InstrumentBranch)
    (coefficient : ℂ) : Prop :=
  ∀ s, Valid s →
    branch.kraus (ket s) = coefficient • ideal (ket s)

/-- An adaptive program coherently implements `ideal` on `Valid` when every
Kraus branch has an input-independent coefficient and those coefficients have
total Born mass one. -/
def CoherentlyImplementsOn
    (program : AdaptiveCircuit)
    (ideal : State →ₗ[ℂ] State)
    (Valid : BasisState → Prop) : Prop :=
  ∃ coefficients : List ℂ,
    List.Forall₂ (BranchCoherentOn ideal Valid)
      program.run coefficients ∧
    (coefficients.map Complex.normSq).sum = 1

private theorem branch_coherent_on_supported_state
    {ideal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop}
    {branch : InstrumentBranch}
    {coefficient : ℂ}
    (hbranch : BranchCoherentOn ideal Valid branch coefficient)
    {psi : State}
    (hpsi : SupportedOn Valid psi) :
    branch.kraus psi = coefficient • ideal psi := by
  induction psi using Finsupp.induction with
  | zero => simp
  | single_add s c psi hs hc ih =>
      have hpsis : psi s = 0 := by
        simpa using hs
      have hsValid : Valid s := by
        apply hpsi s
        simp [hpsis, hc]
      have hpsiValid : SupportedOn Valid psi := by
        intro u hu
        apply hpsi u
        by_cases hus : u = s
        · subst u
          exact (hu hpsis).elim
        · simp [hus, hu]
      have hsingle : Finsupp.single s c = c • ket s := by
        ext u
        simp [ket]
      rw [map_add, hsingle, map_smul, hbranch s hsValid, ih hpsiValid]
      simp [smul_add, smul_smul, mul_comm]

/-- Coherent basis-state refinement extends, with the same aligned branch
coefficients, to every superposition supported on valid inputs. -/
theorem coherent_on_supported_state
    {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop}
    (hrefines : CoherentlyImplementsOn program ideal Valid)
    {psi : State}
    (hpsi : SupportedOn Valid psi) :
    ∃ coefficients : List ℂ,
      List.Forall₂
        (fun branch coefficient =>
          branch.kraus psi = coefficient • ideal psi)
        program.run coefficients ∧
      (coefficients.map Complex.normSq).sum = 1 := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch =>
    branch_coherent_on_supported_state hbranch hpsi

/-- Pairwise products of two aligned coefficient lists, in the same
left-major order as `Instrument.seq`. -/
def coherentSeqCoefficients (first second : List ℂ) : List ℂ :=
  first.flatMap fun before => second.map fun after => before * after

private theorem coherentSeqCoefficients_mass
    (first second : List ℂ) :
    ((coherentSeqCoefficients first second).map Complex.normSq).sum =
      (first.map Complex.normSq).sum *
        (second.map Complex.normSq).sum := by
  induction first with
  | nil => simp [coherentSeqCoefficients]
  | cons coefficient rest ih =>
      rw [coherentSeqCoefficients]
      simp only [List.flatMap_cons,
        List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      rw [List.map_map]
      have hmap :
          List.map
              (Complex.normSq ∘ fun after => coefficient * after)
              second =
            List.map
              (fun after =>
                Complex.normSq coefficient * Complex.normSq after)
              second := by
        apply List.map_congr_left
        intro after hafter
        exact Complex.normSq_mul coefficient after
      rw [hmap]
      rw [List.sum_map_mul_left]
      change
        Complex.normSq coefficient *
              (second.map Complex.normSq).sum +
            ((coherentSeqCoefficients rest second).map
              Complex.normSq).sum =
          (Complex.normSq coefficient +
              (rest.map Complex.normSq).sum) *
            (second.map Complex.normSq).sum
      rw [ih]
      ring

private theorem forall₂_append
    {alpha beta : Type*}
    {relation : alpha → beta → Prop}
    {firstLeft secondLeft : List alpha}
    {firstRight secondRight : List beta}
    (hfirst : List.Forall₂ relation firstLeft firstRight)
    (hsecond : List.Forall₂ relation secondLeft secondRight) :
    List.Forall₂ relation
      (firstLeft ++ secondLeft) (firstRight ++ secondRight) := by
  induction hfirst with
  | nil => exact hsecond
  | cons head tail ih =>
      exact .cons head ih

private theorem aligned_seq_one
    {firstIdeal secondIdeal : State →ₗ[ℂ] State}
    {FirstValid SecondValid : BasisState → Prop}
    {firstBranch : InstrumentBranch}
    {firstCoefficient : ℂ}
    {secondBranches : Instrument}
    {secondCoefficients : List ℂ}
    (hfirst : BranchCoherentOn
      firstIdeal FirstValid firstBranch firstCoefficient)
    (hsecond : List.Forall₂
      (BranchCoherentOn secondIdeal SecondValid)
      secondBranches secondCoefficients)
    (hsupported : ∀ s, FirstValid s →
      SupportedOn SecondValid (firstIdeal (ket s))) :
    List.Forall₂
      (BranchCoherentOn (secondIdeal.comp firstIdeal) FirstValid)
      (secondBranches.map fun secondBranch =>
        firstBranch.seq secondBranch)
      (secondCoefficients.map fun secondCoefficient =>
        firstCoefficient * secondCoefficient) := by
  induction hsecond with
  | nil => exact .nil
  | @cons secondBranch secondCoefficient branchTail coefficientTail
      hhead _ ih =>
      apply List.Forall₂.cons
      · intro s hs
        change
          secondBranch.kraus (firstBranch.kraus (ket s)) =
            (firstCoefficient * secondCoefficient) •
              secondIdeal (firstIdeal (ket s))
        rw [hfirst s hs, map_smul]
        rw [branch_coherent_on_supported_state hhead (hsupported s hs)]
        simp [smul_smul]
      · exact ih

private theorem aligned_seq
    {firstIdeal secondIdeal : State →ₗ[ℂ] State}
    {FirstValid SecondValid : BasisState → Prop}
    {firstBranches secondBranches : Instrument}
    {firstCoefficients secondCoefficients : List ℂ}
    (hfirst : List.Forall₂
      (BranchCoherentOn firstIdeal FirstValid)
      firstBranches firstCoefficients)
    (hsecond : List.Forall₂
      (BranchCoherentOn secondIdeal SecondValid)
      secondBranches secondCoefficients)
    (hsupported : ∀ s, FirstValid s →
      SupportedOn SecondValid (firstIdeal (ket s))) :
    List.Forall₂
      (BranchCoherentOn (secondIdeal.comp firstIdeal) FirstValid)
      (Instrument.seq firstBranches secondBranches)
      (coherentSeqCoefficients firstCoefficients secondCoefficients) := by
  induction hfirst with
  | nil => exact .nil
  | @cons firstBranch firstCoefficient branchTail coefficientTail
      hhead _ ih =>
      apply forall₂_append
      · exact aligned_seq_one hhead hsecond hsupported
      · exact ih

namespace CoherentlyImplementsOn

/-- An ordinary unitary circuit, embedded as a one-branch adaptive program,
coherently implements its existing linear semantics. -/
theorem unitary
    (circuit : Circuit)
    (Valid : BasisState → Prop) :
    CoherentlyImplementsOn
      (.unitary circuit .done) (Quantum.run circuit) Valid := by
  refine ⟨[1], ?_, by simp⟩
  · rw [AdaptiveCircuit.run_unitary_done]
    apply List.Forall₂.cons
    · intro s hs
      simp
    · exact .nil

/-- Coherent refinement composes sequentially when the first ideal map sends
valid basis inputs into the validity subspace required by the second map. -/
theorem seq
    {first second : AdaptiveCircuit}
    {firstIdeal secondIdeal : State →ₗ[ℂ] State}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : CoherentlyImplementsOn first firstIdeal FirstValid)
    (hsecond : CoherentlyImplementsOn second secondIdeal SecondValid)
    (hsupported : ∀ s, FirstValid s →
      SupportedOn SecondValid (firstIdeal (ket s))) :
    CoherentlyImplementsOn
      (first.seq second) (secondIdeal.comp firstIdeal) FirstValid := by
  rcases hfirst with ⟨firstCoefficients, hfirstAligned, hfirstMass⟩
  rcases hsecond with ⟨secondCoefficients, hsecondAligned, hsecondMass⟩
  refine ⟨coherentSeqCoefficients firstCoefficients secondCoefficients,
    ?_, ?_⟩
  ·
    rw [AdaptiveCircuit.run_seq]
    exact aligned_seq hfirstAligned hsecondAligned hsupported
  · rw [coherentSeqCoefficients_mass, hfirstMass, hsecondMass]
    norm_num

/-- A same-validity specialization of sequential composition.  It is the
form used when an independently proved block acts on a tensor factor or on
disjoint wires and therefore preserves the shared validity subspace. -/
theorem tensor_or_disjoint
    {first second : AdaptiveCircuit}
    {firstIdeal secondIdeal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop}
    (hfirst : CoherentlyImplementsOn first firstIdeal Valid)
    (hsecond : CoherentlyImplementsOn second secondIdeal Valid)
    (hpreserves : ∀ s, Valid s →
      SupportedOn Valid (firstIdeal (ket s))) :
    CoherentlyImplementsOn
      (first.seq second) (secondIdeal.comp firstIdeal) Valid :=
  hfirst.seq hsecond hpreserves

end CoherentlyImplementsOn

/-- Born mass of a final computational-basis event. -/
def eventProbability
    (event : BasisState → Prop)
    [DecidablePred event]
    (psi : State) : ℝ :=
  ∑ s ∈ psi.support,
    if event s then Complex.normSq (psi s) else 0

theorem eventProbability_smul
    (event : BasisState → Prop)
    [DecidablePred event]
    (coefficient : ℂ)
    (psi : State) :
    eventProbability event (coefficient • psi) =
      Complex.normSq coefficient * eventProbability event psi := by
  classical
  by_cases hcoefficient : coefficient = 0
  · subst coefficient
    simp [eventProbability]
  · rw [eventProbability, Finsupp.support_smul_eq hcoefficient]
    unfold eventProbability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hevent : event s
    · simp [hevent, Finsupp.smul_apply, smul_eq_mul,
        Complex.normSq_mul]
    · simp [hevent]

/-- Sum of a final event's Born probability over every internal transcript. -/
def Instrument.eventProbability
    (instrument : Instrument)
    (event : BasisState → Prop)
    [DecidablePred event]
    (psi : State) : ℝ :=
  (instrument.map fun branch =>
    Quantum.eventProbability event (branch.kraus psi)).sum

private theorem aligned_eventProbability
    {ideal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop}
    {branches : Instrument}
    {coefficients : List ℂ}
    (haligned : List.Forall₂
      (BranchCoherentOn ideal Valid) branches coefficients)
    {psi : State}
    (hpsi : SupportedOn Valid psi)
    (event : BasisState → Prop)
    [DecidablePred event] :
    Instrument.eventProbability branches event psi =
      (coefficients.map Complex.normSq).sum *
        eventProbability event (ideal psi) := by
  induction haligned with
  | nil => simp [Instrument.eventProbability]
  | @cons branch coefficient branchTail coefficientTail hhead _ ih =>
      simp only [Instrument.eventProbability, List.map_cons, List.sum_cons]
      rw [branch_coherent_on_supported_state hhead hpsi]
      rw [eventProbability_smul]
      change
        Complex.normSq coefficient * eventProbability event (ideal psi) +
            Instrument.eventProbability branchTail event psi =
          (Complex.normSq coefficient +
              (coefficientTail.map Complex.normSq).sum) *
            eventProbability event (ideal psi)
      rw [ih]
      ring

/-- After internal transcripts are forgotten, every final computational-basis
event has exactly the same Born probability as the ideal linear map. -/
theorem coherent_final_probability_eq
    {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop}
    (hrefines : CoherentlyImplementsOn program ideal Valid)
    {psi : State}
    (hpsi : SupportedOn Valid psi)
    (event : BasisState → Prop)
    [DecidablePred event] :
    Instrument.eventProbability program.run event psi =
      eventProbability event (ideal psi) := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  rw [aligned_eventProbability haligned hpsi event]
  rw [hmass]
  simp

end

end ShorECDLP.Quantum
