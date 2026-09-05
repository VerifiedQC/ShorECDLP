import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep

/-!
# Fixed-horizon indexed EEA schedule

This module serially composes the source-indexed microstep over a one-based interval.  It keeps
the forward circuit, the pinned explicit reverse circuit, the measurement-uncomputed forward
program, and the circuit-free state trace on the same recursion.  The state invariant records
only obligations that depend on the concrete EEA encoding: clean shared scratch, the borrowed
epoch, and the two decoded iteration-end routes.  Those obligations are discharged by the
concrete encoding layer rather than hidden inside this scheduler.  This first schedule boundary
proves forward semantics and adaptive coherent refinement.  Cancellation of the explicit reverse
also needs the source inverse decoders to select the forward boundaries; that state-dependent fact
is intentionally left to the concrete encoding layer rather than assumed here.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-! ## One automatically routed step -/

/-- Direct indexed-step recurrence with both optional iteration-end boundaries chosen from the
actual unary decoders.  This removes the caller-supplied route parameters from schedule clients. -/
def indexedStepRoutedState
    (registers : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) : BasisState :=
  let routes := indexedStepEndRoutes registers n T state
  indexedStepForwardState registers n T routes.1 routes.2 state

/-- Both decoder outputs lie in the certified source windows for this index. -/
def IndexedStepRoutesValid
    (registers : IndexedStepRegisters) (n T : Nat)
    (state : BasisState) : Prop :=
  let routes := indexedStepEndRoutes registers n T state
  (endIterationWindowsAt n T).k4 ≤ routes.1 ∧
    routes.1 ≤ (endIterationWindowsAt n T).K4 ∧
    (endIterationWindowsAt n T).k5 ≤ routes.2 ∧
    routes.2 ≤ (endIterationWindowsAt n T).K5Decode n

/-- The landed indexed-step theorem with its two routes selected internally. -/
theorem indexedStepUnitary_correct_routed
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hlayout : IndexedStepLayout registers n T)
    (hready : IndexedStepReady registers state)
    (hencoded : IndexedStepEpochEncoded registers state)
    (hroutes : IndexedStepRoutesValid registers n T state) :
    run (indexedStepUnitary registers n T) state =
        indexedStepRoutedState registers n T state ∧
      IndexedStepReady registers
        (run (indexedStepUnitary registers n T) state) := by
  let routes := indexedStepEndRoutes registers n T state
  have hbounds :
      (endIterationWindowsAt n T).k4 ≤ routes.1 ∧
        routes.1 ≤ (endIterationWindowsAt n T).K4 ∧
        (endIterationWindowsAt n T).k5 ≤ routes.2 ∧
        routes.2 ≤ (endIterationWindowsAt n T).K5Decode n := by
    simpa only [IndexedStepRoutesValid, routes] using hroutes
  have hcorrect := indexedStepUnitary_correct registers n T routes.1 routes.2
    ⟨hbounds.1, hbounds.2.1⟩ ⟨hbounds.2.2.1, hbounds.2.2.2⟩
    state hlayout hready hencoded (fun _ ↦ rfl)
  simpa only [indexedStepRoutedState, routes] using hcorrect

/-! ## Shared schedule recursion -/

/-- Forward coherent source stream for `count` consecutive one-based indices. -/
def indexedScheduleUnitary
    (registers : IndexedStepRegisters) (n start : Nat) : Nat → Circuit
  | 0 => []
  | count + 1 =>
      indexedStepUnitary registers n start ++
        indexedScheduleUnitary registers n (start + 1) count

/-- Pinned explicit reverse stream in descending index order. -/
def indexedScheduleInverseUnitary
    (registers : IndexedStepRegisters) (n start : Nat) : Nat → Circuit
  | 0 => []
  | count + 1 =>
      indexedScheduleInverseUnitary registers n (start + 1) count ++
        indexedStepInverseUnitary registers n start

/-- Measurement-uncomputed forward schedule, with the same chronological step order. -/
def indexedScheduleAdaptive
    (registers : IndexedStepRegisters) (n start : Nat) : Nat → AdaptiveCircuit
  | 0 => .unitary [] .done
  | count + 1 =>
      (indexedStepAdaptive registers n start).seq
        (indexedScheduleAdaptive registers n (start + 1) count)

/-- Circuit-free trace of the automatically routed indexed-step recurrence. -/
def indexedScheduleState
    (registers : IndexedStepRegisters) (n start : Nat) :
    Nat → BasisState → BasisState
  | 0, state => state
  | count + 1, state =>
      indexedScheduleState registers n (start + 1) count
        (indexedStepRoutedState registers n start state)

/-- Per-index physical layouts, separated from the state-dependent encoding invariant. -/
inductive IndexedScheduleLayout
    (registers : IndexedStepRegisters) (n : Nat) : Nat → Nat → Prop
  | done (start : Nat) : IndexedScheduleLayout registers n start 0
  | step {start count : Nat}
      (head : IndexedStepLayout registers n start)
      (tail : IndexedScheduleLayout registers n (start + 1) count) :
      IndexedScheduleLayout registers n start (count + 1)

/-- State-dependent invariant threaded through the circuit-free schedule trace.  `tail` states
that the same conditions hold at the next index after the exact routed recurrence. -/
inductive IndexedScheduleInvariant
    (registers : IndexedStepRegisters) (n : Nat) :
    Nat → Nat → BasisState → Prop
  | done (start : Nat) (state : BasisState)
      (ready : IndexedStepReady registers state) :
      IndexedScheduleInvariant registers n start 0 state
  | step {start count : Nat} {state : BasisState}
      (ready : IndexedStepReady registers state)
      (epochEncoded : IndexedStepEpochEncoded registers state)
      (routesValid : IndexedStepRoutesValid registers n start state)
      (tail : IndexedScheduleInvariant registers n (start + 1) count
        (indexedStepRoutedState registers n start state)) :
      IndexedScheduleInvariant registers n start (count + 1) state

/-! ## Structural and direct semantic theorems -/

theorem indexedScheduleUnitary_wellFormed
    (registers : IndexedStepRegisters) (n start count : Nat)
    (hlayout : IndexedScheduleLayout registers n start count) :
    CircuitWellFormed (indexedScheduleUnitary registers n start count) := by
  induction hlayout with
  | done start => simp [indexedScheduleUnitary, CircuitWellFormed]
  | @step start count head tail ih =>
      rw [indexedScheduleUnitary, circuitWellFormed_append]
      exact ⟨indexedStepUnitary_wellFormed registers n start head, ih⟩

theorem indexedScheduleInverseUnitary_wellFormed
    (registers : IndexedStepRegisters) (n start count : Nat)
    (hlayout : IndexedScheduleLayout registers n start count) :
    CircuitWellFormed
      (indexedScheduleInverseUnitary registers n start count) := by
  induction hlayout with
  | done start => simp [indexedScheduleInverseUnitary, CircuitWellFormed]
  | @step start count head tail ih =>
      rw [indexedScheduleInverseUnitary, circuitWellFormed_append]
      exact ⟨ih, indexedStepInverseUnitary_wellFormed registers n start head⟩

@[simp]
theorem indexedScheduleUnitary_HPFree
    (registers : IndexedStepRegisters) (n start count : Nat) :
    HPFree (indexedScheduleUnitary registers n start count) := by
  induction count generalizing start with
  | zero => simp [indexedScheduleUnitary]
  | succ count ih =>
      simp [indexedScheduleUnitary, indexedStepUnitary_HPFree, ih]

@[simp]
theorem indexedScheduleInverseUnitary_HPFree
    (registers : IndexedStepRegisters) (n start count : Nat) :
    HPFree (indexedScheduleInverseUnitary registers n start count) := by
  induction count generalizing start with
  | zero => simp [indexedScheduleInverseUnitary]
  | succ count ih =>
      simp [indexedScheduleInverseUnitary, indexedStepInverseUnitary_HPFree, ih]

theorem indexedScheduleAdaptive_wellFormed
    (registers : IndexedStepRegisters) (n start count : Nat)
    (hlayout : IndexedScheduleLayout registers n start count) :
    (indexedScheduleAdaptive registers n start count).WellFormed := by
  induction hlayout with
  | done start => simp [indexedScheduleAdaptive, AdaptiveCircuit.WellFormed]
  | @step start count head tail ih =>
      exact AdaptiveCircuit.WellFormed.seq
        (indexedStepAdaptive_wellFormed registers n start head) ih

/-- The coherent schedule runs the exact routed recurrence and restores boundary readiness. -/
theorem indexedScheduleUnitary_correct
    (registers : IndexedStepRegisters) (n start count : Nat)
    (state : BasisState)
    (hlayout : IndexedScheduleLayout registers n start count)
    (hinvariant : IndexedScheduleInvariant registers n start count state) :
    run (indexedScheduleUnitary registers n start count) state =
        indexedScheduleState registers n start count state ∧
      IndexedStepReady registers
        (run (indexedScheduleUnitary registers n start count) state) := by
  induction hlayout generalizing state with
  | done start =>
      cases hinvariant with
      | done _ _ hready =>
          exact ⟨rfl, hready⟩
  | @step start count head tail ih =>
      cases hinvariant with
      | step hready hencoded hroutes htail =>
          have hhead := indexedStepUnitary_correct_routed registers n start state
            head hready hencoded hroutes
          have hrest := ih (indexedStepRoutedState registers n start state) htail
          constructor
          · simp only [indexedScheduleUnitary, indexedScheduleState,
              Classical.run_append]
            rw [hhead.1, hrest.1]
          · simpa only [indexedScheduleUnitary, Classical.run_append,
              hhead.1] using hrest.2

private theorem indexedSchedule_coherent_strengthen
    {program : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid Stronger : BasisState → Prop}
    (hrefines : CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ state, Stronger state → Valid state) :
    CoherentlyImplementsOn program ideal Stronger := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hstate ↦
    hbranch state (hsub state hstate)

private theorem indexedSchedule_coherent_seq_circuits
    {first second : AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (Classical.run firstCircuit state)) :
    CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [Quantum.run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact Quantum.supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit (Quantum.ket state)).symm

/-- Measurement-uncomputation composes through the complete schedule with one list of
input-independent branch coefficients. -/
theorem indexedScheduleAdaptive_coherent
    (registers : IndexedStepRegisters) (n start count : Nat)
    (hlayout : IndexedScheduleLayout registers n start count) :
    CoherentlyImplementsOn
      (indexedScheduleAdaptive registers n start count)
      (Quantum.run (indexedScheduleUnitary registers n start count))
      (IndexedScheduleInvariant registers n start count) := by
  induction hlayout with
  | done start =>
      simpa [indexedScheduleAdaptive, indexedScheduleUnitary] using
        (CoherentlyImplementsOn.unitary ([] : Circuit)
          (IndexedScheduleInvariant registers n start 0))
  | @step start count head tail ih =>
      have hheadBase := indexedStepAdaptive_coherent registers n start head
      have hhead : CoherentlyImplementsOn
          (indexedStepAdaptive registers n start)
          (Quantum.run (indexedStepUnitary registers n start))
          (IndexedScheduleInvariant registers n start (count + 1)) :=
        indexedSchedule_coherent_strengthen hheadBase (by
          intro state hstate
          cases hstate with
          | step hready hencoded _ _ => exact ⟨hready, hencoded⟩)
      have hall := indexedSchedule_coherent_seq_circuits hhead ih
        (indexedStepUnitary_HPFree registers n start) (by
          intro state hstate
          cases hstate with
          | step hready hencoded hroutes htail =>
              have hcorrect := indexedStepUnitary_correct_routed registers n start
                state head hready hencoded hroutes
              rw [hcorrect.1]
              exact htail)
      simpa only [indexedScheduleAdaptive, indexedScheduleUnitary] using hall

/-! ## Exact secp256k1 horizon -/

/-- Fixed number of one-based microsteps in the secp256k1 paper schedule. -/
def secp256k1ScheduleLength : Nat := 1620

/-- Exact one-based index list `1, …, 1620`. -/
def secp256k1ScheduleIndices : List Nat :=
  List.range' 1 secp256k1ScheduleLength

theorem mem_secp256k1ScheduleIndices_iff (T : Nat) :
    T ∈ secp256k1ScheduleIndices ↔ 1 ≤ T ∧ T ≤ 1620 := by
  simp [secp256k1ScheduleIndices, secp256k1ScheduleLength]
  omega

/-- Every exact schedule index is classified by the circuit-free active-or-padding theorem. -/
theorem secp256k1Schedule_indexedFrame
    {x : Nat} (hx : 1 ≤ x) (hxp : x < ShorECDLP.p) :
    ∀ T ∈ secp256k1ScheduleIndices,
      Nonempty (PaperIndexedFrame ShorECDLP.p x T) := by
  intro T hT
  apply paperIndexedFrame_exists ShorECDLP.Secp256k1.p_prime hx hxp
  exact (mem_secp256k1ScheduleIndices_iff T).mp hT |>.1

/-- Exact coherent forward EEA schedule used by the secp256k1 submission. -/
def secp256k1EEAForwardUnitary (registers : IndexedStepRegisters) : Circuit :=
  indexedScheduleUnitary registers 256 1 secp256k1ScheduleLength

/-- Exact pinned explicit reverse schedule, ordered from index 1,620 down to 1. -/
def secp256k1EEAReverseUnitary (registers : IndexedStepRegisters) : Circuit :=
  indexedScheduleInverseUnitary registers 256 1 secp256k1ScheduleLength

/-- Exact measurement-uncomputed forward EEA schedule. -/
def secp256k1EEAForwardAdaptive
    (registers : IndexedStepRegisters) : AdaptiveCircuit :=
  indexedScheduleAdaptive registers 256 1 secp256k1ScheduleLength

/-- Circuit-free automatically routed trace over all 1,620 indices. -/
def secp256k1EEAState
    (registers : IndexedStepRegisters) (state : BasisState) : BasisState :=
  indexedScheduleState registers 256 1 secp256k1ScheduleLength state

abbrev Secp256k1ScheduleLayout (registers : IndexedStepRegisters) : Prop :=
  IndexedScheduleLayout registers 256 1 secp256k1ScheduleLength

abbrev Secp256k1ScheduleInvariant
    (registers : IndexedStepRegisters) (state : BasisState) : Prop :=
  IndexedScheduleInvariant registers 256 1 secp256k1ScheduleLength state

theorem secp256k1EEAForwardUnitary_correct
    (registers : IndexedStepRegisters) (state : BasisState)
    (hlayout : Secp256k1ScheduleLayout registers)
    (hinvariant : Secp256k1ScheduleInvariant registers state) :
    run (secp256k1EEAForwardUnitary registers) state =
        secp256k1EEAState registers state ∧
      IndexedStepReady registers
        (run (secp256k1EEAForwardUnitary registers) state) := by
  exact indexedScheduleUnitary_correct registers 256 1
    secp256k1ScheduleLength state hlayout hinvariant

theorem secp256k1EEAForwardAdaptive_coherent
    (registers : IndexedStepRegisters)
    (hlayout : Secp256k1ScheduleLayout registers) :
    CoherentlyImplementsOn
      (secp256k1EEAForwardAdaptive registers)
      (Quantum.run (secp256k1EEAForwardUnitary registers))
      (Secp256k1ScheduleInvariant registers) := by
  exact indexedScheduleAdaptive_coherent registers 256 1
    secp256k1ScheduleLength hlayout

end

end ShorECDLP.Paper2607_13816
