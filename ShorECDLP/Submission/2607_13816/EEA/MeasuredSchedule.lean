import ShorECDLP.Submission.«2607_13816».EEA.MeasuredStep
import ShorECDLP.Submission.«2607_13816».EEA.Schedule

namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem schedule_restrict {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P Q : BasisState → Prop} (h : CoherentlyImplementsOn a v P)
    (hp : ∀ s, Q s → P s) : CoherentlyImplementsOn a v Q := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩
private theorem schedule_seq {a b : AdaptiveCircuit} {u v : Circuit} {P Q : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) Q)
    (hu : HPFree u) (hp : ∀ s, P s → Q (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket Q _ (hp s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append u v (ket s)).symm

/-- Actual ascending schedule with measured endpoint H at each step. -/
def measuredIndexedSchedule (r : IndexedStepRegisters) (n start : Nat) : Nat → AdaptiveCircuit
  | 0 => .unitary [] .done
  | count+1 => (measuredIndexedStep r n start).seq
      (measuredIndexedSchedule r n (start+1) count)

/-- Actual descending schedule; each inverse step starts with measured H. -/
def measuredIndexedScheduleInverse (r : IndexedStepRegisters) (n start : Nat) : Nat → AdaptiveCircuit
  | 0 => .unitary [] .done
  | count+1 => (measuredIndexedScheduleInverse r n (start+1) count).seq
      (measuredIndexedStepInverse r n start)

/-- Inverse H-entry readiness and existing tail conditions at every actual strict prefix. -/
def MeasuredScheduleInverseInput (r : IndexedStepRegisters) (n start : Nat) : Nat → BasisState → Prop
  | 0, _ => True
  | count+1, s => MeasuredScheduleInverseInput r n (start+1) count s ∧
      IndexedStepReady r (Classical.run (indexedScheduleInverseUnitary r n (start+1) count) s) ∧
      IndexedStepInverseAdaptiveInput r n start
        (Classical.run (indexedScheduleInverseUnitary r n (start+1) count) s)

/-- Forward refinement uses the same actual-prefix input contract as the existing schedule. -/
theorem measuredIndexedSchedule_coherent (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) :
    CoherentlyImplementsOn (measuredIndexedSchedule r n start count)
      (Quantum.run (indexedScheduleUnitary r n start count))
      (IndexedScheduleAdaptiveInput r n start count) := by
  induction hl with
  | done start =>
      simpa [measuredIndexedSchedule,indexedScheduleUnitary] using
        (CoherentlyImplementsOn.unitary ([] : Circuit) (IndexedScheduleAdaptiveInput r n start 0))
  | @step start count head tail ih =>
      have hh := schedule_restrict (measuredIndexedStep_coherent r n start head)
        (Q := IndexedScheduleAdaptiveInput r n start (count+1)) (fun _ h => ⟨h.1,h.2.1⟩)
      exact schedule_seq hh ih (indexedStepUnitary_HPFree r n start) (fun _ h => h.2.2)

/-- Inverse refinement retains all actual-prefix scratch conditions, including H entry. -/
theorem measuredIndexedScheduleInverse_coherent (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) :
    CoherentlyImplementsOn (measuredIndexedScheduleInverse r n start count)
      (Quantum.run (indexedScheduleInverseUnitary r n start count))
      (MeasuredScheduleInverseInput r n start count) := by
  induction hl with
  | done start =>
      simpa [measuredIndexedScheduleInverse,indexedScheduleInverseUnitary] using
        (CoherentlyImplementsOn.unitary ([] : Circuit) (MeasuredScheduleInverseInput r n start 0))
  | @step start count head tail ih =>
      have ht := schedule_restrict ih
        (Q := MeasuredScheduleInverseInput r n start (count+1)) (fun _ h => h.1)
      exact schedule_seq ht (measuredIndexedStepInverse_coherent r n start head)
        (indexedScheduleInverseUnitary_HPFree r n (start+1) count) (fun _ h => h.2)

/-- Every emitted forward branch is well formed on the same per-index layout. -/
theorem measuredIndexedSchedule_wellFormed (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) : (measuredIndexedSchedule r n start count).WellFormed := by
  induction hl with
  | done start => simp [measuredIndexedSchedule,AdaptiveCircuit.WellFormed,CircuitWellFormed]
  | @step start count head tail ih => exact (measuredIndexedStep_wellFormed r n start head).seq ih

/-- Every emitted inverse branch is well formed on the same per-index layout. -/
theorem measuredIndexedScheduleInverse_wellFormed (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) : (measuredIndexedScheduleInverse r n start count).WellFormed := by
  induction hl with
  | done start => simp [measuredIndexedScheduleInverse,AdaptiveCircuit.WellFormed,CircuitWellFormed]
  | @step start count head tail ih => exact ih.seq (measuredIndexedStepInverse_wellFormed r n start head)

/-- Sum of the proved H savings along the emitted chronological index interval. -/
def measuredScheduleSavings (n start : Nat) : Nat → Nat
  | 0 => 0
  | count+1 => measuredBlockHSavings n start + measuredScheduleSavings n (start+1) count

/-- Exact forward schedule savings, obtained by counting the actual emitted adaptive steps. -/
theorem measuredIndexedSchedule_toffoli (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) (hw : 2 ≤ r.lengthT.length) :
    (primitiveResources (measuredIndexedSchedule r n start count)).toffoli + measuredScheduleSavings n start count =
      (primitiveResources (indexedScheduleAdaptive r n start count)).toffoli := by
  induction hl with
  | done start => simp [measuredIndexedSchedule,indexedScheduleAdaptive,measuredScheduleSavings]
  | @step start count head tail ih =>
      have hh := measuredIndexedStep_toffoli r n start head hw
      simp only [measuredIndexedSchedule,indexedScheduleAdaptive,measuredScheduleSavings,
        primitiveResources_seq,PrimitiveResources.add]
      omega

/-- Exact descending schedule savings, with the same per-index sum. -/
theorem measuredIndexedScheduleInverse_toffoli (r : IndexedStepRegisters) (n start count : Nat)
    (hl : IndexedScheduleLayout r n start count) (hw : 2 ≤ r.lengthT.length) :
    (primitiveResources (measuredIndexedScheduleInverse r n start count)).toffoli + measuredScheduleSavings n start count =
      (primitiveResources (indexedScheduleInverseAdaptive r n start count)).toffoli := by
  induction hl with
  | done start => simp [measuredIndexedScheduleInverse,indexedScheduleInverseAdaptive,measuredScheduleSavings]
  | @step start count head tail ih =>
      have hh := measuredIndexedStepInverse_toffoli r n start head hw
      simp only [measuredIndexedScheduleInverse,indexedScheduleInverseAdaptive,measuredScheduleSavings,
        primitiveResources_seq,PrimitiveResources.add]
      omega
/-- Savings compose over adjacent chronological intervals. -/
theorem measuredScheduleSavings_add (n start a b : Nat) :
    measuredScheduleSavings n start (a+b) =
      measuredScheduleSavings n start a + measuredScheduleSavings n (start+a) b := by
  induction a generalizing start with
  | zero => simp [measuredScheduleSavings]
  | succ a ih =>
      simp only [Nat.succ_add,measuredScheduleSavings,ih]
      have hs : (start + a).succ = start + (a+1) := by omega
      rw [hs,Nat.add_assoc]

end
end ShorECDLP.Paper2607_13816
