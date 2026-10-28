import ShorECDLP.Submission.«2607_13816».Challenge.UniformT
import ShorECDLP.Submission.«2607_13816».Challenge.CompleteSupport
import ShorECDLP.Submission.«2607_13816».Challenge.WindowSlots
import ShorECDLP.Submission.«2607_13816».Challenge.ActualPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] batchedOuterPlan coefficientTable OuterPlan.repeat

/-- Generic packaging avoids unfolding a large coefficient table to transport its length. -/
def fixedTableEntry {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) : StraightEntry where
  coefficients := List.ofFn f
  finalCursor := e
  program := reindexStraight (Fin.cast List.length_ofFn.symm) p

private theorem ofFn_read {n : Nat} (f : Fin n → PointCoeff) (Q : Point) :
    (fun r : ConstantBit n => readConstant (List.ofFn f).get Q
      ⟨Fin.cast (List.length_ofFn).symm r.point, r.field, r.bit⟩) =
      readConstant f Q := by
  funext r
  simp only [readConstant,List.get_eq_getElem,List.getElem_ofFn,Fin.val_cast,Fin.eta]

theorem fixedTableEntry_instantiate {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (fixedTableEntry f p).instantiate Q = p.instantiate (readConstant f Q) Fin.elim0 := by
  dsimp only [fixedTableEntry,StraightEntry.instantiate]
  rw [reindexStraight_instantiate]
  simp only [Function.comp_def,reindexBit]
  rw [ofFn_read]

theorem fixedTableEntry_slots {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).program.gateSlots = p.gateSlots :=
  reindexStraight_gateSlots _ _

theorem fixedTableEntry_wellFormed {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).program.WellFormed ↔ p.WellFormed :=
  reindexStraight_wellFormed _ _

theorem fixedTableEntry_cursor {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).finalCursor = e := rfl

theorem fixedTableEntry_rows {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).coefficients.length = n := List.length_ofFn

private theorem resource_t (c : AdaptiveCircuit) : (resources c).tModel = c.tCount := rfl
private theorem resource_m (c : AdaptiveCircuit) : (resources c).measurements = c.measurementCount := rfl
private theorem resource_q (c : AdaptiveCircuit) : (resources c).qubits = c.qubitCount := rfl

theorem fixedTableEntry_measurements {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (resources ((fixedTableEntry f p).instantiate Q)).measurements = e := by
  rw [resource_m,fixedTableEntry_instantiate,Straight.measurementCount,Nat.sub_zero]

/-- The actual fixed 56-round producer, using the public coefficient table. -/
def streamingEntry : StraightEntry := fixedTableEntry coefficientAt (batchedOuterPlan.repeat 56 0)

theorem streamingEntry_instantiate (Q : Point) :
    streamingEntry.instantiate Q =
      (batchedOuterPlan.repeat 56 0).instantiate (readConstant coefficientAt Q) Fin.elim0 :=
  fixedTableEntry_instantiate _ _ Q

attribute [local irreducible] streamingEntry fixedTableEntry

/-- Upper bounds; the qubit bound is not an exact cardinality claim. -/
def streamingBounds : Bounds := ⟨3932,806028979896,48194018992⟩

theorem streamingEntry_qubitCount (Q : Point) :
    (streamingEntry.instantiate Q).qubitCount ≤ 3932 := by
  rw [streamingEntry_instantiate]
  simpa only [AdaptiveCircuit.qubitCount,List.card_toFinset] using
    batchedOuter_qubits_le_3932 56 0 (readConstant coefficientAt Q) Fin.elim0

theorem streamingEntry_tModel (Q : Point) :
    (resources (streamingEntry.instantiate Q)).tModel ≤ 806028979896 := by
  rw [resource_t,streamingEntry_instantiate]
  exact batchedOuterPlan_total_t_uniform Q

theorem streamingEntry_measurements (Q : Point) :
    (resources (streamingEntry.instantiate Q)).measurements = 48194018992 := by
  rw [streamingEntry,fixedTableEntry_measurements,Nat.zero_add]
  exact batchedOuterPlan_finalCursor

theorem streamingEntry_resources (Q : Point) :
    (resources (streamingEntry.instantiate Q)).qubits ≤ streamingBounds.qubits ∧
    (resources (streamingEntry.instantiate Q)).tModel ≤ streamingBounds.tModel ∧
    (resources (streamingEntry.instantiate Q)).measurements ≤ streamingBounds.measurements := by
  rw [resource_q]
  exact ⟨streamingEntry_qubitCount Q,streamingEntry_tModel Q,(streamingEntry_measurements Q).le⟩

theorem streamingEntry_gateSlots : streamingEntry.program.gateSlots ≤ 5000000000000 := by
  simpa only [streamingEntry,fixedTableEntry_slots] using batchedOuterPlan_slots 0

theorem streamingEntry_gateBudget : streamingEntry.program.gateSlots ≤ officialLimits.gateSlots :=
  streamingEntry_gateSlots.trans (by decide)

theorem streamingEntry_finalCursor : streamingEntry.finalCursor = 48194018992 := by
  unfold streamingEntry
  exact (fixedTableEntry_cursor coefficientAt (batchedOuterPlan.repeat 56 0)).trans
    ((Nat.zero_add _).trans batchedOuterPlan_finalCursor)

theorem streamingEntry_recordBudget : streamingEntry.finalCursor ≤ officialLimits.measurements :=
  streamingEntry_finalCursor.le.trans (by decide)

theorem streamingEntry_tableBudget : streamingEntry.coefficients.length ≤ officialLimits.coefficientRows := by
  rw [streamingEntry,fixedTableEntry_rows]
  exact Nat.le_refl _

theorem streamingEntry_candidateBudget :
    batchedOuterPlan.layout.trials.length *
      decoderCandidateLimit batchedOuterPlan.layout.kind batchedOuterPlan.layout.params ≤
      officialLimits.candidateChecks := by
  exact streaming_candidate_budget batchedOuterPlan.layout rfl rfl

theorem streamingEntry_wellFormed : streamingEntry.program.WellFormed := by
  rw [streamingEntry]
  exact (fixedTableEntry_wellFormed _ _).mpr (batchedOuterPlan_repeat_wellFormed 56 0)

/-- Only success remains an input: all physical, syntactic and resource fields
refer to this actual fixed entry. This conditional shell is not an accepted submission. -/
theorem streamingEntry_certificate
    (success : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q = d • G →
      (99 : ℝ)/100 ≤ Instrument.bornMass
        ((streamingEntry.instantiate Q).run.filter
          (fun b => (verifiedCandidate batchedOuterPlan.layout Q b.history).isSome))
        (ket zeroBasisState)) :
    Certificate officialLimits batchedOuterPlan.layout streamingEntry streamingBounds where
  gateBudget := streamingEntry_gateBudget
  recordBudget := streamingEntry_recordBudget
  tableBudget := streamingEntry_tableBudget
  candidateBudget := streamingEntry_candidateBudget
  wellFormed := streamingEntry_wellFormed
  resources := streamingEntry_resources
  success := success
end ShorECDLP.Paper2607_13816.ChallengeMigration
