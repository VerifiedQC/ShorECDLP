import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.Positions

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1 ShorECDLP.Challenge

/-- The candidate budget is independent of measurement positions and of the
extra work needed to implement fixed-shape exceptional-point corrections. -/
theorem streaming_candidate_budget (layout : DecodeLayout)
    (hk : layout.kind = .wrappedShift)
    (hp : layout.params = legacyDecoderParams) :
    layout.trials.length * decoderCandidateLimit layout.kind layout.params ≤ budget55 := by
  have hn := layout.trials_le
  have hc : decoderCandidateLimit layout.kind layout.params = 2^49 + 2 := by
    rw [hk, hp]
    decide +kernel
  rw [hc]
  exact Nat.mul_le_mul_right _ hn

theorem streaming_candidates_length (layout : DecodeLayout)
    (hk : layout.kind = .wrappedShift)
    (hp : layout.params = legacyDecoderParams) (history : List Bool) :
    (candidates layout history).length ≤ budget55 :=
  (candidates_length_trials layout history).trans (streaming_candidate_budget layout hk hp)

/-- Producer interface for the migrated program. Resource bounds deliberately
remain parameters: equality of execution does not establish syntactic costs,
and the fixed-shape correction can change both costs and record positions.
No instance of this structure is asserted for an unfinished migration. -/
structure StreamingAssembly (layout : DecodeLayout) (entry : StraightEntry)
    (bounds : Bounds) : Prop where
  kind : layout.kind = .wrappedShift
  precision : layout.params = legacyDecoderParams
  wellFormed : entry.program.WellFormed
  resources : ∀ Q : Point,
    (resources (entry.instantiate Q)).qubits ≤ bounds.qubits ∧
    (resources (entry.instantiate Q)).tModel ≤ bounds.tModel ∧
    (resources (entry.instantiate Q)).measurements ≤ bounds.measurements
  success : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q = d • G →
    (99 : ℝ) / 100 ≤ Instrument.bornMass
      ((entry.instantiate Q).run.filter (fun b => (verifiedCandidate layout Q b.history).isSome))
      (ket zeroBasisState)

/-- Assemble the protected certificate only after the actual producer proves
its semantic, physical and resource obligations. Budgets refer to this entry's
syntax, cursor and table, never to the legacy circuit's execution. -/
theorem StreamingAssembly.certificate {layout : DecodeLayout} {entry : StraightEntry}
    {bounds : Bounds} (h : StreamingAssembly layout entry bounds) (limits : Limits)
    (hg : entry.program.gateSlots ≤ limits.gateSlots)
    (hm : entry.finalCursor ≤ limits.measurements)
    (ht : entry.coefficients.length ≤ limits.coefficientRows)
    (hc : budget55 ≤ limits.candidateChecks) :
    Certificate limits layout entry bounds where
  gateBudget := hg
  recordBudget := hm
  tableBudget := ht
  candidateBudget := (streaming_candidate_budget layout h.kind h.precision).trans hc
  wellFormed := h.wellFormed
  resources := h.resources
  success := h.success

end ShorECDLP.Paper2607_13816.ChallengeMigration
