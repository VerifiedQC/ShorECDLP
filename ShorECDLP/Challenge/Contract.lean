import ShorECDLP.Challenge.Decoder
import ShorECDLP.Challenge.StraightLine
import ShorECDLP.Math.EllipticCurve.GeneratorOrder

namespace ShorECDLP.Challenge
open Quantum Secp256k1
noncomputable section

/-- Only the protected evaluator checks the public group relation. -/
def verifiedCandidate (layout : DecodeLayout) (Q : Point) (history : List Bool) :
    Option (ZMod order) := by
  classical
  exact (candidates layout history).find? (fun c => decide (c.val • G = Q))

theorem verifiedCandidate_mem (layout : DecodeLayout) (Q : Point)
    (history : List Bool) (c : ZMod order)
    (h : verifiedCandidate layout Q history = some c) :
    c ∈ candidates layout history ∧ c.val • G = Q := by
  classical
  have hf := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  exact ⟨hf, of_decide_eq_true hp⟩

theorem verifiedCandidate_sound (layout : DecodeLayout) (Q : Point)
    (d : Nat) (hd : Q = d • G) (history : List Bool) (c : ZMod order)
    (h : verifiedCandidate layout Q history = some c) : c = (d : ZMod order) := by
  have he := (verifiedCandidate_mem layout Q history c h).2
  rw [hd, nsmul_eq_nsmul_iff_modEq, generator_order,
    ← ZMod.natCast_eq_natCast_iff] at he
  letI : NeZero order := ⟨order_prime.ne_zero⟩
  simpa only [ZMod.natCast_zmod_val] using he

/-- Declared upper bounds, not submitted counter implementations. -/
structure Bounds where
  qubits : Nat
  tModel : Nat
  measurements : Nat

/-- Organizer-selected admission limits, fixed before submissions are scored.
These values must NOT be supplied by the entrant in the release harness. -/
structure Limits where
  gateSlots : Nat
  measurements : Nat
  coefficientRows : Nat
  candidateChecks : Nat

/-- Named organizer policy options. Neither is a default. -/
def budget48 : Nat := 2^48
def budget55 : Nat := 56 * (2^49 + 2)

/-- The decoder algorithm is protected; the submission supplies only index data.
All resource and probability expressions refer to the SAME instantiated circuit.
This semantic interface is not yet the isolated benchmark runner. -/
structure Certificate (limits : Limits) (layout : DecodeLayout) (e : StraightEntry) (bounds : Bounds) : Prop where
  gateBudget : e.program.gateSlots ≤ limits.gateSlots
  recordBudget : e.finalCursor ≤ limits.measurements
  tableBudget : e.coefficients.length ≤ limits.coefficientRows
  candidateBudget : layout.trials.length * trialCandidateLimit layout.params ≤ limits.candidateChecks
  wellFormed : e.program.WellFormed
  resources : ∀ Q : Point,
    (resources (e.instantiate Q)).qubits ≤ bounds.qubits ∧
    (resources (e.instantiate Q)).tModel ≤ bounds.tModel ∧
    (resources (e.instantiate Q)).measurements ≤ bounds.measurements
  success : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q = d • G →
    (99 : ℝ) / 100 ≤ Instrument.bornMass
      ((e.instantiate Q).run.filter (fun b => (verifiedCandidate layout Q b.history).isSome))
      (ket zeroBasisState)

theorem Certificate.candidateChecks_le {limits : Limits} {layout : DecodeLayout}
    {e : StraightEntry} {bounds : Bounds} (h : Certificate limits layout e bounds)
    (history : List Bool) : (candidates layout history).length ≤ limits.candidateChecks :=
  (candidates_length_trials layout history).trans h.candidateBudget

def declaredScore (bounds : Bounds) : Nat := bounds.tModel

end
end ShorECDLP.Challenge
