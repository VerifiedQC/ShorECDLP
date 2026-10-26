import ShorECDLP.Submission.Naive.Challenge.RecordPositions
import ShorECDLP.Framework.Quantum.TerminalInterference

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge
noncomputable section

def repeatedDecodeLayout : DecodeLayout where
  kind := .nearestPair
  params := repeatedDecoderParams
  trials := List.ofFn repeatedTrialPositions
  trials_le := by simp

theorem repeated_success_candidate (d : Nat) (history : List Bool)
    (hl : history.length = 5385536) (hs : fixedRepeatedSuccess d history = true) :
    (d : ZMod order) ∈ candidates repeatedDecodeLayout history := by
  obtain ⟨t, a, b, ha, hb, hp⟩ := fixedRepeatedSuccess_actualWords d history hl hs
  apply List.mem_flatMap.mpr
  refine ⟨repeatedTrialPositions t, List.mem_ofFn.mpr ⟨t, rfl⟩, ?_⟩
  change (d : ZMod order) ∈ decodeTrial .nearestPair repeatedDecoderParams history (repeatedTrialPositions t)
  simp only [decodeTrial, ha, hb]
  have hp' := of_decide_eq_true hp
  simp only [nearestPairCandidates, repeatedDecoderParams, ↓reduceIte]
  rw [hp']
  simp

theorem repeated_success_verified (Q : Point) (d : Nat) (hd : Q = d • G)
    (history : List Bool) (hl : history.length = 5385536)
    (hs : fixedRepeatedSuccess d history = true) :
    (verifiedCandidate repeatedDecodeLayout Q history).isSome = true := by
  classical
  have hm := repeated_success_candidate d history hl hs
  have he : (d : ZMod order).val • G = Q := by
    rw [hd, ZMod.val_natCast]
    exact nsmul_mod_order G (by simpa using dlogPoint_order 1) d
  unfold verifiedCandidate
  exact List.find?_isSome.mpr ⟨_, hm, by simpa using he⟩

theorem bornMass_filter_mono (I : Instrument) (p q : InstrumentBranch → Bool)
    (h : ∀ b ∈ I, p b = true → q b = true) (ψ : State) :
    Instrument.bornMass (I.filter p) ψ ≤ Instrument.bornMass (I.filter q) ψ := by
  have he : (I.filter q).filter p = I.filter p := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro b hb
    by_cases hp : p b = true
    · simp [hp, h b hb hp]
    · simp [hp]
  rw [← he]
  exact Instrument.bornMass_filter_le _ _ _

theorem naiveRepeatedEntry_verified_success (Q : Point) (d : Nat)
    (hd : Q = d • G) (hn : Q ≠ 0) :
    (99/100 : ℝ) ≤ Instrument.bornMass
      ((naiveRepeatedEntry.instantiate Q).run.filter
        (fun b => (verifiedCandidate repeatedDecodeLayout Q b.history).isSome))
      (ket zeroBasisState) := by
  apply (naiveRepeatedEntry_success Q d hd hn).trans
  apply bornMass_filter_mono
  intro b hb hs
  have ho : order • Q = 0 := by rw [hd]; exact dlogPoint_order d
  exact repeated_success_verified Q d hd b.history
    (naiveRepeatedEntry_history_length Q ho b hb) hs

attribute [local irreducible] Straight.WellFormed repeatedProgram naivePowerTable

theorem repeatedDecodeLayout_candidates_bound (history : List Bool) :
    (candidates repeatedDecodeLayout history).length ≤ 26 := by
  simpa [repeatedDecodeLayout, decoderCandidateLimit] using
    candidates_length_trials repeatedDecodeLayout history

/-- Admission is conditional only on the organizer's limits covering this fixed
entry. The resource expressions cover all 26 rounds; their numeric evaluation
is a separate publication obligation. -/
theorem naiveRepeatedEntry_certificate (limits : Limits)
    (hg : naiveRepeatedEntry.program.gateSlots ≤ limits.gateSlots)
    (hm : 5385536 ≤ limits.measurements)
    (ht : 512 ≤ limits.coefficientRows)
    (hc : 26 ≤ limits.candidateChecks) :
    Certificate limits repeatedDecodeLayout naiveRepeatedEntry repeatedStaticBounds where
  gateBudget := hg
  recordBudget := hm
  tableBudget := by simpa only [naiveRepeatedEntry, naivePowerTable_length] using ht
  candidateBudget := by simpa [repeatedDecodeLayout, decoderCandidateLimit] using hc
  wellFormed := naiveRepeatedEntry_wellFormed
  resources := by
    intro Q
    obtain ⟨hq, ht, hm⟩ := naiveRepeatedEntry_resources Q
    exact ⟨hq, ht, hm.le⟩
  success := fun Q d hn hd => naiveRepeatedEntry_verified_success Q d hd hn

end
end ShorECDLP.NaiveChallenge
