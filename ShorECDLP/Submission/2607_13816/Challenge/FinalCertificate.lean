import ShorECDLP.Submission.«2607_13816».Challenge.ResourceCertificate
import ShorECDLP.Submission.«2607_13816».Challenge.RepeatEvent
import ShorECDLP.Submission.«2607_13816».Challenge.IdealDistribution
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] batchedOuterPlan actualRoundSource streamingEntry

theorem publicPoint_order (Q : Point) (d : Nat) (h : Q=d • G) : order • Q=0 := by
  rw [h,smul_comm,generator_nsmul_eq_zero,nsmul_zero]

theorem actualRoundAcceptedMass_le_one (Q : Point) (hQ : order • Q=0) :
    Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState) ≤ 1 := by
  exact (Instrument.bornMass_filter_le _ _ _).trans_eq (actualRoundSource_total Q hQ)

theorem actualCompiledRepeat_success_of_round (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (h : (163:ℝ)/1000 ≤ Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState)) :
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((((batchedOuterPlan.repeat 56 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate batchedOuterPlan.layout Q b.history).isSome)) (ket zeroBasisState) := by
  rw [actualCompiledRepeat_verified_mass Q hQ hn]
  have hm := independentRetrySuccessProbability_mono 56 (actualRoundAcceptedMass_le_one Q hQ) h
  have hnum : (99:ℝ)/100 ≤ independentRetrySuccessProbability ((163:ℝ)/1000) 56 := by
    norm_num [independentRetrySuccessProbability]
  exact hnum.trans hm

/-- Actual single-round accepted mass, with the protected decoder and no loss term. -/
theorem streamingRound_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d • G) :
    (163:ℝ)/1000 ≤ Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState) := by
  have hQ := publicPoint_order Q d hd
  rw [actualRoundSource_fixedPair_mass Q hQ hn,selectedIdealTwoAxes_event_eq Q hQ hn]
  exact wrappedIdeal_mass_lower Q G_ne_zero hn hQ d hd

/-- Success of the actual fixed 56-round entry, measured by the protected final decoder. -/
theorem streamingEntry_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((streamingEntry.instantiate Q).run.filter
        (fun b => (verifiedCandidate batchedOuterPlan.layout Q b.history).isSome))
      (ket zeroBasisState) := by
  rw [streamingEntry_instantiate]
  exact actualCompiledRepeat_success_of_round Q (publicPoint_order Q d hd) hn
    (streamingRound_success Q d hn hd)

/-- Unconditional protected certificate for the actual fixed streaming submission. -/
theorem streamingEntry_certificate_unconditional :
    Certificate officialLimits batchedOuterPlan.layout streamingEntry streamingBounds :=
  streamingEntry_certificate streamingEntry_success
end ShorECDLP.Paper2607_13816.ChallengeMigration
