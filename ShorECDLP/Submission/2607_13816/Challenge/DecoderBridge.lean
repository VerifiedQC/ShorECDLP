import ShorECDLP.Submission.«2607_13816».Challenge.ActualPair
import ShorECDLP.Submission.«2607_13816».Window.RawDistribution
import ShorECDLP.Submission.«2607_13816».Window.Repetition
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
open scoped BigOperators

theorem fixedCandidates_legacy_eq (out : Fin (2^256) × Fin (2^208)) :
    fixedCandidates legacyDecoderParams out.1.val out.2.val = reducedShiftCandidates order 256 208 out := rfl

theorem wrappedPairAccept_legacy_iff (Q : Point) (out : Fin (2^256) × Fin (2^208)) :
    wrappedPairAccept legacyDecoderParams Q out.1.val out.2.val = true ↔
      (reducedVerifiedCandidate Q out).isSome = true := by
  classical
  rw [wrappedPairAccept,fixedCandidates_legacy_eq]
  simp only [List.find?_isSome,Finset.mem_toList,decide_eq_true_eq]
  unfold reducedVerifiedCandidate
  split_ifs with h
  · simp only [Option.isSome_some,iff_true]; exact h
  · simp only [Option.isSome_none,Bool.false_eq_true,iff_false]; exact h

attribute [local irreducible] wrappedPairAccept reducedVerifiedCandidate

theorem old_accept_implies_wrapped (Q : Point) (out : List Bool × List Bool)
    (h : reducedRawDecoderAccept Q out = true) :
    wrappedPairAccept legacyDecoderParams Q (fourierWordLSB out.1) (fourierWordLSB out.2) = true := by
  unfold reducedRawDecoderAccept reducedRawPublicDecode at h
  split_ifs at h with hl
  · let out' : Fin (2^256) × Fin (2^208) :=
      (⟨fourierWordLSB out.1, by simpa [hl.1] using fourierWordLSB_lt out.1⟩,
       ⟨fourierWordLSB out.2, by simpa [hl.2] using fourierWordLSB_lt out.2⟩)
    exact (wrappedPairAccept_legacy_iff Q out').mpr h
  · simp at h

theorem wrappedAccept_paperOutcomes (Q : Point) (out : Fin (2^256) × Fin (2^208)) :
    wrappedPairAccept legacyDecoderParams Q
      (fourierWordLSB (paperOutcomeBits 256 out.1)) (fourierWordLSB (paperOutcomeBits 208 out.2)) =
      reducedRawDecoderAccept Q (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [paperOutcomeBits_word]
  rw [wrappedPairAccept_legacy_iff]
  simp [reducedRawDecoderAccept,reducedRawPublicDecode,paperOutcomeBits_length,paperOutcomeBits_word]

theorem wrappedIdeal_mass_eq (Q : Point) (hG : G≠0) (hQ : Q≠0) (hrQ : order • Q=0) :
    reducedRawIdealFourierEventMass G Q
      (fun xy => wrappedPairAccept legacyDecoderParams Q (fourierWordLSB xy.1) (fourierWordLSB xy.2)) =
      reducedRawIdealFourierEventMass G Q (reducedRawDecoderAccept Q) := by
  rw [reducedRawIdealFourierEventMass_distribution G Q hG hQ generator_nsmul_eq_zero hrQ,
      reducedRawIdealFourierEventMass_distribution G Q hG hQ generator_nsmul_eq_zero hrQ]
  apply Finset.sum_congr rfl
  intro out _
  rw [wrappedAccept_paperOutcomes]

theorem wrappedIdeal_mass_lower (Q : Point) (hG : G≠0) (hQ : Q≠0) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    (163:ℝ)/1000 ≤ reducedRawIdealFourierEventMass G Q
      (fun xy => wrappedPairAccept legacyDecoderParams Q (fourierWordLSB xy.1) (fourierWordLSB xy.2)) := by
  rw [wrappedIdeal_mass_eq Q hG hQ hrQ,reducedRawIdealDecoder_eq Q hG hQ hrQ d hQd]
  exact secpSuccessBound_numeric.trans (reducedPhysicalVerifiedMass_lower Q hG hQ hrQ d hQd)
end ShorECDLP.Paper2607_13816.ChallengeMigration
