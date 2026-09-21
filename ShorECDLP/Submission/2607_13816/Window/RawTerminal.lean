import ShorECDLP.Submission.«2607_13816».Window.RawInterference
import ShorECDLP.Submission.«2607_13816».Window.ReducedOutcomes
import ShorECDLP.Framework.Quantum.TerminalInterference
import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedVerified
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual raw arithmetic followed by the two adaptive Fourier measurements. -/
def reducedRawFourierProgram (P Q : Point) : AdaptiveCircuit :=
  (reducedRawProgram P Q).seq reducedFourierProgram

def decodeReducedRawFourier (P Q : Point) (hist : List Bool) :
    Option (List Bool × List Bool) :=
  (consumeAdaptiveHistory (reducedRawProgram P Q) hist).map decodeReducedFourier

/-- Select an output event from the actual terminal histories. -/
def reducedFourierSelection (accept : List Bool × List Bool → Bool) : Instrument :=
  reducedFourierProgram.run.filter (fun b => accept (decodeReducedFourier b.history))

theorem reducedRawFourier_filter (P Q : Point) (accept : List Bool × List Bool → Bool) :
    (reducedRawProgram P Q).run.seq (reducedFourierSelection accept) =
    (reducedRawFourierProgram P Q).run.filter
      (fun b => ((decodeReducedRawFourier P Q b.history).map accept).getD false) := by
  rw [reducedRawFourierProgram, AdaptiveCircuit.run_seq]
  exact adaptiveTerminalFilter _ _ _ _ (by
    intro first hf second _
    simp [decodeReducedRawFourier, InstrumentBranch.seq, consumeAdaptiveHistory_run _ first hf])

theorem reducedFourierProgram_wellFormed : reducedFourierProgram.WellFormed :=
  (semiclassicalFourier_wellFormed _ _ _).seq (semiclassicalFourier_wellFormed _ _ _)

theorem reducedFourierSelection_contractive (accept : List Bool × List Bool → Bool) (ψ : State) :
    (reducedFourierSelection accept).bornMass ψ ≤ normSq ψ := by
  apply (Instrument.bornMass_filter_le _ _ _).trans
  exact le_of_eq (AdaptiveCircuit.run_preservesBornMass _ reducedFourierProgram_wellFormed ψ)

/-- A contractive terminal instrument can select histories as well as final states. -/
theorem reducedRawTerminal_bounds (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (J : Instrument)
    (hJ : ∀ ψ, J.bornMass ψ ≤ normSq ψ) :
    (9/16:ℝ)*J.bornMass ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) reducedRawEntryState)
      - 147/16384 ≤ ((reducedRawProgram P Q).run.seq J).bornMass reducedRawEntryState ∧
    ((reducedRawProgram P Q).run.seq J).bornMass reducedRawEntryState ≤
      (25/16:ℝ)*J.bornMass ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) reducedRawEntryState)
      + 315/16384 := by
  let good := reducedRawEntryState.filter (reducedRawExclusions P Q hP hQ hrP hrQ)
  let bad := reducedRawEntryState.filter (fun s => ¬reducedRawExclusions P Q hP hQ hrP hrQ s)
  let ideal := Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)
  let I := (reducedRawProgram P Q).run.seq J
  have hb : I.bornMass bad ≤ (7:ℝ)/4096 := by
    apply (Instrument.seq_bornMass_le _ J hJ bad).trans
    rw [reducedRawProgram_bornMass]
    exact reducedRawEntry_excluded_mass P Q hP hQ hrP hrQ
  have hg : I.bornMass good = J.bornMass (ideal good) := by
    apply (reducedRaw_registers_coherent P Q hP hQ hrP hrQ).terminalMass
    intro s hs
    have he : reducedRawExclusions P Q hP hQ hrP hrQ s := by
      by_contra hn
      exact hs (by simp [good, hn])
    exact ⟨reducedRawEntryState_supported s (by simpa [good, he] using hs), he⟩
  have he : good+bad=reducedRawEntryState := Finsupp.filter_pos_add_filter_neg _ _
  have hr := I.bornMass_interference good bad
  rw [he, hg] at hr
  have hib : J.bornMass (ideal bad) ≤ (7:ℝ)/4096 := by
    apply (hJ _).trans
    rw [reducedScalarOutput_normSq P Q bad (by
      intro s hs
      apply reducedRawEntryState_supported s
      intro hz
      exact hs (by simp [bad, Finsupp.filter_apply, hz]))]
    exact reducedRawEntry_excluded_mass P Q hP hQ hrP hrQ
  have hd : ideal good=ideal reducedRawEntryState + -(ideal bad) := by
    rw [←he, map_add]; abel
  have hi := J.bornMass_interference (ideal reducedRawEntryState) (-(ideal bad))
  rw [←hd, Instrument.bornMass_neg] at hi
  constructor <;> linarith [hr.1, hr.2, hi.1, hi.2]

/-- Unconditional event mass, summing every accepted arithmetic/Fourier history. -/
def reducedRawFourierEventMass (P Q : Point) (accept : List Bool × List Bool → Bool) : ℝ :=
  Instrument.bornMass ((reducedRawFourierProgram P Q).run.filter
    (fun b => ((decodeReducedRawFourier P Q b.history).map accept).getD false)) reducedRawEntryState

/-- Accepted histories have at most unit mass on the full physical entry. -/
theorem reducedRawFourierEventMass_le_one (P Q : Point) (accept : List Bool × List Bool → Bool) :
    reducedRawFourierEventMass P Q accept ≤ 1 := by
  unfold reducedRawFourierEventMass
  rw [←reducedRawFourier_filter]
  apply (Instrument.seq_bornMass_le _ _ (reducedFourierSelection_contractive accept) _).trans
  rw [reducedRawProgram_bornMass, reducedRawEntryState_normSq]

/-- The same selected Fourier instrument on the full ideal scalar state. -/
def reducedRawIdealFourierEventMass (P Q : Point) (accept : List Bool × List Bool → Bool) : ℝ :=
  (reducedFourierSelection accept).bornMass
    ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) reducedRawEntryState)

theorem reducedRawFourierEvent_bounds (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (accept : List Bool × List Bool → Bool) :
    (9/16:ℝ)*reducedRawIdealFourierEventMass P Q accept -147/16384 ≤
      reducedRawFourierEventMass P Q accept ∧
    reducedRawFourierEventMass P Q accept ≤
      (25/16:ℝ)*reducedRawIdealFourierEventMass P Q accept +315/16384 := by
  unfold reducedRawFourierEventMass reducedRawIdealFourierEventMass
  rw [←reducedRawFourier_filter]
  exact reducedRawTerminal_bounds P Q hP hQ hrP hrQ _ (reducedFourierSelection_contractive accept)
/-- Decode chronological Fourier bits, rejecting malformed lengths. -/
def reducedRawPublicDecode (Q : Point) (out : List Bool × List Bool) : Option (ZMod order) :=
  if h : out.1.length=256 ∧ out.2.length=208 then
    reducedVerifiedCandidate Q
      (⟨fourierWordLSB out.1, by simpa [h.1] using fourierWordLSB_lt out.1⟩,
       ⟨fourierWordLSB out.2, by simpa [h.2] using fourierWordLSB_lt out.2⟩)
  else none

/-- Every returned candidate is verified against the public point. -/
theorem reducedRawPublicDecode_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (out : List Bool × List Bool) (c : ZMod order)
    (hc : reducedRawPublicDecode Q out=some c) : c=(d:ZMod order) := by
  unfold reducedRawPublicDecode at hc
  split_ifs at hc with h
  · exact reducedVerifiedCandidate_sound Q d hQd _ c hc

/-- The selected history event uses the public-point decoder, not a hidden scalar test. -/
def reducedRawDecoderAccept (Q : Point) (out : List Bool × List Bool) : Bool :=
  (reducedRawPublicDecode Q out).isSome

theorem reducedRawDecoderAccept_correct (Q : Point) (d : Nat) (hQd : Q=d • G)
    (out : List Bool × List Bool) :
    reducedRawDecoderAccept Q out=true ↔ reducedRawPublicDecode Q out=some (d:ZMod order) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    rw [reducedRawPublicDecode_sound Q d hQd out c hc] at hc
    exact hc
  · intro h
    simp [reducedRawDecoderAccept, h]

/-- Actual accepted-history mass compared with the full ideal accepted-history mass.
A numerical success bound still requires a lower bound on the ideal event on this entry. -/
theorem reducedRawDecoder_bounds (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) :
    (9/16:ℝ)*reducedRawIdealFourierEventMass G Q (reducedRawDecoderAccept Q) -147/16384 ≤
      reducedRawFourierEventMass G Q (reducedRawDecoderAccept Q) ∧
    reducedRawFourierEventMass G Q (reducedRawDecoderAccept Q) ≤
      (25/16:ℝ)*reducedRawIdealFourierEventMass G Q (reducedRawDecoderAccept Q) +315/16384 :=
  reducedRawFourierEvent_bounds G Q hG hQ generator_nsmul_eq_zero hrQ _

end
end ShorECDLP.Paper2607_13816
