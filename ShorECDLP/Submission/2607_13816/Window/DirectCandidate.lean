import ShorECDLP.Submission.«2607_13816».Window.DirectResetOutcomes
import ShorECDLP.Submission.«2607_13816».Window.Candidate
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem word_outcome (v : Fin (2^257)) :
    windowWordOutcome (paperOutcomeBits 257 v)=some v := by
  simp only [windowWordOutcome,paperOutcomeBits_word,dif_pos v.isLt]
/-- Read the two output words of the actual reset trial. -/
def resetDirectWindowFiniteDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (Fin (2^257) × Fin (2^257)) := do
  let bits ← resetDirectWindowDecode Q hrQ hist
  let a ← windowWordOutcome bits.1
  let b ← windowWordOutcome bits.2
  some (a,b)
private theorem finite_decode_of_bits (Q : Point) (hrQ : order • Q=0) (hist : List Bool)
    (out : Fin (2^257) × Fin (2^257))
    (h : resetDirectWindowDecode Q hrQ hist=some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2)) :
    resetDirectWindowFiniteDecode Q hrQ hist=some out := by
  simp only [resetDirectWindowFiniteDecode,h,Bind.bind,Option.bind,word_outcome]
private theorem reset_decode_total (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetDirectWindowTrial Q hrQ).run) :
    ∃ out : Fin (2^257) × Fin (2^257), resetDirectWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  rw [resetDirectWindowTrial,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,hbefore,hrest⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,hafter,rfl⟩ := List.mem_map.mp hrest
  obtain ⟨out,ho⟩ := directSecpWindowDecode_total Q hrQ before hbefore
  refine ⟨out,?_⟩
  simp only [resetDirectWindowDecode,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hbefore,
    Option.bind,Bind.bind,List.length_append,Nat.add_sub_cancel_right,List.take_left,ho]
private theorem finite_decode_iff (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetDirectWindowTrial Q hrQ).run) (out : Fin (2^257) × Fin (2^257)) :
    resetDirectWindowFiniteDecode Q hrQ b.history=some out ↔ resetDirectWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  constructor
  · intro h
    obtain ⟨v,hv⟩ := reset_decode_total Q hrQ b hb
    have he := Option.some.inj ((finite_decode_of_bits Q hrQ b.history v hv).symm.trans h)
    exact he ▸ hv
  · exact finite_decode_of_bits Q hrQ b.history out

theorem resetDirectWindowFiniteOutputMass (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^257) × Fin (2^257)) :
    Instrument.bornMass ((resetDirectWindowTrial Q hrQ).run.filter
      (fun b => resetDirectWindowFiniteDecode Q hrQ b.history==some out)) (ket zeroBasisState)=
      secpWindowOutputMass Q hrQ out := by
  have he : (resetDirectWindowTrial Q hrQ).run.filter
      (fun b => resetDirectWindowFiniteDecode Q hrQ b.history==some out)=
      (resetDirectWindowTrial Q hrQ).run.filter (fun b => resetDirectWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2)) := by
    apply List.filter_congr
    intro b hb
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact finite_decode_iff Q hrQ b hb out
  rw [he]
  exact resetDirectWindowOutputMass_physical Q hrQ out
/-- The classical decoder specification checks the candidate against the public point. -/
def resetDirectWindowCandidate (Q : Point) (hrQ : order • Q=0) (hist : List Bool) : Option (ZMod order) :=
  (resetDirectWindowFiniteDecode Q hrQ hist).bind (secpWindowVerifiedCandidate Q)

theorem resetDirectWindowCandidate_sound (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) (c : ZMod order) (hc : resetDirectWindowCandidate Q hrQ hist=some c) : c=(d:ZMod order) := by
  obtain ⟨out,_,ho⟩ := Option.bind_eq_some_iff.mp hc
  exact secpWindowVerifiedCandidate_sound Q d hQd out c ho

theorem resetDirectWindowCandidate_mass (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass ((resetDirectWindowTrial Q hrQ).run.filter
      (fun b => (resetDirectWindowCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)=
      secpWindowSuccessMass Q hrQ d := by
  have ha (out : Fin (2^257) × Fin (2^257)) :
      (secpWindowVerifiedCandidate Q out).isSome ↔ secpWindowPostprocess Q out=some (d:ZMod order) := by
    constructor
    · intro h
      obtain ⟨c,hc⟩ := Option.isSome_iff_exists.mp h
      have he := secpWindowVerifiedCandidate_sound Q d hQd out c hc
      exact (secpWindowVerifiedCandidate_complete Q d hQd out).mp (he ▸ hc)
    · intro h
      rw [(secpWindowVerifiedCandidate_complete Q d hQd out).mpr h]
      rfl
  have hp := selectedDecode_mass (resetDirectWindowTrial Q hrQ).run
    (fun b => resetDirectWindowFiniteDecode Q hrQ b.history)
    (fun out => (secpWindowVerifiedCandidate Q out).isSome) (ket zeroBasisState)
  simp only [resetDirectWindowFiniteOutputMass,ha] at hp
  have he (hist : List Bool) : (resetDirectWindowCandidate Q hrQ hist).isSome=
      (resetDirectWindowFiniteDecode Q hrQ hist).any (fun out => (secpWindowVerifiedCandidate Q out).isSome) := by
    unfold resetDirectWindowCandidate
    cases resetDirectWindowFiniteDecode Q hrQ hist <;> rfl
  simp only [he]
  exact hp
end
end ShorECDLP.Paper2607_13816
