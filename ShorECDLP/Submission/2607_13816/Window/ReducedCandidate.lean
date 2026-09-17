import ShorECDLP.Submission.«2607_13816».Window.ReducedResetOutcomes
import ShorECDLP.Submission.«2607_13816».Window.Candidate
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
def reducedWordOutcome (n : Nat) (bits : List Bool) : Option (Fin (2^n)) :=
  if h : fourierWordLSB bits<2^n then some ⟨fourierWordLSB bits,h⟩ else none
private theorem word_outcome (n : Nat) (v : Fin (2^n)) :
    reducedWordOutcome n (paperOutcomeBits n v)=some v := by
  simp only [reducedWordOutcome,paperOutcomeBits_word,dif_pos v.isLt]
/-- Read the two output words of the actual reset trial. -/
def resetReducedWindowFiniteDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (Fin (2^256) × Fin (2^208)) := do
  let bits ← resetReducedWindowDecode Q hrQ hist
  let a ← reducedWordOutcome 256 bits.1
  let b ← reducedWordOutcome 208 bits.2
  some (a,b)
private theorem finite_decode_of_bits (Q : Point) (hrQ : order • Q=0) (hist : List Bool)
    (out : Fin (2^256) × Fin (2^208))
    (h : resetReducedWindowDecode Q hrQ hist=some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2)) :
    resetReducedWindowFiniteDecode Q hrQ hist=some out := by
  simp only [resetReducedWindowFiniteDecode,h,Bind.bind,Option.bind,word_outcome]
private theorem reset_decode_total (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetReducedWindowTrial Q hrQ).run) :
    ∃ out : Fin (2^256) × Fin (2^208), resetReducedWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) := by
  rw [resetReducedWindowTrial,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,hbefore,hrest⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,hafter,rfl⟩ := List.mem_map.mp hrest
  obtain ⟨out,ho⟩ := reducedSecpWindowDecode_total Q hrQ before hbefore
  refine ⟨out,?_⟩
  simp only [resetReducedWindowDecode,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hbefore,
    Option.bind,Bind.bind,List.length_append,Nat.add_sub_cancel_right,List.take_left,ho]
private theorem finite_decode_iff (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetReducedWindowTrial Q hrQ).run) (out : Fin (2^256) × Fin (2^208)) :
    resetReducedWindowFiniteDecode Q hrQ b.history=some out ↔ resetReducedWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) := by
  constructor
  · intro h
    obtain ⟨v,hv⟩ := reset_decode_total Q hrQ b hb
    have he := Option.some.inj ((finite_decode_of_bits Q hrQ b.history v hv).symm.trans h)
    exact he ▸ hv
  · exact finite_decode_of_bits Q hrQ b.history out

theorem resetReducedWindowFiniteOutputMass (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^256) × Fin (2^208)) :
    Instrument.bornMass ((resetReducedWindowTrial Q hrQ).run.filter
      (fun b => resetReducedWindowFiniteDecode Q hrQ b.history==some out)) (ket zeroBasisState)=
      reducedSecpWindowOutputMass Q hrQ out := by
  have he : (resetReducedWindowTrial Q hrQ).run.filter
      (fun b => resetReducedWindowFiniteDecode Q hrQ b.history==some out)=
      (resetReducedWindowTrial Q hrQ).run.filter (fun b => resetReducedWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2)) := by
    apply List.filter_congr
    intro b hb
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact finite_decode_iff Q hrQ b hb out
  rw [he]
  exact resetReducedWindowOutputMass_physical Q hrQ out
/-- The classical decoder specification checks the candidate against the public point. -/
def resetReducedWindowCandidate (Q : Point) (hrQ : order • Q=0) (hist : List Bool) : Option (ZMod order) :=
  (resetReducedWindowFiniteDecode Q hrQ hist).bind (reducedSecpWindowPostprocess Q)

theorem resetReducedWindowCandidate_sound (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) (c : ZMod order) (hc : resetReducedWindowCandidate Q hrQ hist=some c) : c=(d:ZMod order) := by
  obtain ⟨out,_,ho⟩ := Option.bind_eq_some_iff.mp hc
  exact reducedSecpWindowPostprocess_sound Q d hQd out c ho

theorem resetReducedWindowCandidate_mass (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass ((resetReducedWindowTrial Q hrQ).run.filter
      (fun b => (resetReducedWindowCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)=
      reducedSecpWindowSuccessMass Q hrQ d := by
  have ha (out : Fin (2^256) × Fin (2^208)) :
      (reducedSecpWindowPostprocess Q out).isSome ↔ reducedSecpWindowPostprocess Q out=some (d:ZMod order) := by
    constructor
    · intro h
      obtain ⟨c,hc⟩ := Option.isSome_iff_exists.mp h
      have he := reducedSecpWindowPostprocess_sound Q d hQd out c hc
      exact he ▸ hc
    · intro h
      rw [h]
      rfl
  have hp := selectedDecode_mass (resetReducedWindowTrial Q hrQ).run
    (fun b => resetReducedWindowFiniteDecode Q hrQ b.history)
    (fun out => (reducedSecpWindowPostprocess Q out).isSome) (ket zeroBasisState)
  simp only [resetReducedWindowFiniteOutputMass,ha] at hp
  have he (hist : List Bool) : (resetReducedWindowCandidate Q hrQ hist).isSome=
      (resetReducedWindowFiniteDecode Q hrQ hist).any (fun out => (reducedSecpWindowPostprocess Q out).isSome) := by
    unfold resetReducedWindowCandidate
    cases resetReducedWindowFiniteDecode Q hrQ hist <;> rfl
  simp only [he]
  exact hp
end
end ShorECDLP.Paper2607_13816
