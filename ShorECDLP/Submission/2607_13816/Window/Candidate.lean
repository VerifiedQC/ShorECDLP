import ShorECDLP.Submission.«2607_13816».Window.ResetOutcomes
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Turn a bounded binary word into the finite classical output type. -/
def windowWordOutcome (bs : List Bool) : Option (Fin (2^257)) :=
  if h : fourierWordLSB bs<2^257 then some ⟨fourierWordLSB bs,h⟩ else none
private theorem word_outcome (v : Fin (2^257)) :
    windowWordOutcome (paperOutcomeBits 257 v)=some v := by
  simp only [windowWordOutcome,paperOutcomeBits_word,dif_pos v.isLt]
/-- Read the two output words of the actual reset trial. -/
def resetWindowFiniteDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (Fin (2^257) × Fin (2^257)) := do
  let bits ← resetWindowDecode Q hrQ hist
  let a ← windowWordOutcome bits.1
  let b ← windowWordOutcome bits.2
  some (a,b)
private theorem finite_decode_of_bits (Q : Point) (hrQ : order • Q=0) (hist : List Bool)
    (out : Fin (2^257) × Fin (2^257))
    (h : resetWindowDecode Q hrQ hist=some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2)) :
    resetWindowFiniteDecode Q hrQ hist=some out := by
  simp only [resetWindowFiniteDecode,h,Bind.bind,Option.bind,word_outcome]
private theorem reset_decode_total (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetWindowTrial Q hrQ).run) :
    ∃ out : Fin (2^257) × Fin (2^257), resetWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  rw [resetWindowTrial,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,hbefore,hrest⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,hafter,rfl⟩ := List.mem_map.mp hrest
  obtain ⟨out,ho⟩ := secpWindowDecode_total Q hrQ before hbefore
  refine ⟨out,?_⟩
  simp only [resetWindowDecode,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hbefore,
    Option.bind,Bind.bind,List.length_append,Nat.add_sub_cancel_right,List.take_left,ho]
private theorem finite_decode_iff (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetWindowTrial Q hrQ).run) (out : Fin (2^257) × Fin (2^257)) :
    resetWindowFiniteDecode Q hrQ b.history=some out ↔ resetWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  constructor
  · intro h
    obtain ⟨v,hv⟩ := reset_decode_total Q hrQ b hb
    have he := Option.some.inj ((finite_decode_of_bits Q hrQ b.history v hv).symm.trans h)
    exact he ▸ hv
  · exact finite_decode_of_bits Q hrQ b.history out

theorem resetWindowFiniteOutputMass (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^257) × Fin (2^257)) :
    Instrument.bornMass ((resetWindowTrial Q hrQ).run.filter
      (fun b => resetWindowFiniteDecode Q hrQ b.history==some out)) (ket zeroBasisState)=
      secpWindowOutputMass Q hrQ out := by
  have he : (resetWindowTrial Q hrQ).run.filter
      (fun b => resetWindowFiniteDecode Q hrQ b.history==some out)=
      (resetWindowTrial Q hrQ).run.filter (fun b => resetWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2)) := by
    apply List.filter_congr
    intro b hb
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact finite_decode_iff Q hrQ b hb out
  rw [he]
  exact resetWindowOutputMass_physical Q hrQ out
/-- The classical decoder specification checks the candidate against the public point. -/
def resetWindowCandidate (Q : Point) (hrQ : order • Q=0) (hist : List Bool) : Option (ZMod order) :=
  (resetWindowFiniteDecode Q hrQ hist).bind (secpWindowVerifiedCandidate Q)

theorem resetWindowCandidate_sound (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) (c : ZMod order) (hc : resetWindowCandidate Q hrQ hist=some c) : c=(d:ZMod order) := by
  obtain ⟨out,_,ho⟩ := Option.bind_eq_some_iff.mp hc
  exact secpWindowVerifiedCandidate_sound Q d hQd out c ho

private theorem selected_decode_mass {α : Type} [Fintype α] [BEq α] [LawfulBEq α]
    (I : Instrument) (decode : InstrumentBranch → Option α) (accept : α → Bool) (ψ : State) :
    Instrument.bornMass (I.filter (fun b => (decode b).any accept)) ψ=
      ∑ a : α, if accept a then Instrument.bornMass (I.filter (fun b => decode b==some a)) ψ else 0 := by
  classical
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons b I ih =>
    cases hd : decode b with
    | none => simpa [Instrument.bornMass,hd] using ih
    | some a =>
      have hterm (x : α) :
          (if accept x then Instrument.bornMass ((b::I).filter (fun b => decode b==some x)) ψ else 0)=
          (if x=a then (if accept a then normSq (b.kraus ψ) else 0) else 0)+
          (if accept x then Instrument.bornMass (I.filter (fun b => decode b==some x)) ψ else 0) := by
        by_cases he : x=a
        · subst x; cases accept a <;> simp [Instrument.bornMass,hd]
        · have hn : a≠x := Ne.symm he
          cases accept x <;> simp [Instrument.bornMass,hd,he,hn]
      simp only [hterm,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,←ih]
      cases ha : accept a <;> simp [Instrument.bornMass,hd,ha]

theorem resetWindowCandidate_mass (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass ((resetWindowTrial Q hrQ).run.filter
      (fun b => (resetWindowCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)=
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
  have hp := selected_decode_mass (resetWindowTrial Q hrQ).run
    (fun b => resetWindowFiniteDecode Q hrQ b.history)
    (fun out => (secpWindowVerifiedCandidate Q out).isSome) (ket zeroBasisState)
  simp only [resetWindowFiniteOutputMass,ha] at hp
  have he (hist : List Bool) : (resetWindowCandidate Q hrQ hist).isSome=
      (resetWindowFiniteDecode Q hrQ hist).any (fun out => (secpWindowVerifiedCandidate Q out).isSome) := by
    unfold resetWindowCandidate
    cases resetWindowFiniteDecode Q hrQ hist <;> rfl
  simp only [he]
  exact hp
end
end ShorECDLP.Paper2607_13816
