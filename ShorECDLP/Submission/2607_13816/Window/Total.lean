import ShorECDLP.Submission.«2607_13816».Window.Secp
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem history_length (ws : List Wire) (b : InstrumentBranch)
    (hb : b∈(semiclassicalFourier .inverse ws List.nil).run) : b.history.length=ws.length := by
  rw [semiclassicalFourier_run] at hb
  obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp hb
  exact (fourierOutcomes_mem _ _).mp hbs
private theorem scalar_decode_total (b : InstrumentBranch) (hb : b∈scalarFourierProgram.run) :
    ∃ out : Fin (2^257) × Fin (2^257), decodeScalarFourier b.history=
      (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  rw [scalarFourierProgram,AdaptiveCircuit.run_seq] at hb
  obtain ⟨l,hl,hrest⟩ := List.mem_flatMap.mp hb
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hrest
  have hll : l.history.length=257 := by simpa only [scalarFourierLeft,List.length_reverse,List.length_range'] using history_length _ l hl
  have hrl : r.history.length=257 := by simpa only [scalarFourierRight,List.length_reverse,List.length_range'] using history_length _ r hr
  obtain ⟨va,ha⟩ := paperOutcomeBits_of_word 257 l.history hll
  obtain ⟨vb,hb⟩ := paperOutcomeBits_of_word 257 r.history hrl
  refine ⟨⟨va,vb⟩,?_⟩
  simpa only [decodeScalarFourier,InstrumentBranch.seq,←hll,List.take_left,List.drop_left] using (Prod.ext ha hb).symm
private theorem window_decode_total (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(windowTrialProgram P Q hP hQ hrP hrQ).run) :
    ∃ out : Fin (2^257) × Fin (2^257), decodeWindowTrial P Q hP hQ hrP hrQ b.history=
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  rw [windowTrialProgram,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,hbefore,hrest⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,hafter,rfl⟩ := List.mem_map.mp hrest
  obtain ⟨out,ho⟩ := scalar_decode_total after hafter
  refine ⟨out,?_⟩
  simp only [decodeWindowTrial,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hbefore,
    Option.map_some,ho]
theorem secpWindowDecode_total (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(secpWindowProgram Q hrQ).run) :
    ∃ out : Fin (2^257) × Fin (2^257), secpWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  by_cases hQ : Q=0
  · simp only [secpWindowProgram,dif_pos hQ,AdaptiveCircuit.run,List.mem_singleton] at hb
    subst b
    exact ⟨(0,0),by simp only [secpWindowDecode,dif_pos hQ,ite_true]⟩
  · simp only [secpWindowProgram,dif_neg hQ] at hb
    simpa only [secpWindowDecode,dif_neg hQ] using window_decode_total _ _ _ _ _ _ b hb
private theorem partition_mass {α β : Type} [Fintype α] [BEq β] [LawfulBEq β]
    (I : Instrument) (ψ : State) (decode : InstrumentBranch → β) (encode : α → β)
    (hinj : Function.Injective encode) (ht : ∀ b∈I, ∃ a, decode b=encode a) :
    (∑ a : α, Instrument.bornMass (I.filter (fun b => decode b==encode a)) ψ)=
      Instrument.bornMass I ψ := by
  classical
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons b I ih =>
    obtain ⟨a,ha⟩ := ht b (by simp)
    have htail : ∀ b∈I, ∃ a, decode b=encode a := fun b hb => ht b (by simp [hb])
    have hfilter (x : α) :
        Instrument.bornMass ((b::I).filter (fun b => decode b==encode x)) ψ=
        (if x=a then normSq (b.kraus ψ) else 0)+
          Instrument.bornMass (I.filter (fun b => decode b==encode x)) ψ := by
      by_cases he : x=a
      · subst x; simp [Instrument.bornMass,ha]
      · have hn : decode b≠encode x := by intro h; exact he (hinj (h.symm.trans ha))
        simp [Instrument.bornMass,hn,he]
    simp only [hfilter,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,ih htail]
    rfl
private theorem pair_encode_injective (n : Nat) :
    Function.Injective (fun out : Fin (2^n) × Fin (2^n) =>
      some (paperOutcomeBits n out.1,paperOutcomeBits n out.2)) := by
  intro a b h
  have h' := Option.some.inj h
  exact Prod.ext (paperOutcomeBits_injective n (congrArg Prod.fst h'))
    (paperOutcomeBits_injective n (congrArg Prod.snd h'))

theorem secpWindowProgram_total (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass (secpWindowProgram Q hrQ).run (ket zeroBasisState)=1 := by
  have hp := partition_mass (secpWindowProgram Q hrQ).run (ket zeroBasisState)
    (fun b => secpWindowDecode Q hrQ b.history)
    (fun out : Fin (2^257) × Fin (2^257) => some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))
    (pair_encode_injective 257) (secpWindowDecode_total Q hrQ)
  simp only [secpWindowOutputMass_physical] at hp
  exact hp.symm.trans (secpWindowOutputMass_total Q hrQ d hQd)

end
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem candidate_correct (Q : Point) (d : Nat) (hQd : Q=d • G) (c : ZMod order) :
    c.val • G=Q ↔ c=(d:ZMod order) := by
  rw [hQd,nsmul_eq_nsmul_iff_modEq,generator_order,←ZMod.natCast_eq_natCast_iff]
  letI : NeZero order := ⟨order_prime.ne_zero⟩
  simp only [ZMod.natCast_zmod_val]
/-- Accept a classical candidate only after checking the public group relation. -/
def secpWindowVerifiedCandidate (Q : Point) (out : Fin (2^257) × Fin (2^257)) : Option (ZMod order) := by
  classical
  exact (secpWindowPostprocess Q out).filter (fun c => decide (c.val • G=Q))
theorem secpWindowVerifiedCandidate_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (out : Fin (2^257) × Fin (2^257)) (c : ZMod order)
    (hc : secpWindowVerifiedCandidate Q out=some c) : c=(d:ZMod order) := by
  classical
  have h := Option.filter_eq_some_iff.mp hc
  exact (candidate_correct Q d hQd c).mp (of_decide_eq_true h.2)
theorem secpWindowVerifiedCandidate_complete (Q : Point) (d : Nat) (hQd : Q=d • G)
    (out : Fin (2^257) × Fin (2^257)) :
    secpWindowVerifiedCandidate Q out=some (d:ZMod order) ↔
      secpWindowPostprocess Q out=some (d:ZMod order) := by
  classical
  rw [secpWindowVerifiedCandidate,Option.filter_eq_some_iff]
  simp only [candidate_correct Q d hQd,decide_true,and_true]
end
end ShorECDLP.Paper2607_13816
