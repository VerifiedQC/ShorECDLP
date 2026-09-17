import ShorECDLP.Submission.«2607_13816».Window.ReducedSecp
import ShorECDLP.Submission.«2607_13816».Window.Total
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
theorem reducedFourierDecode_total (b : InstrumentBranch) (hb : b∈reducedFourierProgram.run) :
    ∃ out : Fin (2^256) × Fin (2^208), decodeReducedFourier b.history=
      (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) := by
  rw [reducedFourierProgram,AdaptiveCircuit.run_seq] at hb
  obtain ⟨l,hl,hrest⟩ := List.mem_flatMap.mp hb
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hrest
  have hll : l.history.length=256 := by simpa only [reducedFourierLeft,List.length_reverse,List.length_range'] using semiclassicalFourier_history_length .inverse _ l hl
  have hrl : r.history.length=208 := by simpa only [reducedFourierRight,List.length_reverse,List.length_range'] using semiclassicalFourier_history_length .inverse _ r hr
  obtain ⟨va,ha⟩ := paperOutcomeBits_of_word 256 l.history hll
  obtain ⟨vb,hb⟩ := paperOutcomeBits_of_word 208 r.history hrl
  refine ⟨⟨va,vb⟩,?_⟩
  simpa only [decodeReducedFourier,InstrumentBranch.seq,←hll,List.take_left,List.drop_left] using (Prod.ext ha hb).symm
private theorem window_decode_total (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(reducedWindowTrialProgram P Q hP hQ hrP hrQ).run) :
    ∃ out : Fin (2^256) × Fin (2^208), decodeReducedWindowTrial P Q hP hQ hrP hrQ b.history=
      some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) := by
  rw [reducedWindowTrialProgram,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,hbefore,hrest⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,hafter,rfl⟩ := List.mem_map.mp hrest
  obtain ⟨out,ho⟩ := reducedFourierDecode_total after hafter
  refine ⟨out,?_⟩
  simp only [decodeReducedWindowTrial,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hbefore,
    Option.map_some,ho]
theorem reducedSecpWindowDecode_total (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(reducedSecpWindowProgram Q hrQ).run) :
    ∃ out : Fin (2^256) × Fin (2^208), reducedSecpWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) := by
  by_cases hQ : Q=0
  · simp only [reducedSecpWindowProgram,dif_pos hQ,AdaptiveCircuit.run,List.mem_singleton] at hb
    subst b
    exact ⟨(0,0),by simp only [reducedSecpWindowDecode,dif_pos hQ,ite_true]⟩
  · simp only [reducedSecpWindowProgram,dif_neg hQ] at hb
    simpa only [reducedSecpWindowDecode,dif_neg hQ] using window_decode_total _ _ _ _ _ _ b hb
theorem reducedSecpWindowProgram_total (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass (reducedSecpWindowProgram Q hrQ).run (ket zeroBasisState)=1 := by
  have hp := instrumentPartitionMass (reducedSecpWindowProgram Q hrQ).run (ket zeroBasisState)
    (fun b => reducedSecpWindowDecode Q hrQ b.history)
    (fun out : Fin (2^256) × Fin (2^208) => some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2))
    (unequalOutcomePair_injective 256 208) (reducedSecpWindowDecode_total Q hrQ)
  simp only [reducedSecpWindowOutputMass_physical] at hp
  exact hp.symm.trans (reducedSecpWindowOutputMass_total Q hrQ d hQd)

end
end ShorECDLP.Paper2607_13816
