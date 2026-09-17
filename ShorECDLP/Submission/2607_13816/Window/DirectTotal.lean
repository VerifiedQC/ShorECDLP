import ShorECDLP.Submission.«2607_13816».Window.DirectSecp
import ShorECDLP.Submission.«2607_13816».Window.Total
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem window_decode_total (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(directWindowTrialProgram P Q hP hQ hrP hrQ).run) :
    ∃ out : Fin (2^257) × Fin (2^257), decodeDirectWindowTrial P Q hP hQ hrP hrQ b.history=
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  rw [directWindowTrialProgram,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,hbefore,hrest⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,hafter,rfl⟩ := List.mem_map.mp hrest
  obtain ⟨out,ho⟩ := scalarFourierDecode_total after hafter
  refine ⟨out,?_⟩
  simp only [decodeDirectWindowTrial,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hbefore,
    Option.map_some,ho]
theorem directSecpWindowDecode_total (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(directSecpWindowProgram Q hrQ).run) :
    ∃ out : Fin (2^257) × Fin (2^257), directSecpWindowDecode Q hrQ b.history=
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2) := by
  by_cases hQ : Q=0
  · simp only [directSecpWindowProgram,dif_pos hQ,AdaptiveCircuit.run,List.mem_singleton] at hb
    subst b
    exact ⟨(0,0),by simp only [directSecpWindowDecode,secpWindowDecode,dif_pos hQ,ite_true]⟩
  · simp only [directSecpWindowProgram,dif_neg hQ] at hb
    simpa only [directSecpWindowDecode,dif_neg hQ] using window_decode_total _ _ _ _ _ _ b hb
theorem directSecpWindowProgram_total (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass (directSecpWindowProgram Q hrQ).run (ket zeroBasisState)=1 := by
  have hp := instrumentPartitionMass (directSecpWindowProgram Q hrQ).run (ket zeroBasisState)
    (fun b => directSecpWindowDecode Q hrQ b.history)
    (fun out : Fin (2^257) × Fin (2^257) => some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))
    (paperOutcomePair_injective 257) (directSecpWindowDecode_total Q hrQ)
  simp only [directSecpWindowOutputMass_physical] at hp
  exact hp.symm.trans (secpWindowOutputMass_total Q hrQ d hQd)

end
end ShorECDLP.Paper2607_13816
