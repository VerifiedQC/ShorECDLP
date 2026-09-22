import ShorECDLP.Framework.Quantum.MeasurementUncompute
import ShorECDLP.Framework.Quantum.InnerProduct

namespace ShorECDLP.Quantum
/-- Remove a trailing well-formed unitary from a coherent refinement without adding gates. -/
theorem cancelUnitaryRight {a : AdaptiveCircuit} {u v : Circuit}
    {P : BasisState → Prop} (hu : CircuitWellFormed u)
    (h : CoherentlyImplementsOn (a.seq (.unitary u .done)) (Quantum.run (v ++ u)) P) :
    CoherentlyImplementsOn a (Quantum.run v) P := by
  obtain ⟨cs,hc,hm⟩ := h
  have hmap : (a.seq (.unitary u .done)).run = a.run.map (fun b => b.seq {history:=[],kraus:=Quantum.run u}) := by
    simp [AdaptiveCircuit.run_seq,Instrument.seq,List.map_eq_flatMap]
  rw [hmap] at hc
  rw [List.forall₂_map_left_iff] at hc
  refine ⟨cs,hc.imp ?_,hm⟩
  intro b c hb s hs
  have heq := hb s hs
  change Quantum.run u (b.kraus (ket s)) = c • Quantum.run (v ++ u) (ket s) at heq
  have hh := congrArg (Quantum.run u.adjoint) heq
  simpa only [Quantum.run_append, map_smul, run_adjoint_run u hu] using hh
end ShorECDLP.Quantum
namespace ShorECDLP.Quantum
open Classical
/-- Replace an initial classical unitary by its coherent adaptive implementation. -/
theorem replaceInitialUnitary {a b : AdaptiveCircuit} {u : Circuit}
    {v : State →ₗ[ℂ] State} {P : BasisState → Prop}
    (hu : CircuitWellFormed u) (hp : HPFree u)
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hold : CoherentlyImplementsOn ((AdaptiveCircuit.unitary u .done).seq b) v P) :
    CoherentlyImplementsOn (a.seq b) v P := by
  let Q := fun t => ∃ s, P s ∧ t = Classical.run u s
  have htail : CoherentlyImplementsOn b (v.comp (Quantum.run u.adjoint)) Q := by
    obtain ⟨cs,hc,hm⟩ := hold
    have he : ((AdaptiveCircuit.unitary u .done).seq b).run =
        b.run.map (fun branch => ({history:=[],kraus:=Quantum.run u} : InstrumentBranch).seq branch) := by
      simp [AdaptiveCircuit.run_seq,Instrument.seq,AdaptiveCircuit.run]
      intro branch _
      rfl
    rw [he,List.forall₂_map_left_iff] at hc
    refine ⟨cs,hc.imp ?_,hm⟩
    intro branch c hb t ht
    obtain ⟨s,hs,rfl⟩ := ht
    rw [← run_ket_agrees_classical u s hp]
    change branch.kraus (Quantum.run u (ket s)) = c • v (Quantum.run u.adjoint (Quantum.run u (ket s)))
    rw [run_adjoint_run u hu]
    exact hb s hs
  have hall := ha.seq htail (by
    intro s hs
    rw [run_ket_agrees_classical u s hp]
    exact supportedOn_ket Q _ ⟨s,hs,rfl⟩)
  apply hall.congrIdeal
  intro s _
  change v (Quantum.run u.adjoint (Quantum.run u (ket s))) = v (ket s)
  rw [run_adjoint_run u hu]
end ShorECDLP.Quantum
