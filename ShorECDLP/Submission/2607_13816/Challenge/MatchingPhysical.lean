import ShorECDLP.Submission.«2607_13816».Challenge.FixedNetwork
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum

theorem equalityCells_wellFormed {n : Nat} (a t : Fin n → Wire)
    (flag : Wire) (scratch : List Wire)
    (ha : ∀ i, a i ≠ t i) (hl : EqConstLayout (List.ofFn t) flag scratch) :
    CircuitWellFormed (registerEqualCircuit (equalityCells a t) flag scratch) := by
  have hx : CircuitWellFormed (xorWordCircuit (equalityCells a t)) := by
    intro g hg
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact ha i
  have he : CircuitWellFormed (computeEqConst ((equalityCells a t).map Prod.snd) 0 flag scratch) := by
    apply computeEqConst_wellFormed
    simpa only [equalityCells, List.map_ofFn] using hl
  rw [registerEqualCircuit, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨hx,he⟩,hx⟩

theorem endpointTransposition_wellFormed {n : Nat}
    (a b t : Fin n → Wire) (flag : Wire) (scratch : List Wire)
    (g : EndpointGeometry a b t flag scratch) :
    CircuitWellFormed (endpointTranspositionCircuit a b t flag scratch) := by
  have ht : CircuitWellFormed (endpointTests a b t flag scratch) := by
    rw [endpointTests, circuitWellFormed_append]
    exact ⟨equalityCells_wellFormed a t flag scratch (fun i => (g.inputsApart i i).1) g.equalityLayout,
      equalityCells_wellFormed b t flag scratch (fun i => (g.inputsApart i i).2) g.equalityLayout⟩
  have hu : CircuitWellFormed (endpointWordCircuit flag (endpointUpdateCells a b t)) := by
    intro gate hg
    obtain ⟨p,hp,hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    simp only [endpointBitCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨(g.flagApart i).1,(g.flagApart i).2.2,(g.inputsApart i i).1⟩
    · exact ⟨(g.flagApart i).2.1,(g.flagApart i).2.2,(g.inputsApart i i).2⟩
  rw [endpointTranspositionCircuit, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨ht,hu⟩,ht⟩

theorem matchingCircuit_wellFormed {n : Nat}
    (rows : MatchingSlot → Fin n → Wire) (flag : Wire) (scratch : List Wire)
    (geometries : ∀ m ∈ matchingNetwork,
      EndpointGeometry (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch) :
    CircuitWellFormed (matchingCircuit rows flag scratch) := by
  intro gate hg
  obtain ⟨m,hm,hg⟩ := List.mem_flatMap.mp hg
  exact endpointTransposition_wellFormed _ _ _ _ _ (geometries m hm) gate hg
end ShorECDLP.Paper2607_13816.ChallengeMigration
