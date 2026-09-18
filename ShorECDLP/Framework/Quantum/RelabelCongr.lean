import ShorECDLP.Framework.Quantum.Relabel
namespace ShorECDLP
noncomputable section
theorem Gate.relabel_trans (g : Gate) (e f : Wire ≃ Wire) :
    (g.relabel e).relabel f=g.relabel (e.trans f) := by cases g <;> rfl
theorem Gate.relabel_congr (g : Gate) (e f : Wire ≃ Wire)
    (h : ∀ w∈gateWires g,e w=f w) : g.relabel e=g.relabel f := by
  cases g <;> simp_all [gateWires,Gate.relabel]
namespace Quantum
theorem AdaptiveCircuit.relabel_trans (p : AdaptiveCircuit) (e f : Wire ≃ Wire) :
    (p.relabel e).relabel f=p.relabel (e.trans f) := by
  induction p with
  | done => rfl
  | unitary c p ih => simp [AdaptiveCircuit.relabel,List.map_map,Gate.relabel_trans,ih]
  | xMeasureReset w a b ia ib => simp [AdaptiveCircuit.relabel,ia,ib]
theorem AdaptiveCircuit.relabel_congr (p : AdaptiveCircuit) (e f : Wire ≃ Wire)
    (h : ∀ w∈p.wires,e w=f w) : p.relabel e=p.relabel f := by
  induction p with
  | done => rfl
  | unitary c p ih =>
    simp only [AdaptiveCircuit.relabel]
    congr 1
    · apply List.map_congr_left
      intro g hg
      apply Gate.relabel_congr
      intro w hw
      exact h w (List.mem_append_left _ (List.mem_flatMap.mpr ⟨g,hg,hw⟩))
    · exact ih (by intro w hw; exact h w (List.mem_append_right _ hw))
  | xMeasureReset w a b ia ib =>
    simp only [AdaptiveCircuit.relabel]
    rw [h w (by simp [AdaptiveCircuit.wires]),ia,ib]
    · intro v hv; exact h v (by simp [AdaptiveCircuit.wires,hv])
    · intro v hv; exact h v (by simp [AdaptiveCircuit.wires,hv])
end Quantum
end
end ShorECDLP
