import ShorECDLP.Framework.Quantum.MeasurementUncompute
namespace ShorECDLP.Quantum
noncomputable section
private theorem support_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ+φ) := by
  intro s hs
  by_cases h : ψ s=0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h
private theorem support_smul {V : BasisState → Prop} {ψ : State} (c : ℂ)
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])
private theorem support_linear (V : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn V (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn V (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz,hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u=s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,he,map_smul]
    exact support_add (support_smul c (hL s hvs)) (ih hvψ)
private theorem gate_frame (g : Gate) (w : Wire) (v : Bool) (hw : w∉gateWires g)
    (ψ : State) (hψ : SupportedOn (fun s => s w=v) ψ) :
    SupportedOn (fun s => s w=v) (applyGate g ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  have hup (t : Wire) (h : w≠t) (b : Bool) :
      SupportedOn (fun s => s w=v) (ket (s[t ↦ b])) :=
    supportedOn_ket _ _ (by simpa [upd,h] using hs)
  rw [applyGate_ket]
  cases g with
  | X t => exact hup t (by simpa [gateWires] using hw) _
  | H t =>
    have h : w≠t := by simpa [gateWires] using hw
    exact support_add (support_smul _ (hup t h _)) (support_smul _ (hup t h _))
  | CX c t => exact hup t (by simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false,not_or] at hw; exact hw.2) _
  | CCX a b t => exact hup t (by simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false,not_or] at hw; exact hw.2.2) _
  | P dir k t => exact support_smul _ (supportedOn_ket _ _ hs)
private theorem circuit_frame (g : Circuit) (w : Wire) (v : Bool) (hw : w∉circuitWires g)
    (ψ : State) (hψ : SupportedOn (fun s => s w=v) ψ) :
    SupportedOn (fun s => s w=v) (Quantum.run g ψ) := by
  induction g generalizing ψ with
  | nil => exact hψ
  | cons a g ih =>
    have h : w∉gateWires a ∧ w∉circuitWires g := by
      simpa only [circuitWires,List.flatMap_cons,List.mem_append,not_or] using hw
    exact ih h.2 _ (gate_frame a w v h.1 ψ hψ)
private theorem reset_frame (t w : Wire) (v out : Bool) (hw : w≠t)
    (ψ : State) (hψ : SupportedOn (fun s => s w=v) ψ) :
    SupportedOn (fun s => s w=v) (xResetKraus t out ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  rw [xResetKraus_ket]
  exact support_smul _ (supportedOn_ket _ _ (by simpa [upd,hw] using hs))
/-- Every adaptive branch preserves a basis bit outside the program support. -/
theorem AdaptiveCircuit.branch_frame (a : AdaptiveCircuit) (w : Wire) (v : Bool)
    (hw : w∉a.wires) (b : InstrumentBranch) (hb : b∈a.run)
    (ψ : State) (hψ : SupportedOn (fun s => s w=v) ψ) :
    SupportedOn (fun s => s w=v) (b.kraus ψ) := by
  induction a generalizing b ψ with
  | done =>
    simp only [AdaptiveCircuit.run,List.mem_singleton] at hb
    subst b
    exact hψ
  | unitary g a ih =>
    have h : w∉circuitWires g ∧ w∉a.wires := by
      simpa only [AdaptiveCircuit.wires,List.mem_append,not_or] using hw
    obtain ⟨next,hn,he⟩ := List.mem_map.mp hb
    subst b
    exact ih h.2 next hn _ (circuit_frame g w v h.1 ψ hψ)
  | xMeasureReset t a c iha ihc =>
    have h : w≠t ∧ w∉a.wires ∧ w∉c.wires := by
      simpa only [AdaptiveCircuit.wires,List.mem_cons,List.mem_append,not_or] using hw
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨next,hn,he⟩ := List.mem_map.mp hb
      subst b
      exact iha h.2.1 next hn _ (reset_frame t w v false h.1 ψ hψ)
    · obtain ⟨next,hn,he⟩ := List.mem_map.mp hb
      subst b
      exact ihc h.2.2 next hn _ (reset_frame t w v true h.1 ψ hψ)

end
end ShorECDLP.Quantum
