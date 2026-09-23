import ShorECDLP.Framework.Quantum.AdaptiveComposition
namespace ShorECDLP.Quantum
noncomputable section
private theorem upd_swap (s : BasisState) (a b : Wire) (ha : a ≠ b) (x y : Bool) :
    s[a ↦ x][b ↦ y] = s[b ↦ y][a ↦ x] := by
  funext w
  by_cases hwa : w = a <;> by_cases hwb : w = b <;> simp_all [upd]
private theorem linear_commute (A B : State →ₗ[ℂ] State)
    (h : ∀ s, A (B (ket s)) = B (A (ket s))) (ψ : State) : A (B ψ) = B (A ψ) := by
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s c ψ hs hc ih =>
    have he : Finsupp.single s c = c • ket s := by simp [ket]
    simp only [map_add, he, map_smul, ih, h]
/-- A Hadamard outside a primitive's support commutes on arbitrary states. -/
theorem applyGate_H_commute (g : Gate) (w : Wire) (hw : w ∉ gateWires g) (ψ : State) :
    applyGate g (applyGate (.H w) ψ) = applyGate (.H w) (applyGate g ψ) := by
  apply linear_commute
  intro s
  cases g with
  | X t =>
    have h : w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_H_ket, map_add, map_smul, applyGate_X_ket,
      upd_other _ _ _ h, upd_other _ _ _ (Ne.symm h), upd_swap s w t h]
  | CX c t =>
    have h : w ≠ c ∧ w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_H_ket, map_add, map_smul, applyGate_CX_ket,
      upd_other _ _ _ h.2, upd_other _ _ _ (Ne.symm h.1),
      upd_other _ _ _ (Ne.symm h.2), upd_swap s w t h.2]
  | CCX a b t =>
    have h : w ≠ a ∧ w ≠ b ∧ w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_H_ket, map_add, map_smul, applyGate_CCX_ket,
      upd_other _ _ _ h.2.2, upd_other _ _ _ (Ne.symm h.1),
      upd_other _ _ _ (Ne.symm h.2.1), upd_other _ _ _ (Ne.symm h.2.2), upd_swap s w t h.2.2]
  | P dir k t =>
    have h : w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_H_ket, applyGate_P_ket, map_add, map_smul,
      upd_other _ _ _ (Ne.symm h), smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  | H t =>
    have h : w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_H_ket, map_add, map_smul,
      upd_other _ _ _ h, upd_other _ _ _ (Ne.symm h), upd_swap s w t h,
      smul_add, smul_smul]
    module
private theorem reset_H_commute (t w : Wire) (b : Bool) (h : w ≠ t) (ψ : State) :
    xResetKraus t b (applyGate (.H w) ψ) = applyGate (.H w) (xResetKraus t b ψ) := by
  apply linear_commute
  intro s
  simp only [applyGate_H_ket, map_add, map_smul, xResetKraus_ket,
    upd_other _ _ _ h, upd_other _ _ _ (Ne.symm h), upd_swap s w t h,
    smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring
private theorem circuit_H_commute (c : Circuit) (w : Wire) (hw : w ∉ circuitWires c) (ψ : State) :
    Quantum.run c (applyGate (.H w) ψ) = applyGate (.H w) (Quantum.run c ψ) := by
  induction c generalizing ψ with
  | nil => rfl
  | cons g c ih =>
    have h : w ∉ gateWires g ∧ w ∉ circuitWires c := by
      simpa only [circuitWires, List.flatMap_cons, List.mem_append, not_or] using hw
    rw [run_cons, applyGate_H_commute g w h.1, ih h.2, run_cons]
/-- Measurement outcomes are fixed branchwise, so a disjoint Hadamard commutes
with every adaptive branch, including its reset and conditional continuation. -/
theorem AdaptiveCircuit.branch_H_commute (a : AdaptiveCircuit) (w : Wire)
    (hw : w ∉ a.wires) (b : InstrumentBranch) (hb : b ∈ a.run) (ψ : State) :
    b.kraus (applyGate (.H w) ψ) = applyGate (.H w) (b.kraus ψ) := by
  induction a generalizing b ψ with
  | done =>
    simp only [AdaptiveCircuit.run, List.mem_singleton] at hb
    subst b
    rfl
  | unitary c a ih =>
    have h : w ∉ circuitWires c ∧ w ∉ a.wires := by
      simpa only [AdaptiveCircuit.wires, List.mem_append, not_or] using hw
    obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hb
    change next.kraus (Quantum.run c (applyGate (.H w) ψ)) =
      applyGate (.H w) (next.kraus (Quantum.run c ψ))
    rw [circuit_H_commute c w h.1, ih h.2 next hn]
  | xMeasureReset t a c iha ihc =>
    have h : w ≠ t ∧ w ∉ a.wires ∧ w ∉ c.wires := by
      simpa only [AdaptiveCircuit.wires, List.mem_cons, List.mem_append, not_or] using hw
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hb
      change next.kraus (xResetKraus t false (applyGate (.H w) ψ)) =
        applyGate (.H w) (next.kraus (xResetKraus t false ψ))
      rw [reset_H_commute t w false h.1, iha h.2.1 next hn]
    · obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hb
      change next.kraus (xResetKraus t true (applyGate (.H w) ψ)) =
        applyGate (.H w) (next.kraus (xResetKraus t true ψ))
      rw [reset_H_commute t w true h.1, ihc h.2.2 next hn]
/-- A whole unused register may be prepared before or after any fixed branch.
No cleanliness, normalization or product-state hypothesis is needed. -/
theorem AdaptiveCircuit.branch_hadamards_commute (a : AdaptiveCircuit) (ws : List Wire)
    (hw : ∀ w ∈ ws, w ∉ a.wires) (b : InstrumentBranch) (hb : b ∈ a.run) (ψ : State) :
    b.kraus (Quantum.run (ws.map Gate.H) ψ) = Quantum.run (ws.map Gate.H) (b.kraus ψ) := by
  induction ws generalizing ψ with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, run_cons]
    rw [ih (by intro v hv; exact hw v (by simp [hv])), a.branch_H_commute w (hw w (by simp)) b hb]

/-- Moving a disjoint register preparation across an adaptive prefix preserves
all ordered histories and branch states, even with an arbitrary adaptive suffix. -/
theorem AdaptiveCircuit.prepare_hadamards_run (a tail : AdaptiveCircuit) (ws : List Wire)
    (hw : ∀ w ∈ ws, w ∉ a.wires) (ψ : State) :
    (a.seq (.unitary (ws.map Gate.H) tail)).run.map (fun b => (b.history, b.kraus ψ)) =
    ((AdaptiveCircuit.unitary (ws.map Gate.H) a).seq tail).run.map
      (fun b => (b.history, b.kraus ψ)) := by
  rw [AdaptiveCircuit.run_seq, AdaptiveCircuit.seq, AdaptiveCircuit.run]
  rw [AdaptiveCircuit.run, AdaptiveCircuit.run_seq]
  simp only [Instrument.seq, List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro b hb
  apply List.map_congr_left
  intro c hc
  change (b.history ++ c.history, c.kraus (Quantum.run (ws.map Gate.H) (b.kraus ψ))) =
    (b.history ++ c.history, c.kraus (b.kraus (Quantum.run (ws.map Gate.H) ψ)))
  rw [a.branch_hadamards_commute ws hw b hb]
end
end ShorECDLP.Quantum
