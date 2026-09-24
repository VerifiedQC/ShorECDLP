import ShorECDLP.Framework.Quantum.AdaptiveHadamard
namespace ShorECDLP.Quantum
noncomputable section
private theorem linear_commute (A B : State →ₗ[ℂ] State)
    (h : ∀ s, A (B (ket s)) = B (A (ket s))) (ψ : State) : A (B ψ) = B (A ψ) := by
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s c ψ hs hc ih =>
    have he : Finsupp.single s c = c • ket s := by simp [ket]
    simp only [map_add, he, map_smul, ih, h]
private theorem upd_swap (s : BasisState) (a b : Wire) (ha : a ≠ b) (x y : Bool) :
    s[a ↦ x][b ↦ y] = s[b ↦ y][a ↦ x] := by
  funext w
  by_cases hwa : w = a <;> by_cases hwb : w = b <;> simp_all [upd]

theorem applyGate_P_commute (g : Gate) (w : Wire) (dir : PhaseDir) (k : Nat)
    (hw : w ∉ gateWires g) (ψ : State) :
    applyGate g (applyGate (.P dir k w) ψ) = applyGate (.P dir k w) (applyGate g ψ) := by
  apply linear_commute
  intro s
  cases g with
  | X t =>
    have h : w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_P_ket, map_smul, applyGate_X_ket, upd_other _ _ _ h]
  | CX c t =>
    have h : w ≠ c ∧ w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_P_ket, map_smul, applyGate_CX_ket, upd_other _ _ _ h.2]
  | CCX a b t =>
    have h : w ≠ a ∧ w ≠ b ∧ w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_P_ket, map_smul, applyGate_CCX_ket, upd_other _ _ _ h.2.2]
  | P d l t =>
    simp only [applyGate_P_ket, map_smul, smul_smul]
    congr 1
    ring
  | H t =>
    have h : t ≠ w := by simpa [gateWires, ne_comm] using hw
    exact (applyGate_H_commute (.P dir k w) t (by simpa [gateWires] using h) (ket s)).symm

theorem xReset_P_commute (t w : Wire) (b : Bool) (dir : PhaseDir) (k : Nat)
    (h : w ≠ t) (ψ : State) :
    xResetKraus t b (applyGate (.P dir k w) ψ) = applyGate (.P dir k w) (xResetKraus t b ψ) := by
  apply linear_commute
  intro s
  simp only [applyGate_P_ket, xResetKraus_ket, map_smul, upd_other _ _ _ h, smul_smul]
  congr 1
  ring

theorem applyGate_reset_commute (g : Gate) (w : Wire) (b : Bool)
    (hw : w ∉ gateWires g) (ψ : State) :
    applyGate g (xResetKraus w b ψ) = xResetKraus w b (applyGate g ψ) := by
  apply linear_commute
  intro s
  cases g with
  | X t =>
    have h : w ≠ t := by simpa [gateWires] using hw
    simp only [xResetKraus_ket, map_smul, applyGate_X_ket,
      upd_other _ _ _ h, upd_other _ _ _ (Ne.symm h), upd_swap s w t h]
  | CX c t =>
    have h : w ≠ c ∧ w ≠ t := by simpa [gateWires] using hw
    simp only [xResetKraus_ket, map_smul, applyGate_CX_ket, upd_other _ _ _ h.2,
      upd_other _ _ _ (Ne.symm h.1), upd_other _ _ _ (Ne.symm h.2), upd_swap s w t h.2]
  | CCX a c t =>
    have h : w ≠ a ∧ w ≠ c ∧ w ≠ t := by simpa [gateWires] using hw
    simp only [xResetKraus_ket, map_smul, applyGate_CCX_ket, upd_other _ _ _ h.2.2,
      upd_other _ _ _ (Ne.symm h.1), upd_other _ _ _ (Ne.symm h.2.1),
      upd_other _ _ _ (Ne.symm h.2.2), upd_swap s w t h.2.2]
  | P dir k t =>
    have h : t ≠ w := by simpa [gateWires, ne_comm] using hw
    exact (xReset_P_commute w t b dir k h (ket s)).symm
  | H t =>
    have h : w ≠ t := by simpa [gateWires] using hw
    simp only [applyGate_H_ket, xResetKraus_ket, map_add, map_smul,
      upd_other _ _ _ h, upd_other _ _ _ (Ne.symm h), upd_swap s w t h,
      smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring

theorem xReset_reset_commute (t w : Wire) (a b : Bool) (h : w ≠ t) (ψ : State) :
    xResetKraus t a (xResetKraus w b ψ) = xResetKraus w b (xResetKraus t a ψ) := by
  apply linear_commute
  intro s
  simp only [xResetKraus_ket, map_smul, upd_other _ _ _ h,
    upd_other _ _ _ (Ne.symm h), upd_swap s w t h, smul_smul]
  congr 1
  ring

private theorem circuit_commute (c : Circuit) (L : State →ₗ[ℂ] State)
    (hg : ∀ g ∈ c, ∀ ψ, applyGate g (L ψ) = L (applyGate g ψ)) (ψ : State) :
    Quantum.run c (L ψ) = L (Quantum.run c ψ) := by
  induction c generalizing ψ with
  | nil => rfl
  | cons g c ih =>
    rw [run_cons, hg g (by simp), ih (by intro t ht; exact hg t (by simp [ht])), run_cons]

/-- A fixed linear operation commuting with every primitive in a program commutes
with each actual branch, without discarding its measurement history. -/
theorem AdaptiveCircuit.branch_commute (a : AdaptiveCircuit) (L : State →ₗ[ℂ] State)
    (hg : ∀ g, (∀ w ∈ gateWires g, w ∈ a.wires) → ∀ ψ, applyGate g (L ψ) = L (applyGate g ψ))
    (hr : ∀ w ∈ a.wires, ∀ v ψ, xResetKraus w v (L ψ) = L (xResetKraus w v ψ))
    (b : InstrumentBranch) (hb : b ∈ a.run) (ψ : State) : b.kraus (L ψ) = L (b.kraus ψ) := by
  induction a generalizing b ψ with
  | done =>
    simp only [AdaptiveCircuit.run, List.mem_singleton] at hb
    subst b
    rfl
  | unitary c a ih =>
    obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hb
    have hc : ∀ ψ, Quantum.run c (L ψ) = L (Quantum.run c ψ) := by
      apply circuit_commute
      intro g hmem
      apply hg g
      intro w hw
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨g, hmem, hw⟩
    change next.kraus (Quantum.run c (L ψ)) = L (next.kraus (Quantum.run c ψ))
    rw [hc]
    exact ih (by intro g h; exact hg g (by intro w hw; exact List.mem_append_right _ (h w hw)))
      (by intro w hw; exact hr w (List.mem_append_right _ hw)) next hn _
  | xMeasureReset t a c iha ihc =>
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hb
      change next.kraus (xResetKraus t false (L ψ)) = L (next.kraus (xResetKraus t false ψ))
      rw [hr t (by simp [AdaptiveCircuit.wires])]
      exact iha (by intro g h; exact hg g (by intro w hw; simp [AdaptiveCircuit.wires, h w hw]))
        (by intro w hw; exact hr w (by simp [AdaptiveCircuit.wires, hw])) next hn _
    · obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hb
      change next.kraus (xResetKraus t true (L ψ)) = L (next.kraus (xResetKraus t true ψ))
      rw [hr t (by simp [AdaptiveCircuit.wires])]
      exact ihc (by intro g h; exact hg g (by intro w hw; simp [AdaptiveCircuit.wires, h w hw]))
        (by intro w hw; exact hr w (by simp [AdaptiveCircuit.wires, hw])) next hn _

theorem AdaptiveCircuit.branch_P_commute (a : AdaptiveCircuit) (w : Wire) (dir : PhaseDir) (k : Nat)
    (hw : w ∉ a.wires) (b : InstrumentBranch) (hb : b ∈ a.run) (ψ : State) :
    b.kraus (applyGate (.P dir k w) ψ) = applyGate (.P dir k w) (b.kraus ψ) := by
  apply a.branch_commute
  · intro g hg φ
    exact applyGate_P_commute g w dir k (fun h => hw (hg w h)) φ
  · intro t ht v φ
    exact xReset_P_commute t w v dir k (by intro h; subst t; exact hw ht) φ
  · exact hb

theorem AdaptiveCircuit.branch_reset_commute (a : AdaptiveCircuit) (w : Wire) (v : Bool)
    (hw : w ∉ a.wires) (b : InstrumentBranch) (hb : b ∈ a.run) (ψ : State) :
    b.kraus (xResetKraus w v ψ) = xResetKraus w v (b.kraus ψ) := by
  apply a.branch_commute
  · intro g hg φ
    exact applyGate_reset_commute g w v (fun h => hw (hg w h)) φ
  · intro t ht z φ
    exact xReset_reset_commute t w z v (by intro h; subst t; exact hw ht) φ
  · exact hb
end
end ShorECDLP.Quantum
