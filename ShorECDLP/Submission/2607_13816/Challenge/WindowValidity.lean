import ShorECDLP.Submission.«2607_13816».Challenge.ActualWindow
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1

theorem batchedWindowValid_address_update (s : BasisState) (hs : BatchedWindowValid s)
    (w : Wire) (hw : w ∈ streamAddress) (b : Bool) : BatchedWindowValid (s[w ↦ b]) := by
  have hw' : 855 ≤ w ∧ w < 871 := by simpa [streamAddress,List.mem_range'_1] using hw
  have hcore (v : Wire) (hv : v < 839) : (s[w ↦ b]) v = s v := by
    simp only [upd]
    rw [if_neg (by dsimp only [Wire] at *; omega)]
  have hx : wireValues (List.range' 263 256) (s[w ↦ b]) = wireValues (List.range' 263 256) s := by
    apply List.map_congr_left
    intro v hv
    exact hcore v (by simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  have hy : wireValues (List.range' 580 256) (s[w ↦ b]) = wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro v hv
    exact hcore v (by simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  obtain ⟨⟨⟨hclean,hzero,hxbound,hybound⟩,hq⟩,hworkspace⟩ := hs.1
  refine ⟨⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro v hv
    rw [hcore v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)]
    exact hclean v hv
  · rw [hcore 837 (by decide)]; exact hzero
  · rw [hx]; exact hxbound
  · rw [hy]; exact hybound
  · rw [hcore 836 (by decide)]; exact hq
  · intro v hv
    have hv' : 1024 ≤ v := by simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
    have hne : v ≠ w := by dsimp only [Wire] at *; omega
    simpa only [upd,if_neg hne] using hworkspace v hv
  · obtain ⟨P,hP⟩ := hs.2
    refine ⟨P,?_⟩
    simpa only [pointStateCoordinates,hcore 838 (by decide),hx,hy] using hP


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

theorem batchedWindowValid_fourierClear (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (s : BasisState)
    (hs : BatchedWindowValid s) : BatchedWindowValid (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => exact hs
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (batchedWindowValid_address_update s hs w (hws w (by simp)) false)

theorem batchedWindowValid_fourierBranch (dir : PhaseDir) (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (prior bs : List Bool)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (fourierBranch dir ws prior bs ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  rw [fourierBranch_ket]
  exact support_smul _ (supportedOn_ket _ _
    (batchedWindowValid_fourierClear ws hws s hs))

theorem batchedWindowValid_H (w : Wire) (hw : w ∈ streamAddress)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (applyGate (.H w) ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  rw [applyGate_ket]
  exact support_add
    (support_smul _ (supportedOn_ket _ _ (batchedWindowValid_address_update s hs w hw false)))
    (support_smul _ (supportedOn_ket _ _ (batchedWindowValid_address_update s hs w hw true)))

theorem batchedWindowValid_prepare (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (ψ : State)
    (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (batchedWindowValid_H w (hws w (by simp)) ψ hψ)


theorem actualBatchedWindowState_supported (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (ψ : State)
    (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w) ψ) := by
  apply support_linear _ _ ?_ ψ hψ
  intro s hs
  simpa [ket] using supportedOn_ket BatchedWindowValid _
    (actualBatchedWindowState_valid Q hQ hn w s hs)

theorem actualBatchedWindow_branch_supported (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (start : Nat) (history : Fin start → Bool)
    (b : InstrumentBranch)
    (hb : b ∈ (((actualBatchedWindow w).program start).instantiate
      (readConstant coefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (b.kraus ψ) := by
  obtain ⟨c,hc⟩ := (actualBatchedWindow_coherent Q hQ hn w start history).branch_coefficient b hb
  rw [hc.on_supported hψ]
  exact support_smul c (actualBatchedWindowState_supported Q hQ hn w ψ hψ)
end ShorECDLP.Paper2607_13816.ChallengeMigration
