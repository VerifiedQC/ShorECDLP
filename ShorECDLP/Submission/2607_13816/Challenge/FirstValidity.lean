import ShorECDLP.Submission.«2607_13816».Challenge.WindowValidity
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1

private theorem zero_word (n : Nat) : boolWordToNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]
private theorem zero_read (ws : List Wire) (s : BasisState)
    (hs : ∀ w ∈ ws, s w = false) :
    wireValues ws s = List.replicate ws.length false := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wireValues,List.map_cons,List.length_cons,List.replicate_succ]
    rw [hs w (by simp)]
    exact congrArg (false :: ·) (ih (fun v hv => hs v (List.mem_cons_of_mem w hv)))

/-- Before direct loading, only the query flag and address register may be nonzero. -/
def FirstWindowInput (s : BasisState) : Prop :=
  s 836 = true ∧ ∀ v, v ≠ 836 → v ∉ streamAddress → s v = false

theorem firstWindowInput_start : FirstWindowInput (zeroBasisState[836 ↦ true]) := by
  constructor
  · simp [upd]
  · intro v hv _
    simp [upd,hv,zeroBasisState]

theorem firstWindowInput_update (s : BasisState) (hs : FirstWindowInput s)
    (w : Wire) (hw : w ∈ streamAddress) (b : Bool) : FirstWindowInput (s[w ↦ b]) := by
  have hw' : 855 ≤ w ∧ w < 871 := by simpa [streamAddress,List.mem_range'_1] using hw
  have hwb : 855 ≤ w := hw'.1
  constructor
  · simpa only [upd,if_neg (by dsimp only [Wire] at *; omega : (836:Wire) ≠ w)] using hs.1
  · intro v hv ha
    have hvw : v ≠ w := by intro he; subst v; exact ha hw
    simpa only [upd,if_neg hvw] using hs.2 v hv ha

theorem firstWindowInput_ready (s : BasisState) (hs : FirstWindowInput s) :
    BatchedPointReady s := by
  have hz (v : Wire) (hv : v < 836) : s v = false :=
    hs.2 v (by dsimp only [Wire] at *; omega) (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)
  have hx : wireValues (List.range' 263 256) s = List.replicate 256 false := by
    exact (zero_read _ s (fun v hv => hz v (by
      simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega))).trans
      (by simp only [List.length_range'])
  have hy : wireValues (List.range' 580 256) s = List.replicate 256 false := by
    exact (zero_read _ s (fun v hv => hz v (by
      simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega))).trans
      (by simp only [List.length_range'])
  refine ⟨⟨⟨?_,?_,?_,?_⟩,hs.1⟩,?_⟩
  · intro v hv
    exact hz v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  · exact hs.2 837 (by decide) (by simp [streamAddress])
  · rw [hx]; rw [zero_word]; norm_num [ShorECDLP.p]
  · rw [hy]; rw [zero_word]; norm_num [ShorECDLP.p]
  · intro v hv
    have hb : 1024 ≤ v := by
      simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    exact hs.2 v (by dsimp only [Wire] at *; omega) (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)

theorem firstWindowInput_lookup (s : BasisState) (hs : FirstWindowInput s) :
    DirectPointLookupValid (List.range' 519 16) 836 s := by
  refine ⟨?_,?_,hs.1⟩
  · intro v hv
    apply hs.2
    · simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
    · simp only [List.mem_range'_1] at hv
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega
  · intro v hv
    have hb : v < 839 := by
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    have hn : v ≠ 836 := by
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    exact hs.2 v hn (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)

theorem firstWindowInput_pointWrite (s : BasisState) (hs : FirstWindowInput s) (P : Point) :
    BatchedWindowValid (pointWrite P s) :=
  ⟨pointWrite_batchedReady P s (firstWindowInput_ready s hs),P,pointWrite_coordinates P s⟩



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
private theorem support_linear (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn W (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn W (L ψ) := by
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

theorem firstWindowInput_H (w : Wire) (hw : w ∈ streamAddress)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn FirstWindowInput (applyGate (.H w) ψ) := by
  apply support_linear FirstWindowInput FirstWindowInput (applyGate (.H w)) ?_ ψ hψ
  intro s hs
  rw [applyGate_ket]
  exact support_add
    (support_smul _ (supportedOn_ket _ _ (firstWindowInput_update s hs w hw false)))
    (support_smul _ (supportedOn_ket _ _ (firstWindowInput_update s hs w hw true)))

theorem firstWindowInput_prepare (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (ψ : State)
    (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn FirstWindowInput (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (firstWindowInput_H w (hws w (by simp)) ψ hψ)

noncomputable def actualFirstWindowState (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
    ((2^(16*15)) • G) (tableAddressValue (List.range' 855 16) s)) s

theorem actualFirstWindowState_supported (Q : Point) (ψ : State)
    (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn BatchedWindowValid
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q) ψ) := by
  apply support_linear FirstWindowInput BatchedWindowValid _ ?_ ψ hψ
  intro s hs
  rw [show Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q) (ket s) =
      ket (actualFirstWindowState Q s) from by simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]]
  exact supportedOn_ket _ _ (firstWindowInput_pointWrite s hs _)

theorem actualFirstWindow_coherent_input (Q : Point) (hQ : order • Q = 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actualFirstWindow.program start).instantiate
      (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput := by
  obtain ⟨cs,ha,hm⟩ := actualFirstWindow_coherent Q hQ start history
  exact ⟨cs,ha.imp (fun _ _ hb s hs => hb s (firstWindowInput_lookup s hs)),hm⟩

theorem actualFirstWindow_branch_supported (Q : Point) (hQ : order • Q = 0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((actualFirstWindow.program start).instantiate
      (readConstant coefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn BatchedWindowValid (b.kraus ψ) := by
  obtain ⟨c,hc⟩ := (actualFirstWindow_coherent_input Q hQ start history).branch_coefficient b hb
  rw [hc.on_supported hψ]
  exact support_smul c (actualFirstWindowState_supported Q ψ hψ)

end ShorECDLP.Paper2607_13816.ChallengeMigration
