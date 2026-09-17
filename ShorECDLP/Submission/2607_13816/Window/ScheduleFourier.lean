import ShorECDLP.Submission.«2607_13816».Window.FourierSupport
import ShorECDLP.Submission.«2607_13816».Window.PreparedSchedule
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
theorem preparedWindowSum_reset (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (s : BasisState) (w : Wire) (hr : w≠836)
    (hb : ∀ i, j ≤ i → i < j + n → w∉windowAddressBits i)
    (hs : ∀ i, j ≤ i → i < j + n → w≠windowBankStart i+15) :
    preparedWindowSum x y hc n j (s[w ↦ false])=preparedWindowSum x y hc n j s := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [preparedWindowSum,preparedWindowSum]
    have hd := preparedWindowDelta_reset x y hc j s w
      (hb j (by omega) (by omega)) hr (hs j (by omega) (by omega))
    change preparedWindowDelta x y hc j (s[w ↦ false])=preparedWindowDelta x y hc j s at hd
    rw [hd,ih (j+1) (by intro i h1 h2; exact hb i (by omega) (by omega))
      (by intro i h1 h2; exact hs i (by omega) (by omega))]
theorem preparedWindowSchedule_read_coherent (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) : CoherentlyImplementsOn (preparedWindowSchedule x y hc n j)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite
        (statePointRead s+preparedWindowSum x y hc n j s) s)) WindowPointValid := by
  apply (preparedWindowSchedule_coherent x y hc n j).congrIdeal
  intro s hs
  obtain ⟨hv,P,hp⟩ := hs
  simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket]
  rw [statePointRead_correct P s hp,preparedWindowScheduleState_correct x y hc n j P s hv hp]
theorem preparedWindowScheduleIdeal_fourier_commute (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (hp : ∀ w∈ws,w∉pointLogicalWires) (hr : ∀ w∈ws,w≠836)
    (hb : ∀ i, j ≤ i → i < j + n → ∀ w∈ws,w∉windowAddressBits i)
    (hs : ∀ i, j ≤ i → i < j + n → ∀ w∈ws,w≠windowBankStart i+15) (ψ : State) :
    let f := fun s => pointWrite (statePointRead s+preparedWindowSum x y hc n j s) s
    fourierBranch dir ws prior bs (Finsupp.lmapDomain ℂ ℂ f ψ)=
      Finsupp.lmapDomain ℂ ℂ f (fourierBranch dir ws prior bs ψ) := by
  apply fourierBranch_pointWrite_commute dir ws prior bs _ hp
  intro w hw s
  rw [statePointRead_reset s w (hp w hw),preparedWindowSum_reset x y hc n j s w (hr w hw)
    (by intro i hi hn; exact hb i hi hn w hw) (by intro i hi hn; exact hs i hi hn w hw)]
theorem preparedWindowSchedule_branch_fourier_commute (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (hw : ∀ w∈ws,839≤w)
    (hb : ∀ i, j ≤ i → i < j + n → ∀ w∈ws,w∉windowAddressBits i)
    (hs : ∀ i, j ≤ i → i < j + n → ∀ w∈ws,w≠windowBankStart i+15)
    (b : InstrumentBranch) (hmem : b∈(preparedWindowSchedule x y hc n j).run)
    (ψ : State) (hψ : SupportedOn WindowPointValid ψ) :
    fourierBranch dir ws prior bs (b.kraus ψ)=
      b.kraus (fourierBranch dir ws prior bs ψ) := by
  have hp : ∀ w∈ws,w∉pointLogicalWires := by
    intro w hm hn
    have hlow := pointLogicalWires_bound w hn
    have hhigh := hw w hm
    dsimp only [Wire] at *
    omega
  have hr : ∀ w∈ws,w≠836 := by
    intro w hm
    have hhigh := hw w hm
    dsimp only [Wire] at *
    omega
  obtain ⟨c,hc'⟩ := (preparedWindowSchedule_read_coherent x y hc n j).branch_coefficient b hmem
  rw [hc'.on_supported hψ,hc'.on_supported
    (windowPointValid_fourier_supported dir ws prior bs hw ψ hψ),map_smul]
  rw [preparedWindowScheduleIdeal_fourier_commute x y hc n j dir ws prior bs hp hr hb hs ψ]
/-- A complete bank outside the schedule interval can be measured before it. -/
theorem preparedWindowSchedule_otherBank_fourier_commute (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j k : Nat) (hout : k < j ∨ j+n ≤ k) (dir : PhaseDir) (prior bs : List Bool)
    (b : InstrumentBranch) (hmem : b∈(preparedWindowSchedule x y hc n j).run)
    (ψ : State) (hψ : SupportedOn WindowPointValid ψ) :
    fourierBranch dir (List.range' (windowBankStart k) 16).reverse prior bs (b.kraus ψ)=
      b.kraus (fourierBranch dir (List.range' (windowBankStart k) 16).reverse prior bs ψ) := by
  refine preparedWindowSchedule_branch_fourier_commute x y hc n j dir _ prior bs ?_ ?_ ?_ b hmem ψ hψ
  · intro w hm
    simp only [List.mem_reverse,List.mem_range'_1,windowBankStart] at hm
    dsimp only [Wire] at *
    omega
  · intro i hi hn w hm hb
    simp only [List.mem_reverse,List.mem_range'_1,windowBankStart] at hm
    simp only [windowAddressBits,List.mem_range'_1,windowBankStart] at hb
    omega
  · intro i hi hn w hm he
    simp only [List.mem_reverse,List.mem_range'_1,windowBankStart] at hm
    unfold windowBankStart at he
    dsimp only [Wire] at *
    omega
end
end ShorECDLP.Paper2607_13816
