import ShorECDLP.Submission.«2607_13816».Fourier.Support
import ShorECDLP.Submission.«2607_13816».Window.FourierCommutation
import ShorECDLP.Submission.«2607_13816».Window.Kernel
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
theorem windowPointValid_fourier_supported (dir : PhaseDir) (ws : List Wire)
    (prior bs : List Bool) (hw : ∀ w∈ws,839≤w) (ψ : State)
    (hψ : SupportedOn WindowPointValid ψ) :
    SupportedOn WindowPointValid (fourierBranch dir ws prior bs ψ) := by
  apply fourierBranch_supported dir ws prior bs WindowPointValid _ ψ hψ
  intro s hs
  apply windowPointValid_core s _ _ hs
  intro w hb
  rw [fourierClear_apply]
  have hn : w∉ws := by intro h; have := hw w h; dsimp only [Wire] at *; omega
  simp [hn]
/-- Address-only Fourier measurement can cross each disjoint arithmetic branch
without an extra post-measurement validity premise. -/
theorem preparedWindowCall_address_fourier_commute (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (hw : ∀ w∈ws,839≤w)
    (hb : ∀ w∈ws,w∉windowAddressBits j)
    (hs : ∀ w∈ws,w≠windowBankStart j+15)
    (b : InstrumentBranch) (hmem : b∈(preparedWindowCall x y hc j).run)
    (ψ : State) (hψ : SupportedOn WindowPointValid ψ) :
    fourierBranch dir ws prior bs (b.kraus ψ)=
      b.kraus (fourierBranch dir ws prior bs ψ) := by
  refine preparedWindowCall_branch_fourier_commute x y hc j dir ws prior bs ?_ hb ?_ hs b hmem ψ hψ ?_
  · intro w hm hp
    have hg := hw w hm
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hp
    try dsimp only [Wire] at *
    omega
  · intro w hm
    have hg := hw w hm
    try dsimp only [Wire] at *
    omega
  · exact windowPointValid_fourier_supported dir ws prior bs hw ψ hψ

/-- Any other physical window bank can be measured before this prepared call. -/
theorem preparedWindowCall_otherBank_fourier_commute (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j k : Nat) (hjk : j≠k) (dir : PhaseDir) (prior bs : List Bool)
    (b : InstrumentBranch) (hmem : b∈(preparedWindowCall x y hc j).run)
    (ψ : State) (hψ : SupportedOn WindowPointValid ψ) :
    fourierBranch dir (List.range' (windowBankStart k) 16).reverse prior bs (b.kraus ψ)=
      b.kraus (fourierBranch dir (List.range' (windowBankStart k) 16).reverse prior bs ψ) := by
  refine preparedWindowCall_address_fourier_commute x y hc j dir _ prior bs ?_ ?_ ?_ b hmem ψ hψ
  · intro w hm
    simp only [List.mem_reverse,List.mem_range'_1,windowBankStart] at hm
    try dsimp only [Wire] at *
    omega
  · intro w hm hb
    simp only [List.mem_reverse,List.mem_range'_1,windowBankStart] at hm
    simp only [windowAddressBits,List.mem_range'_1,windowBankStart] at hb
    try dsimp only [Wire] at *
    omega
  · intro w hm he
    simp only [List.mem_reverse,List.mem_range'_1,windowBankStart] at hm
    unfold windowBankStart at he
    try dsimp only [Wire] at *
    omega
end
end ShorECDLP.Paper2607_13816
