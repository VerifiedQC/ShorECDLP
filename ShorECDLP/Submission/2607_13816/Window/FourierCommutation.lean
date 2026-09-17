import ShorECDLP.Submission.«2607_13816».Fourier.Commutation
import ShorECDLP.Submission.«2607_13816».Window.Preparation
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem pointWrite_reset (P : Point) (s : BasisState) (w : Wire) (hw : w∉pointLogicalWires) :
    pointWrite P (s[w ↦ false])=(pointWrite P s)[w ↦ false] := by
  funext v
  by_cases hv : v=w
  · subst v; simp [pointWrite,hw,upd]
  · by_cases hp : v∈pointLogicalWires <;> simp [pointWrite,hp,upd,hv]
/-- A point update selected independently of an address block commutes with each measured branch. -/
theorem fourierBranch_pointWrite_commute (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (R : BasisState → Point) (hw : ∀ w∈ws,w∉pointLogicalWires)
    (hR : ∀ w∈ws,∀ s,R (s[w ↦ false])=R s) (ψ : State) :
    fourierBranch dir ws prior bs (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (R s) s) ψ)=
      Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (R s) s) (fourierBranch dir ws prior bs ψ) := by
  apply fourierBranch_mapDomain_commute
  · intro w h s
    exact pointWrite_frame _ _ w (hw w h)
  · intro w h s
    rw [hR w h s]
    exact pointWrite_reset _ _ _ (hw w h)

/-- Read canonical curve coordinates; invalid encodings default to infinity. -/
def encodedPointRead (z : Bool × (ShorECDLP.Fp × ShorECDLP.Fp)) : Point := by
  classical
  exact if h : ∃ P, fig14PointEncoding P=z then h.choose else 0
theorem encodedPointRead_encoding (P : Point) :
    encodedPointRead (fig14PointEncoding P)=P := by
  unfold encodedPointRead
  split
  · rename_i h
    exact fig14PointEncoding_injective h.choose_spec
  · rename_i h
    exact (h ⟨P,rfl⟩).elim
def statePointRead (s : BasisState) : Point := encodedPointRead (pointStateCoordinates s)
theorem statePointRead_correct (P : Point) (s : BasisState)
    (hp : pointStateCoordinates s=fig14PointEncoding P) : statePointRead s=P := by
  simp [statePointRead,hp,encodedPointRead_encoding]
theorem pointStateCoordinates_reset (s : BasisState) (w : Wire)
    (hw : w∉pointLogicalWires) : pointStateCoordinates (s[w ↦ false])=pointStateCoordinates s := by
  have hf : ∀ v∈pointLogicalWires,(s[w ↦ false]) v=s v := by
    intro v hv
    have hn : v≠w := by intro h; subst v; exact hw hv
    simp [upd,hn]
  have hx : wireValues (List.range' 263 256) (s[w ↦ false])=wireValues (List.range' 263 256) s := by
    apply List.map_congr_left
    intro v hv
    apply hf v
    simp [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,hv]
  have hy : wireValues (List.range' 580 256) (s[w ↦ false])=wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro v hv
    apply hf v
    simp [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,hv]
  simp only [pointStateCoordinates,hx,hy,hf 838 (by decide +kernel)]
theorem statePointRead_reset (s : BasisState) (w : Wire) (hw : w∉pointLogicalWires) :
    statePointRead (s[w ↦ false])=statePointRead s := by
  unfold statePointRead
  rw [pointStateCoordinates_reset s w hw]
theorem preparedWindowCallState_read (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (s : BasisState) (hs : WindowPointValid s) :
    preparedWindowCallState x y hc j s=
      pointWrite (statePointRead s+windowPointDelta x y hc j (windowPrepareState j s)) s := by
  obtain ⟨hv,P,hp⟩ := hs
  rw [statePointRead_correct P s hp]
  exact preparedWindowCallState_correct x y hc j P s hv hp

private theorem address_reset (bits : List Wire) (s : BasisState) (w : Wire)
    (hw : w∉bits) : tableAddressValue bits (s[w ↦ false])=tableAddressValue bits s := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    have hb : b≠w := by intro h; subst b; exact hw (by simp)
    simp only [tableAddressValue,upd,hb,ite_false]
    rw [ih (by intro h; exact hw (by simp [h]))]
private theorem prepare_reset (j : Nat) (s : BasisState) (w : Wire)
    (hb : w∉windowAddressBits j) (hr : w≠836) (hs : w≠windowBankStart j+15) :
    windowPrepareState j (s[w ↦ false])=(windowPrepareState j s)[w ↦ false] := by
  funext v
  have hr' : (836 : Wire)≠w := Ne.symm hr
  have hs' : windowBankStart j+15≠w := Ne.symm hs
  by_cases hv : v=w
  · subst v
    simp [windowPrepareState,signedAddressState,tableXorState,upd,hb,hr',hs']
  · simp [windowPrepareState,signedAddressState,tableXorState,upd,hv,hr',hs']
theorem preparedWindowDelta_reset (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (s : BasisState) (w : Wire)
    (hb : w∉windowAddressBits j) (hr : w≠836) (hs : w≠windowBankStart j+15) :
    windowPointDelta x y hc j (windowPrepareState j (s[w ↦ false]))=
      windowPointDelta x y hc j (windowPrepareState j s) := by
  rw [prepare_reset j s w hb hr hs]
  unfold windowPointDelta
  have ha := address_reset (List.range' (windowBankStart j) 15) (windowPrepareState j s) w hb
  simp only [ha]
  simp [upd,Ne.symm hs]
/-- The ideal map of an actual prepared call commutes with a disjoint Fourier block. -/
theorem preparedWindowIdeal_fourier_commute (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (hp : ∀ w∈ws,w∉pointLogicalWires)
    (hb : ∀ w∈ws,w∉windowAddressBits j)
    (hr : ∀ w∈ws,w≠836) (hs : ∀ w∈ws,w≠windowBankStart j+15) (ψ : State) :
    let f := fun s => pointWrite (statePointRead s+windowPointDelta x y hc j (windowPrepareState j s)) s
    fourierBranch dir ws prior bs (Finsupp.lmapDomain ℂ ℂ f ψ)=
      Finsupp.lmapDomain ℂ ℂ f (fourierBranch dir ws prior bs ψ) := by
  apply fourierBranch_pointWrite_commute dir ws prior bs _ hp
  intro w hw s
  rw [statePointRead_reset s w (hp w hw),preparedWindowDelta_reset x y hc j s w
    (hb w hw) (hr w hw) (hs w hw)]
/-- The actual arithmetic instrument implements the point-local ideal map. -/
theorem preparedWindowCall_read_coherent (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) : CoherentlyImplementsOn (preparedWindowCall x y hc j)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite
        (statePointRead s+windowPointDelta x y hc j (windowPrepareState j s)) s)) WindowPointValid := by
  apply (preparedWindowCall_coherent x y hc j).congrIdeal
  intro s hs
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ket]
  rw [preparedWindowCallState_read x y hc j s hs]
/-- Every actual arithmetic branch commutes, on valid supported states, with
an earlier disjoint Fourier branch; internal transcripts remain distinct. -/
theorem preparedWindowCall_branch_fourier_commute (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (hp : ∀ w∈ws,w∉pointLogicalWires)
    (hb : ∀ w∈ws,w∉windowAddressBits j)
    (hr : ∀ w∈ws,w≠836) (hs : ∀ w∈ws,w≠windowBankStart j+15)
    (b : InstrumentBranch) (hmem : b∈(preparedWindowCall x y hc j).run)
    (ψ : State) (hψ : SupportedOn WindowPointValid ψ)
    (hF : SupportedOn WindowPointValid (fourierBranch dir ws prior bs ψ)) :
    fourierBranch dir ws prior bs (b.kraus ψ)=
      b.kraus (fourierBranch dir ws prior bs ψ) := by
  obtain ⟨c,hc'⟩ := (preparedWindowCall_read_coherent x y hc j).branch_coefficient b hmem
  rw [hc'.on_supported hψ,hc'.on_supported hF,map_smul]
  rw [preparedWindowIdeal_fourier_commute x y hc j dir ws prior bs hp hb hr hs ψ]
end
end ShorECDLP.Paper2607_13816
