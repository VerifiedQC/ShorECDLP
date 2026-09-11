import ShorECDLP.Submission.«2607_13816».Window.SignedPoint
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
/-- Swap the active 16-bit address bank with a disjoint parked bank. -/
def windowAddressSwap (start w : Nat) : Nat :=
  if 839≤w ∧ w<855 then start+(w-839)
  else if start≤w ∧ w<start+16 then 839+(w-start) else w
private theorem windowAddressSwap_involutive (start : Nat) (hs : 855≤start) :
    Function.Involutive (windowAddressSwap start) := by
  intro w
  unfold windowAddressSwap
  split
  · rename_i h
    rw [if_neg (by omega),if_pos (by omega)]
    omega
  · rename_i h
    split
    · rename_i ht
      rw [if_pos (by omega)]
      omega
    · rename_i ht
      rfl
def windowAddressPerm (start : Nat) (hs : 855≤start) : Wire ≃ Wire :=
  (windowAddressSwap_involutive start hs).toPerm _
theorem windowAddressPerm_core (start : Nat) (hs : 855≤start) (w : Wire) (hw : w<839) :
    windowAddressPerm start hs w=w := by
  change windowAddressSwap start w=w
  simp only [windowAddressSwap,if_neg (by (try dsimp only [Wire] at *); omega : ¬(839≤w ∧ w<855)),
    if_neg (by (try dsimp only [Wire] at *); omega : ¬(start≤w ∧ w<start+16))]
theorem windowAddressPerm_address (start : Nat) (hs : 855≤start) (i : Nat) (hi : i<16) :
    windowAddressPerm start hs (839+i)=start+i := by
  change windowAddressSwap start (839+i)=start+i
  rw [windowAddressSwap,if_pos (by omega)]
  omega
theorem windowAddressPerm_bound (start : Nat) (hs : 855≤start) (w : Wire) (hw : w<855) :
    windowAddressPerm start hs w<start+16 := by
  by_cases h : w<839
  · rw [windowAddressPerm_core start hs w h]; (try dsimp only [Wire] at *); omega
  · change windowAddressSwap start w<start+16
    rw [windowAddressSwap,if_pos (by (try dsimp only [Wire] at *); omega)]
    (try dsimp only [Wire] at *); omega

def parkedWindowProgram (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) : AdaptiveCircuit :=
  (signedLookupPointProgram x y hc).relabel (windowAddressPerm start hs)
def parkedWindowState (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm start hs)
    (signedLookupPointState x y hc (relabelBasis (windowAddressPerm start hs).symm s))

private theorem parkedWindow_valid (start : Nat) (hs : 855≤start) (s : BasisState)
    (hv : PointLookupValid s) : PointLookupValid (relabelBasis (windowAddressPerm start hs).symm s) := by
  have he (w : Wire) (hw : w<839) : relabelBasis (windowAddressPerm start hs).symm s w=s w := by
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w hw]
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro w hw
    have hb : w<839 := by simp only [List.mem_append,List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    rw [he w hb]
    exact hv.1.1 w hw
  · rw [he 837 (by decide)]; exact hv.1.2.1
  · have hh : wireValues (List.range' 263 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 263 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.1
  · have hh : wireValues (List.range' 580 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 580 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.2
  · rw [he 836 (by decide)]; exact hv.2

theorem parkedWindowProgram_coherent (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    CoherentlyImplementsOn (parkedWindowProgram start hs x y hc)
      (Finsupp.lmapDomain ℂ ℂ (parkedWindowState start hs x y hc)) PointLookupValid := by
  have h := (signedLookupPointProgram_coherent x y hc).relabel (windowAddressPerm start hs)
  have hr : CoherentlyImplementsOn (parkedWindowProgram start hs x y hc)
      ((relabelState (windowAddressPerm start hs)).comp
        ((Finsupp.lmapDomain ℂ ℂ (signedLookupPointState x y hc)).comp (relabelState (windowAddressPerm start hs).symm))) PointLookupValid := by
    obtain ⟨cs,ha,hm⟩ := h
    exact ⟨cs,ha.imp (fun b c hb s hv => hb s (parkedWindow_valid start hs s hv)),hm⟩
  apply hr.congrIdeal
  intro s hv
  simp [parkedWindowState,LinearMap.comp_apply,relabelState,ket]
private theorem point_bank_bound (w : Wire) (hw : w∈pointLogicalWires) : w<839 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega
private theorem relabel_pointWrite (start : Nat) (hs : 855≤start)
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis (windowAddressPerm start hs)
      (pointWrite P (relabelBasis (windowAddressPerm start hs).symm s))=pointWrite P s := by
  have hsym : (windowAddressPerm start hs).symm=windowAddressPerm start hs := rfl
  funext w
  by_cases hw : w∈pointLogicalWires
  · have he := windowAddressPerm_core start hs w (point_bank_bound w hw)
    simp [relabelBasis,hsym,he,pointWrite,hw]
  · have hn : (windowAddressPerm start hs).symm w∉pointLogicalWires := by
      intro h
      have he := windowAddressPerm_core start hs _ (point_bank_bound _ h)
      rw [Equiv.apply_symm_apply] at he
      exact hw (he ▸ h)
    simp [relabelBasis,pointWrite,hw,hn]

private theorem relabel_coordinates (start : Nat) (hs : 855≤start) (s : BasisState) :
    pointStateCoordinates (relabelBasis (windowAddressPerm start hs).symm s)=pointStateCoordinates s := by
  have he (bits : List Wire) (hb : ∀ w∈bits,w<839) :
      wireValues bits (relabelBasis (windowAddressPerm start hs).symm s)=wireValues bits s := by
    apply List.map_congr_left
    intro w hw
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w (hb w hw)]
  have hx := he (List.range' 263 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hy := he (List.range' 580 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs 838 (by decide)]

private theorem parkedWindowState_correct (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hv : PointLookupValid s)
    (hP : pointStateCoordinates s=fig14PointEncoding P) :
    parkedWindowState start hs x y hc s=pointWrite
      (P+(if s (start+15) then .some (hc (tableAddressValue pointLookupAddress (relabelBasis (windowAddressPerm start hs).symm s)))
        else -(.some (hc (tableAddressValue pointLookupAddress (relabelBasis (windowAddressPerm start hs).symm s)))))) s := by
  unfold parkedWindowState
  rw [signedLookupPointState_correct x y hc P _ (parkedWindow_valid start hs s hv)
    ((relabel_coordinates start hs s).trans hP),relabel_pointWrite]
  have he : relabelBasis (windowAddressPerm start hs).symm s 854=s (start+15) := by
    simp only [relabelBasis,Equiv.symm_symm]
    rw [show (854:Wire)=839+15 by rfl,windowAddressPerm_address start hs 15 (by decide)]
  rw [he]

theorem parkedWindowProgram_support (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (parkedWindowProgram start hs x y hc).wires ⊆ List.range (start+16) := by
  intro w hw
  rw [parkedWindowProgram,AdaptiveCircuit.relabel_wires] at hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr (windowAddressPerm_bound start hs v (List.mem_range.mp (signedLookupPointProgram_wires x y hc hv)))

private theorem address_relabel (e : Wire ≃ Wire) (bits : List Wire) (s : BasisState) :
    tableAddressValue bits (relabelBasis e.symm s)=tableAddressValue (bits.map e) s := by
  induction bits with
  | nil => rfl
  | cons w ws ih => simp only [tableAddressValue,List.map_cons,relabelBasis,Equiv.symm_symm,ih]
theorem parkedWindow_address (start : Nat) (hs : 855≤start) (s : BasisState) :
    tableAddressValue pointLookupAddress (relabelBasis (windowAddressPerm start hs).symm s)=
      tableAddressValue (List.range' start 15) s := by
  rw [address_relabel]
  have he : pointLookupAddress.map (windowAddressPerm start hs)=List.range' start 15 := by
    apply List.ext_getElem
    · simp [pointLookupAddress]
    · intro i hi hj
      simp only [List.getElem_map,pointLookupAddress,List.getElem_range']
      simpa only [one_mul] using windowAddressPerm_address start hs i (by simpa [pointLookupAddress] using Nat.lt_trans hi (by decide : 15<16))
  rw [he]
theorem parkedWindowState_bank_correct (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a))
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hv : PointLookupValid s)
    (hP : pointStateCoordinates s=fig14PointEncoding P) :
    parkedWindowState start hs x y hc s=pointWrite
      (P+(if s (start+15) then .some (hc (tableAddressValue (List.range' start 15) s))
        else -(.some (hc (tableAddressValue (List.range' start 15) s))))) s := by
  have h := parkedWindowState_correct start hs x y hc P s hv hP
  simpa only [parkedWindow_address] using h

theorem parkedWindowProgram_tCount (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (parkedWindowProgram start hs x y hc).tCount=(signedLookupPointProgram x y hc).tCount := by
  simp [parkedWindowProgram]
theorem parkedWindowProgram_measurements (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (parkedWindowProgram start hs x y hc).measurementCount=(signedLookupPointProgram x y hc).measurementCount := by
  simp [parkedWindowProgram]

theorem parkedWindowProgram_tight_support (start : Nat) (hs : 855≤start) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (parkedWindowProgram start hs x y hc).wires ⊆ List.range 839++List.range' start 16 := by
  intro w hw
  rw [parkedWindowProgram,AdaptiveCircuit.relabel_wires] at hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  have hb := List.mem_range.mp (signedLookupPointProgram_wires x y hc hv)
  by_cases h : v<839
  · rw [windowAddressPerm_core start hs v h]
    exact List.mem_append_left _ (List.mem_range.mpr h)
  · have he : windowAddressPerm start hs v=start+(v-839) := by
      change windowAddressSwap start v=_
      rw [windowAddressSwap,if_pos (by dsimp only [Wire] at *; omega)]
    rw [he]
    apply List.mem_append_right
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *
    omega

end
end ShorECDLP.Paper2607_13816
