import ShorECDLP.Submission.«2607_13816».Window.RawInitialize
import ShorECDLP.Submission.«2607_13816».Window.RawSchedule
import ShorECDLP.Submission.«2607_13816».Window.RawCoordinate
import ShorECDLP.Submission.«2607_13816».OrderFinding.PointEigenstates
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

/-- Full point encoding, rather than just coordinate nonsingularity, supplies
local raw validity away from the selected constant's exceptional set. -/
theorem signedRawDomain_of_encoding (x y : Nat → Nat) (P : Point) (s : BasisState)
    (hs : PointLookupValid s)
    (hx : x (tableAddressValue pointLookupAddress s)<ShorECDLP.p)
    (hy : signedPointTableValue y s<ShorECDLP.p)
    (hC : curve.toAffine.Nonsingular (x (tableAddressValue pointLookupAddress s) : ShorECDLP.Fp)
      (signedPointTableValue y s : ShorECDLP.Fp))
    (he : pointStateCoordinates s=fig14PointEncoding P)
    (hout : P ∉ fig14ExceptionalPoints (.some hC)) : SignedRawDomain x y s := by
  cases P with
  | zero => exact False.elim (hout (by change (0 : Point) ∈ _; simp [fig14ExceptionalPoints]))
  | @some a b hP =>
    have ha := congrArg (fun v : Bool × (ShorECDLP.Fp × ShorECDLP.Fp) => v.2.1) he
    have hb := congrArg (fun v : Bool × (ShorECDLP.Fp × ShorECDLP.Fp) => v.2.2) he
    simp only [pointStateCoordinates,fig14PointEncoding] at ha hb
    have hf := fig14_nonexceptional_factors hP hC hout
    apply (signedRawDomain_iff_selected x y s hs).mpr
    apply fig14RawDomain_of_factors _ _ hx hy s hs.1 hs.2
    · simpa only [ha] using hf.1
    · simpa only [ha,hb] using hf.2

private theorem write_ext (P : Point) (s t : BasisState)
    (ht : Secp256k1ZeroAllowedInputValid t)
    (he : pointStateCoordinates t=fig14PointEncoding P)
    (hf : ∀ w, w ∉ pointLogicalWires → t w=s w) : t=pointWrite P s := by
  have hw := (pointStateCoordinates_word t ht).trans (congrArg pointCoordinateWord he)
  have hp := pointWrite_word P s
  have hwords : wireValues pointLogicalWires t=wireValues pointLogicalWires (pointWrite P s) := hw.trans hp.symm
  funext w
  by_cases hm : w∈pointLogicalWires
  · exact List.map_inj_left.mp hwords w hm
  · exact (hf w hm).trans (pointWrite_frame P s w hm).symm

/-- The entire output state is the group sum, including the infinity marker,
with every wire outside the point word unchanged. -/
theorem signedRawPointState_correct (x y : Nat → Nat) (P : Point) (s : BasisState)
    (hs : PointLookupValid s)
    (hx : x (tableAddressValue pointLookupAddress s)<ShorECDLP.p)
    (hy : signedPointTableValue y s<ShorECDLP.p)
    (hC : curve.toAffine.Nonsingular (x (tableAddressValue pointLookupAddress s) : ShorECDLP.Fp)
      (signedPointTableValue y s : ShorECDLP.Fp))
    (he : pointStateCoordinates s=fig14PointEncoding P)
    (hout : P ∉ fig14ExceptionalPoints (.some hC)) :
    signedLookupCoordinateState x y s=pointWrite (P+.some hC) s := by
  have henc := fig14CoordinateState_encoded
    (x (tableAddressValue pointLookupAddress s) : ShorECDLP.Fp)
    (signedPointTableValue y s : ShorECDLP.Fp) s hs.1 hs.2
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] at henc
  rw [he,fig14EncodedEquiv_nonexceptional hC P hout] at henc
  apply write_ext _ s _ (signedLookupCoordinateState_ready x y s hs).1
  · rw [signedLookupCoordinateState_eq x y s hs]
    exact henc
  · intro w hw
    apply signedLookupCoordinateState_frame x y s hs w
    · intro hm
      exact hw (by simp only [pointLogicalWires,pointCorrectionX,List.mem_append]; exact Or.inl hm)
    · intro hm
      exact hw (by simp only [pointLogicalWires,pointCorrectionYInf,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; exact Or.inr (Or.inl hm))

/-- The local group-sum encoding and query readiness are available for the next
step; its own exceptional-set exclusion must still be proved separately. -/
theorem signedRawPointState_output (x y : Nat → Nat) (P : Point) (s : BasisState)
    (hs : PointLookupValid s)
    (hx : x (tableAddressValue pointLookupAddress s)<ShorECDLP.p)
    (hy : signedPointTableValue y s<ShorECDLP.p)
    (hC : curve.toAffine.Nonsingular (x (tableAddressValue pointLookupAddress s) : ShorECDLP.Fp)
      (signedPointTableValue y s : ShorECDLP.Fp))
    (he : pointStateCoordinates s=fig14PointEncoding P)
    (hout : P ∉ fig14ExceptionalPoints (.some hC)) :
    SignedRawDomain x y s ∧ PointLookupValid (signedLookupCoordinateState x y s) ∧
      pointStateCoordinates (signedLookupCoordinateState x y s)=fig14PointEncoding (P+.some hC) := by
  refine ⟨signedRawDomain_of_encoding x y P s hs hx hy hC he hout,
    signedLookupCoordinateState_ready x y s hs,?_⟩
  rw [signedRawPointState_correct x y P s hs hx hy hC he hout,pointWrite_coordinates]
private theorem core_word (s t : BasisState) (he : ∀ w, w<839 → t w=s w)
    (bits : List Wire) (hb : ∀ w∈bits,w<839) : wireValues bits t=wireValues bits s := by
  apply List.map_congr_left
  intro w hw
  exact he w (hb w hw)
private theorem core_coordinates (s t : BasisState) (he : ∀ w, w<839 → t w=s w) :
    pointStateCoordinates t=pointStateCoordinates s := by
  have hx := core_word s t he (List.range' 263 256) (by
    intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hy := core_word s t he (List.range' 580 256) (by
    intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,he 838 (by decide)]

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

/-- The exact input to a parked raw call, after physical address preparation. -/
def preparedRawPointInput (j : Nat) (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm (windowBankStart j) (by unfold windowBankStart; omega)).symm
    (windowPrepareState j s)

private theorem input_core (j : Nat) (s : BasisState) (w : Wire) (hw : w<839) :
    preparedRawPointInput j s w=s w := by
  simp only [preparedRawPointInput,relabelBasis,Equiv.symm_symm,windowAddressPerm_core _ _ w hw]
  apply signedAddressState_frame
  simp only [windowAddressBits,List.mem_range'_1,windowBankStart]
  dsimp only [Wire] at *
  omega

/-- The prepared call restores the input banks and preserves the entire
point encoding while advancing it by the selected nonexceptional group sum. -/
theorem preparedRawPointState_correct (x y : Nat → Nat → Nat) (j : Nat) (P : Point)
    (s : BasisState) (hs : PointLookupValid s) (he : pointStateCoordinates s=fig14PointEncoding P)
    (hx : x j (tableAddressValue pointLookupAddress (preparedRawPointInput j s))<ShorECDLP.p)
    (hy : signedPointTableValue (y j) (preparedRawPointInput j s)<ShorECDLP.p)
    (hC : curve.toAffine.Nonsingular
      (x j (tableAddressValue pointLookupAddress (preparedRawPointInput j s)) : ShorECDLP.Fp)
      (signedPointTableValue (y j) (preparedRawPointInput j s) : ShorECDLP.Fp))
    (hout : P ∉ fig14ExceptionalPoints (.some hC)) :
    PreparedRawDomain x y j s ∧ preparedRawState x y j s=pointWrite (P+.some hC) s := by
  have ht := (windowPointValid_core s _ (input_core j s) ⟨hs,P,he⟩).1
  have hp := (core_coordinates s _ (input_core j s)).trans he
  have hd := signedRawDomain_of_encoding (x j) (y j) P _ ht hx hy hC hp hout
  have hc := signedRawPointState_correct (x j) (y j) P _ ht hx hy hC hp hout
  refine ⟨hd,?_⟩
  unfold preparedRawState parkedRawState
  change windowPrepareState j (relabelBasis _ (signedLookupCoordinateState (x j) (y j)
    (preparedRawPointInput j s))) = _
  rw [hc]
  unfold preparedRawPointInput
  rw [relabel_pointWrite,windowPrepareState_pointWrite,windowPrepareState_involution]

/-- Algebraic path conditions evaluated on complete point-written states.
Each step selects its constant from the actual prepared bank and excludes that
constant's exceptional set. This relation does not assert coverage or weight. -/
inductive RawPointPath (x y : Nat → Nat → Nat) : List Nat → Point → BasisState → Point → Prop where
  | nil (P : Point) (s : BasisState) : RawPointPath x y List.nil P s P
  | cons {j : Nat} {js : List Nat} {P Q : Point} {s : BasisState}
      (hx : x j (tableAddressValue pointLookupAddress (preparedRawPointInput j s))<ShorECDLP.p)
      (hy : signedPointTableValue (y j) (preparedRawPointInput j s)<ShorECDLP.p)
      (hC : curve.toAffine.Nonsingular
        (x j (tableAddressValue pointLookupAddress (preparedRawPointInput j s)) : ShorECDLP.Fp)
        (signedPointTableValue (y j) (preparedRawPointInput j s) : ShorECDLP.Fp))
      (hout : P ∉ fig14ExceptionalPoints (.some hC))
      (tail : RawPointPath x y js (P+.some hC) (pointWrite (P+.some hC) s) Q) :
      RawPointPath x y (j::js) P s Q

/-- Per-step algebraic exclusions propagate actual raw validity and full group
encoding through the supplied execution order, including repeated indices. -/
theorem rawPointPath_correct (x y : Nat → Nat → Nat) {js : List Nat} {P Q : Point}
    {s : BasisState} (path : RawPointPath x y js P s Q)
    (hs : PointLookupValid s) (he : pointStateCoordinates s=fig14PointEncoding P) :
    RawWindowScheduleDomain x y js s ∧ rawWindowScheduleState x y js s=pointWrite Q s := by
  induction path with
  | nil P s =>
    exact ⟨trivial,write_ext P s s hs.1 he (by intros; rfl)⟩
  | @cons j js P Q s hx hy hC hout tail ih =>
    have hc := preparedRawPointState_correct x y j P s hs he hx hy hC hout
    have ht : PointLookupValid (pointWrite (P+.some hC) s) :=
      ⟨pointWrite_valid _ s hs.1,(pointWrite_frame _ s 836 (by decide +kernel)).trans hs.2⟩
    have hi := ih ht (pointWrite_coordinates _ s)
    constructor
    · exact ⟨hc.1,hc.2.symm ▸ hi.1⟩
    · simp only [rawWindowScheduleState,hc.2,hi.2,pointWrite_overwrite]

/-- The physical first lookup initializes the algebraic path. A supplied path
certificate yields the initialized raw domain and the complete final point. -/
theorem initializedRawPointPath_correct (A P : Point) (x y : Nat → Nat → Nat)
    (js : List Nat) (Q : Point) (s : BasisState) (hs : PointInitializeValid s)
    (path : RawPointPath x y js
      (firstWindowTable A P (tableAddressValue (List.range' 855 16) s)) (rawInitialState A P s) Q) :
    InitializedRawDomain A P x y js s ∧
      rawWindowScheduleState x y js (rawInitialState A P s)=pointWrite Q s := by
  have hc := rawPointPath_correct x y path (rawInitialState_ready A P s hs).1
    (pointWrite_coordinates _ s)
  refine ⟨⟨hs,hc.1⟩,?_⟩
  rw [hc.2,rawInitialState,pointWrite_overwrite]

/-- Coherent group-sum semantics on clean inputs with algebraic path
certificates, allowing the final point to depend on the scalar input. -/
theorem initializedRawPointPath_coherent (A P : Point) (x y : Nat → Nat → Nat)
    (js : List Nat) (out : BasisState → Point) :
    CoherentlyImplementsOn (initializedRawProgram A P x y js)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (out s) s))
      (fun s => PointInitializeValid s ∧ RawPointPath x y js
        (firstWindowTable A P (tableAddressValue (List.range' 855 16) s)) (rawInitialState A P s) (out s)) := by
  obtain ⟨cs,ha,hm⟩ := initializedRawProgram_coherent A P x y js
  refine ⟨cs,ha.imp ?_,hm⟩
  intro b c hb s hs
  have hc := initializedRawPointPath_correct A P x y js (out s) s hs.1 hs.2
  have h := hb s hc.1
  simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,hc.2] using h

end
end ShorECDLP.Paper2607_13816
