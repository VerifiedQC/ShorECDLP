import ShorECDLP.Submission.«2607_13816».Window.SignedAddress
import ShorECDLP.Submission.«2607_13816».Window.Schedule
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

def windowAddressBits (j : Nat) : List Wire := List.range' (windowBankStart j) 15
def windowPrepareCircuit (j : Nat) : Circuit :=
  signedAddressCircuit 836 (windowBankStart j+15) (windowAddressBits j)
def windowPrepareState (j : Nat) : BasisState → BasisState :=
  signedAddressState 836 (windowBankStart j+15) (windowAddressBits j)
private theorem prepare_root (j : Nat) : 836∉windowAddressBits j := by
  simp only [windowAddressBits,List.mem_range'_1,windowBankStart]
  omega
private theorem prepare_sign (j : Nat) : windowBankStart j+15∉windowAddressBits j := by
  simp [windowAddressBits,List.mem_range'_1]
private theorem prepare_core (j : Nat) (s : BasisState) (w : Wire) (hw : w<839) :
    windowPrepareState j s w=s w := by
  apply signedAddressState_frame
  simp only [windowAddressBits,List.mem_range'_1,windowBankStart]
  dsimp only [Wire] at *
  omega
private theorem core_word (s t : BasisState) (he : ∀ w, w<839 → t w=s w)
    (bits : List Wire) (hb : ∀ w∈bits,w<839) : wireValues bits t=wireValues bits s := by
  apply List.map_congr_left
  intro w hw
  exact he w (hb w hw)
private theorem core_valid (s t : BasisState) (he : ∀ w, w<839 → t w=s w)
    (hv : PointLookupValid s) : PointLookupValid t := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro w hw
    have hb : w<839 := by
      simp only [List.mem_append,List.mem_range'_1] at hw
      dsimp only [Wire] at *
      omega
    rw [he w hb]
    exact hv.1.1 w hw
  · rw [he 837 (by decide)]; exact hv.1.2.1
  · rw [core_word s t he (List.range' 263 256) (by
      intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)]
    exact hv.1.2.2.1
  · rw [core_word s t he (List.range' 580 256) (by
      intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)]
    exact hv.1.2.2.2
  · rw [he 836 (by decide)]; exact hv.2
private theorem core_coordinates (s t : BasisState) (he : ∀ w, w<839 → t w=s w) :
    pointStateCoordinates t=pointStateCoordinates s := by
  have hx := core_word s t he (List.range' 263 256) (by
    intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hy := core_word s t he (List.range' 580 256) (by
    intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,he 838 (by decide)]

theorem windowPrepareState_ready (j : Nat) (s : BasisState) (hs : WindowPointValid s) :
    WindowPointValid (windowPrepareState j s) := by
  obtain ⟨hv,P,hp⟩ := hs
  exact ⟨core_valid s _ (prepare_core j s) hv,P,(core_coordinates s _ (prepare_core j s)).trans hp⟩
theorem windowPrepareCircuit_ket (j : Nat) (s : BasisState) :
    Quantum.run (windowPrepareCircuit j) (ket s)=ket (windowPrepareState j s) :=
  signedAddressCircuit_ket _ _ _ (List.nodup_range' _ (by decide)) (prepare_root j) (prepare_sign j) s
theorem windowPrepareState_involution (j : Nat) (s : BasisState) :
    windowPrepareState j (windowPrepareState j s)=s :=
  signedAddressState_involution _ _ _ (prepare_root j) (prepare_sign j) s

def windowRawDigit (j : Nat) (s : BasisState) : Nat :=
  boolWordToNat (wireValues (windowAddressBits j) s)+32768*(s (windowBankStart j+15)).toNat

theorem windowPrepareState_address (j : Nat) (s : BasisState) (hs : s 836=true) :
    boolWordToNat (wireValues (windowAddressBits j) (windowPrepareState j s))=
      signedTableAddress 32768 (windowRawDigit j s) := by
  simpa only [windowAddressBits,List.length_range',show 2^15=32768 from rfl,windowRawDigit] using
    signedAddressState_value 836 (windowBankStart j+15) (windowAddressBits j) s hs

theorem windowPrepareCircuit_tCount (j : Nat) : ShorECDLP.tCount (windowPrepareCircuit j)=0 :=
  signedAddressCircuit_tCount _ _ _
private theorem prepare_point_bound (w : Wire) (hw : w∈pointLogicalWires) : w<839 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega
private theorem prepare_sign_not_point (j : Nat) : windowBankStart j+15∉pointLogicalWires := by
  intro h
  have hb := prepare_point_bound _ h
  unfold windowBankStart at hb
  dsimp only [Wire] at hb
  omega

theorem windowPrepareState_pointWrite (j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    windowPrepareState j (pointWrite P s)=pointWrite P (windowPrepareState j s) := by
  have hr := pointWrite_frame P s 836 (by decide +kernel)
  have hsign := pointWrite_frame P s (windowBankStart j+15) (prepare_sign_not_point j)
  funext w
  by_cases hw : w∈pointLogicalWires
  · rw [prepare_core j _ w (prepare_point_bound w hw)]
    simp [pointWrite,hw]
  · simp only [pointWrite_frame P _ w hw]
    simp only [windowPrepareState,signedAddressState,tableXorState,hr,hsign,
      pointWrite_frame P s w hw]

def preparedWindowCall (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).seq (windowCall x y hc j)).seq
    (.unitary (windowPrepareCircuit j) .done)
def preparedWindowCallState (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (s : BasisState) : BasisState :=
  windowPrepareState j (windowCallState x y hc j (windowPrepareState j s))

theorem preparedWindowCallState_correct (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hp : pointStateCoordinates s=fig14PointEncoding P) :
    preparedWindowCallState x y hc j s=
      pointWrite (P+windowPointDelta x y hc j (windowPrepareState j s)) s := by
  rw [preparedWindowCallState,windowCallState_correct x y hc j P _
    (windowPrepareState_ready j s ⟨hs,P,hp⟩).1
    ((core_coordinates s _ (prepare_core j s)).trans hp),windowPrepareState_pointWrite,
    windowPrepareState_involution]

private theorem prepare_coherent (j : Nat) :
    CoherentlyImplementsOn (.unitary (windowPrepareCircuit j) .done)
      (Finsupp.lmapDomain ℂ ℂ (windowPrepareState j)) WindowPointValid := by
  apply (CoherentlyImplementsOn.unitary (windowPrepareCircuit j) WindowPointValid).congrIdeal
  intro s _
  simpa [ket] using windowPrepareCircuit_ket j s

theorem preparedWindowCall_coherent (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) : CoherentlyImplementsOn (preparedWindowCall x y hc j)
      (Finsupp.lmapDomain ℂ ℂ (preparedWindowCallState x y hc j)) WindowPointValid := by
  have hb : CoherentlyImplementsOn (windowCall x y hc j)
      (Finsupp.lmapDomain ℂ ℂ (windowCallState x y hc j)) WindowPointValid := by
    obtain ⟨cs,ha,hm⟩ := parkedWindowProgram_coherent (windowBankStart j) (by unfold windowBankStart; omega) (x j) (y j) (hc j)
    exact ⟨cs,ha.imp (fun b c h s hs => h s hs.1),hm⟩
  have hf := (prepare_coherent j).seq hb (by
    intro s hs
    simpa [ket] using supportedOn_ket _ _ (windowPrepareState_ready j s hs))
  have hall := hf.seq (prepare_coherent j) (by
    intro s hs
    simpa [LinearMap.comp_apply,ket] using supportedOn_ket _ _
      (windowCallState_ready x y hc j _ (windowPrepareState_ready j s hs)))
  apply hall.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket,preparedWindowCallState]

private theorem address_word (bits : List Wire) (s : BasisState) :
    tableAddressValue bits s=boolWordToNat (wireValues bits s) := by
  induction bits with
  | nil => rfl
  | cons w ws ih =>
    change (s w).toNat+2*tableAddressValue ws s=(s w).toNat+2*boolWordToNat (wireValues ws s)
    rw [ih]

theorem windowRawDigit_bound (j : Nat) (s : BasisState) : windowRawDigit j s<65536 := by
  have hb := boolWordToNat_lt_pow_two (wireValues (windowAddressBits j) s)
  simp only [wireValues,List.length_map,windowAddressBits,List.length_range'] at hb
  change boolWordToNat (wireValues (windowAddressBits j) s)<32768 at hb
  unfold windowRawDigit
  cases s (windowBankStart j+15) <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem preparedWindowCallState_ready (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (s : BasisState) (hs : WindowPointValid s) :
    WindowPointValid (preparedWindowCallState x y hc j s) :=
  windowPrepareState_ready j _ (windowCallState_ready x y hc j _ (windowPrepareState_ready j s hs))

theorem preparedWindowCallState_frame (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (s : BasisState) (hs : WindowPointValid s) (w : Wire) (hw : w∉pointLogicalWires) :
    preparedWindowCallState x y hc j s w=s w := by
  obtain ⟨hv,P,hp⟩ := hs
  rw [preparedWindowCallState_correct x y hc j P s hv hp]
  exact pointWrite_frame _ s w hw

private theorem prepare_seq_T (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b

private theorem prepare_unitary_T (j : Nat) :
    (AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).tCount=0 := by
  change ShorECDLP.tCount (windowPrepareCircuit j)+0=0
  rw [windowPrepareCircuit_tCount,Nat.zero_add]
private theorem prepare_unitary_M (j : Nat) :
    (AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).measurementCount=0 := rfl

private theorem prepare_wrap_T (j : Nat) (body : AdaptiveCircuit) :
    (((AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).seq body).seq
      (.unitary (windowPrepareCircuit j) .done)).tCount=body.tCount := by
  simp only [prepare_seq_T,prepare_unitary_T,Nat.add_zero,Nat.zero_add]
private theorem prepare_wrap_M (j : Nat) (body : AdaptiveCircuit) :
    (((AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).seq body).seq
      (.unitary (windowPrepareCircuit j) .done)).measurementCount=body.measurementCount := by
  simp only [modularMeasurements_seq,prepare_unitary_M,Nat.add_zero,Nat.zero_add]

theorem preparedWindowCall_tCount (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) : (preparedWindowCall x y hc j).tCount=(windowCall x y hc j).tCount :=
  prepare_wrap_T j (windowCall x y hc j)

theorem preparedWindowCall_measurements (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) : (preparedWindowCall x y hc j).measurementCount=(windowCall x y hc j).measurementCount :=
  prepare_wrap_M j (windowCall x y hc j)

/-- The physical call selects the reflected odd-table entry from the original raw digit. -/
theorem preparedWindowCallState_selected (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hp : pointStateCoordinates s=fig14PointEncoding P) :
    preparedWindowCallState x y hc j s=pointWrite (P+
      if s (windowBankStart j+15) then .some (hc j (signedTableAddress 32768 (windowRawDigit j s)))
      else -(.some (hc j (signedTableAddress 32768 (windowRawDigit j s))))) s := by
  rw [preparedWindowCallState_correct x y hc j P s hs hp]
  have hsign := signedAddressState_frame 836 (windowBankStart j+15) (windowAddressBits j) s
    (windowBankStart j+15) (prepare_sign j)
  have ha : tableAddressValue (List.range' (windowBankStart j) 15) (windowPrepareState j s)=
      signedTableAddress 32768 (windowRawDigit j s) := by
    rw [address_word]
    exact windowPrepareState_address j s hs.2
  simp only [windowPointDelta,show windowPrepareState j s (windowBankStart j+15)=s (windowBankStart j+15) from hsign,ha]

private theorem prepare_support (j : Nat) : circuitWires (windowPrepareCircuit j) ⊆
    List.range 839++List.range' (windowBankStart j) 16 := by
  intro w hw
  simp only [windowPrepareCircuit,signedAddressCircuit,circuitWires,List.flatMap_append,
    tableXorGates,List.flatMap_map,List.mem_append,List.mem_flatMap,
    gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with ⟨v,hv,hw⟩ | ⟨v,hv,hw⟩
  · rcases hw with rfl | rfl
    · exact List.mem_append_left _ (List.mem_range.mpr (by omega))
    · apply List.mem_append_right
      simp only [windowAddressBits,List.mem_range'_1] at hv ⊢
      omega
  · rcases hw with rfl | rfl
    · apply List.mem_append_right
      simp only [List.mem_range'_1]
      dsimp only [Wire]
      omega
    · apply List.mem_append_right
      simp only [windowAddressBits,List.mem_range'_1] at hv ⊢
      omega

theorem preparedWindowCall_support (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) : (preparedWindowCall x y hc j).wires ⊆
      List.range 839++List.range' (windowBankStart j) 16 := by
  intro w hw
  rw [preparedWindowCall,modularWires_seq,modularWires_seq] at hw
  have hp : (AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).wires ⊆
      List.range 839++List.range' (windowBankStart j) 16 := by
    simpa only [AdaptiveCircuit.wires,List.append_nil] using prepare_support j
  rcases hw with (hw | hw) | hw
  · exact hp hw
  · exact parkedWindowProgram_tight_support (windowBankStart j) (by unfold windowBankStart; omega) (x j) (y j) (hc j) hw
  · exact hp hw

theorem windowPrepareCircuit_wellFormed (j : Nat) : CircuitWellFormed (windowPrepareCircuit j) :=
  signedAddressCircuit_wellFormed _ _ _ (prepare_root j) (prepare_sign j)

end
end ShorECDLP.Paper2607_13816
