import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

def pointInitialize (P : Point) : Circuit :=
  xorConstant pointLogicalWires (boolWordToNat (pointCoordinateWord (fig14PointEncoding P)))

private theorem constantBits_roundtrip (bits : List Bool) :
    constantBits bits.length (boolWordToNat bits)=bits := by
  apply boolWordToNat_injective_of_length (constantBits_length _ _)
  rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt (boolWordToNat_lt_pow_two bits)]

theorem pointInitialize_correct (P : Point) (s : BasisState)
    (hz : wireValues pointLogicalWires s=List.replicate 513 false) :
    run (pointInitialize P) s=pointWrite P s := by
  have h := xorConstant_correct pointLogicalWires
    (boolWordToNat (pointCoordinateWord (fig14PointEncoding P))) s pointLogicalWires_nodup
  have hl : (pointCoordinateWord (fig14PointEncoding P)).length=513 := by
    simp [pointCoordinateWord]
  have hw : wireValues pointLogicalWires (run (pointInitialize P) s)=
      pointCoordinateWord (fig14PointEncoding P) := by
    rw [pointInitialize,h.1,hz]
    change constantBits 513 (boolWordToNat (pointCoordinateWord (fig14PointEncoding P)))=_
    rw [←hl,constantBits_roundtrip]
  funext w
  by_cases hm : w∈pointLogicalWires
  · exact List.map_inj_left.mp (hw.trans (pointWrite_word P s).symm) w hm
  · exact (h.2 w hm).trans (pointWrite_frame P s w hm).symm

theorem pointInitialize_HPFree (P : Point) : HPFree (pointInitialize P) :=
  xorConstant_HPFree _ _
theorem pointInitialize_wellFormed (P : Point) : CircuitWellFormed (pointInitialize P) :=
  xorConstant_wellFormed _ _
theorem pointInitialize_tCount (P : Point) : tCount (pointInitialize P)=0 :=
  xorConstant_tCount _ _
def PointInitializeValid (s : BasisState) : Prop :=
  PointLookupValid s ∧ wireValues pointLogicalWires s=List.replicate 513 false

theorem pointInitialize_coherent (P : Point) :
    CoherentlyImplementsOn (.unitary (pointInitialize P) .done)
      (Finsupp.lmapDomain ℂ ℂ (pointWrite P)) PointInitializeValid := by
  apply (CoherentlyImplementsOn.unitary (pointInitialize P) PointInitializeValid).congrIdeal
  intro s hs
  have h := Quantum.run_ket_agrees_classical (pointInitialize P) s (pointInitialize_HPFree P)
  rw [pointInitialize_correct P s hs.2] at h
  simpa [ket] using h

theorem pointInitialize_ready (P : Point) (s : BasisState) (hs : PointInitializeValid s) :
    WindowPointValid (pointWrite P s) := by
  refine ⟨⟨pointWrite_valid P s hs.1.1,?_⟩,P,pointWrite_coordinates P s⟩
  rw [pointWrite_frame P s 836 (by decide +kernel)]
  exact hs.1.2

def initializedScalarProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (pointInitialize (axisWindowOffset P 17+axisWindowOffset Q 17)) .done).seq
    (scalarWindowsProgram P Q hP hQ hrP hrQ)
def initializedScalarState (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) : BasisState :=
  scalarWindowsState P Q hP hQ hrP hrQ (pointWrite (axisWindowOffset P 17+axisWindowOffset Q 17) s)

theorem initializedScalar_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (initializedScalarProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (initializedScalarState P Q hP hQ hrP hrQ)) PointInitializeValid := by
  have h := (pointInitialize_coherent (axisWindowOffset P 17+axisWindowOffset Q 17)).seq
    (scalarWindows_coherent P Q hP hQ hrP hrQ) (by
      intro s hs
      simpa [ket] using supportedOn_ket _ _ (pointInitialize_ready _ s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket,initializedScalarState]

theorem initializedScalarState_correct (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : Nat) (ha : a<2^257) (hb : b<2^257)
    (s : BasisState) (hs : PointInitializeValid s)
    (hda : rawWindowDigits 17 0 s=windowDigits 16 17 a)
    (hdb : rawWindowDigits 17 17 s=windowDigits 16 17 b) :
    initializedScalarState P Q hP hQ hrP hrQ s=pointWrite (a • P+b • Q) s := by
  rw [initializedScalarState,scalarWindowsState_correct P Q hP hQ hrP hrQ a b ha hb _
    (pointInitialize_ready _ s hs).1 (pointWrite_coordinates _ s)
    (by rw [rawWindowDigits_pointWrite,hda]) (by rw [rawWindowDigits_pointWrite,hdb]),pointWrite_overwrite]

theorem pointInitialize_support (P : Point) : circuitWires (pointInitialize P) ⊆ pointLogicalWires := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  exact xorConstant_usesOnly _ _ g hg w hw

theorem initializedScalar_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (initializedScalarProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 := by
  intro w hw
  rw [initializedScalarProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · simp only [AdaptiveCircuit.wires,List.append_nil] at hw
    have hp := pointInitialize_support _ hw
    apply List.mem_append_left
    simp only [List.mem_range]
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hp
    dsimp only [Wire] at *
    omega
  · exact scalarWindows_support P Q hP hQ hrP hrQ hw

theorem initializedScalar_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (initializedScalarProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (initializedScalarProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (initializedScalar_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

private theorem initialize_T (P : Point) (body : AdaptiveCircuit) :
    ((AdaptiveCircuit.unitary (pointInitialize P) .done).seq body).tCount=body.tCount := by
  have h : (AdaptiveCircuit.unitary (pointInitialize P) .done).tCount=0 := by
    change tCount (pointInitialize P)+0=0
    rw [pointInitialize_tCount,Nat.zero_add]
  have ht := modularGateCount_seq tCost (AdaptiveCircuit.unitary (pointInitialize P) .done) body
  simpa only [gidneyGateCount_tCount,h,Nat.zero_add] using ht

theorem initializedScalar_tCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (initializedScalarProgram P Q hP hQ hrP hrQ).tCount=
      (scalarWindowsProgram P Q hP hQ hrP hrQ).tCount :=
  initialize_T _ _

private theorem initialize_M (P : Point) (body : AdaptiveCircuit) :
    ((AdaptiveCircuit.unitary (pointInitialize P) .done).seq body).measurementCount=body.measurementCount := by
  rw [modularMeasurements_seq]
  exact Nat.zero_add _

theorem initializedScalar_measurementCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (initializedScalarProgram P Q hP hQ hrP hrQ).measurementCount=
      (scalarWindowsProgram P Q hP hQ hrP hrQ).measurementCount :=
  initialize_M _ _

end
end ShorECDLP.Paper2607_13816
