import ShorECDLP.Submission.«2607_13816».Window.ScalarRegisters
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

def scalarRootFlip (s : BasisState) : BasisState := s[836 ↦ !s 836]
def ScalarComputeValid (s : BasisState) : Prop :=
  (∀ w : Wire, w<855 → s w=false) ∧ ScalarPaddingClean 0 s ∧ ScalarPaddingClean 17 s

private theorem root_other (s : BasisState) (w : Wire) (hw : w≠836) : scalarRootFlip s w=s w := by
  simp [scalarRootFlip,upd,hw]
private theorem root_word (ws : List Wire) (s : BasisState) (h : ∀ w∈ws, w≠836) :
    wireValues ws (scalarRootFlip s)=wireValues ws s := by
  apply List.map_congr_left
  intro w hw
  exact root_other s w (h w hw)
private theorem zero_word (ws : List Wire) (s : BasisState) (h : ∀ w∈ws, s w=false) :
    wireValues ws s=List.replicate ws.length false := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wireValues,List.map_cons,List.length_cons,List.replicate_succ]
    rw [h w (by simp)]
    exact congrArg (List.cons false) (ih (by intro q hq; exact h q (by simp [hq])))
private theorem value_zero (n : Nat) : boolWordToNat (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,boolWordToNat,Bool.toNat_false,ih,Nat.mul_zero,Nat.add_zero]

private theorem root_zero_word (ws : List Wire) (s : BasisState)
    (hs : ∀ w : Wire, w<855 → s w=false) (hw : ∀ w∈ws, w<855 ∧ w≠836) :
    wireValues ws (scalarRootFlip s)=List.replicate ws.length false := by
  rw [root_word ws s (by intro w h; exact (hw w h).2)]
  exact zero_word ws s (by intro w h; exact hs w (hw w h).1)

theorem scalarRootFlip_ready (s : BasisState) (hs : ScalarComputeValid s) :
    ScalarRegistersValid (scalarRootFlip s) := by
  have hx := root_zero_word (List.range' 263 256) s hs.1 (by
    intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hy := root_zero_word (List.range' 580 256) s hs.1 (by
    intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hp := root_zero_word pointLogicalWires s hs.1 (by
    intro w hw
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hw
    dsimp only [Wire] at *; omega)
  refine ⟨⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩,?_,?_⟩
  · intro w hw
    rw [root_other]
    · apply hs.1; simp only [List.mem_append,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega
    · simp only [List.mem_append,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega
  · rw [root_other s 837 (by decide)]; exact hs.1 837 (by decide)
  · rw [hx,value_zero]; exact ShorECDLP.Secp256k1.p_prime.pos
  · rw [hy,value_zero]; exact ShorECDLP.Secp256k1.p_prime.pos
  · simp [scalarRootFlip,hs.1 836 (by decide)]
  · simpa only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.length_append,
      List.length_range',List.length_singleton] using hp
  · unfold ScalarPaddingClean
    rw [root_word]
    · exact hs.2.1
    · intro w hw; simp only [List.mem_range'_1,windowBankStart] at hw; dsimp only [Wire] at *; omega
  · unfold ScalarPaddingClean
    rw [root_word]
    · exact hs.2.2
    · intro w hw; simp only [List.mem_range'_1,windowBankStart] at hw; dsimp only [Wire] at *; omega
private theorem root_pointWrite (P : Point) (s : BasisState) :
    scalarRootFlip (pointWrite P s)=pointWrite P (scalarRootFlip s) := by
  have hp : (836:Wire)∉pointLogicalWires := by decide +kernel
  funext w
  by_cases hw : w=836
  · subst w
    rw [scalarRootFlip,upd_same,pointWrite_frame P s 836 hp,pointWrite_frame P _ 836 hp]
    rfl
  · rw [root_other _ w hw]
    by_cases hm : w∈pointLogicalWires
    · simp only [pointWrite,if_pos hm]
    · rw [pointWrite_frame P s w hm,pointWrite_frame P (scalarRootFlip s) w hm,root_other s w hw]
private theorem root_twice (s : BasisState) : scalarRootFlip (scalarRootFlip s)=s := by
  funext w
  by_cases hw : w=836
  · subst w; simp [scalarRootFlip]
  · simp [scalarRootFlip,upd,hw]
private theorem root_scalar (j : Nat) (s : BasisState) :
    scalarInputValue j (scalarRootFlip s)=scalarInputValue j s := by
  unfold scalarInputValue
  rw [root_word]
  intro w hw
  simp only [List.mem_range'_1,windowBankStart] at hw
  dsimp only [Wire] at *
  omega
private theorem root_coherent (Valid : BasisState → Prop) :
    CoherentlyImplementsOn (.unitary [.X 836] .done)
      (Finsupp.lmapDomain ℂ ℂ scalarRootFlip) Valid := by
  apply (CoherentlyImplementsOn.unitary [.X 836] Valid).congrIdeal
  intro s _
  have h := Quantum.run_ket_agrees_classical [.X 836] s (by simp [HPFree])
  simpa [ket,Classical.run,Classical.applyGate,scalarRootFlip] using h

def scalarComputeProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary [.X 836] .done).seq
    (initializedScalarProgram P Q hP hQ hrP hrQ)).seq (.unitary [.X 836] .done)

theorem scalarCompute_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (scalarComputeProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)) ScalarComputeValid := by
  have h1 := (root_coherent ScalarComputeValid).seq
    (initializedScalar_registers_coherent P Q hP hQ hrP hrQ) (by
      intro s hs
      simpa [ket] using supportedOn_ket _ _ (scalarRootFlip_ready s hs))
  have h2 := h1.seq (root_coherent (fun _ => True)) (by
    intro s hs
    simp only [LinearMap.comp_apply,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    exact supportedOn_ket _ _ trivial)
  apply h2.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  change Finsupp.single (scalarRootFlip (scalarRegisterOutput P Q (scalarRootFlip s))) 1 =
    Finsupp.single (scalarRegisterOutput P Q s) 1
  simp only [scalarRegisterOutput,root_scalar,root_pointWrite,root_twice]

private theorem root_support : (AdaptiveCircuit.unitary [.X 836] .done).wires ⊆
    List.range 839++List.range' 855 544 := by
  intro w hw
  simp only [AdaptiveCircuit.wires,circuitWires,List.flatMap_cons,List.flatMap_nil,
    gateWires,List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at hw
  subst w
  exact List.mem_append_left _ (List.mem_range.mpr (by decide))

theorem scalarCompute_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (scalarComputeProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 := by
  intro w hw
  rw [scalarComputeProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · rw [modularWires_seq] at hw
    rcases hw with hw | hw
    · exact root_support hw
    · exact initializedScalar_support P Q hP hQ hrP hrQ hw
  · exact root_support hw

theorem scalarCompute_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (scalarComputeProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (scalarComputeProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (scalarCompute_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

private theorem root_wrap_T (body : AdaptiveCircuit) :
    (((AdaptiveCircuit.unitary [.X 836] .done).seq body).seq (.unitary [.X 836] .done)).tCount=body.tCount := by
  have ht (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  rw [ht,ht]
  have hz : (AdaptiveCircuit.unitary [.X 836] .done).tCount=0 := rfl
  simp only [hz,Nat.zero_add,Nat.add_zero]
private theorem root_wrap_M (body : AdaptiveCircuit) :
    (((AdaptiveCircuit.unitary [.X 836] .done).seq body).seq (.unitary [.X 836] .done)).measurementCount=body.measurementCount := by
  rw [modularMeasurements_seq,modularMeasurements_seq]
  simp only [AdaptiveCircuit.measurementCount,Nat.zero_add,Nat.add_zero]

theorem scalarCompute_tCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (scalarComputeProgram P Q hP hQ hrP hrQ).tCount=
      (scalarWindowsProgram P Q hP hQ hrP hrQ).tCount :=
  (root_wrap_T _).trans (initializedScalar_tCount P Q hP hQ hrP hrQ)
theorem scalarCompute_measurementCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (scalarComputeProgram P Q hP hQ hrP hrQ).measurementCount=
      (scalarWindowsProgram P Q hP hQ hrP hrQ).measurementCount :=
  (root_wrap_M _).trans (initializedScalar_measurementCount P Q hP hQ hrP hrQ)

private def inputHadamards (ws : List Wire) : Circuit := ws.map Gate.H
private def inputUniform : List Wire → BasisState → State
  | [], s => ket s
  | w::ws, s => (((Real.sqrt 2)⁻¹:ℝ):ℂ) • inputUniform ws (s[w ↦ false])+
      (((Real.sqrt 2)⁻¹:ℝ):ℂ) • inputUniform ws (s[w ↦ true])
private theorem inputHadamards_ket (ws : List Wire) (hn : ws.Nodup) (s : BasisState)
    (hz : Clean ws s) : Quantum.run (inputHadamards ws) (ket s)=inputUniform ws s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    have hn' := List.nodup_cons.mp hn
    have hc (b : Bool) : Clean ws (s[w ↦ b]) := by
      intro q hq
      rw [upd_other _ _ _ (by intro he; subst q; exact hn'.1 hq)]
      exact hz q (List.mem_cons_of_mem _ hq)
    simp only [inputHadamards,List.map_cons,Quantum.run_cons,Quantum.applyGate_H_ket,
      hz w (List.mem_cons_self),Bool.false_eq_true,if_false,mul_one,map_add,map_smul]
    dsimp only [inputHadamards] at ih
    rw [ih hn'.2 _ (hc false),ih hn'.2 _ (hc true)]
    rfl
private theorem supported_add (Valid : BasisState → Prop) (a b : State)
    (ha : SupportedOn Valid a) (hb : SupportedOn Valid b) : SupportedOn Valid (a+b) := by
  intro s hs
  by_cases hz : a s=0
  · apply hb s
    intro h
    exact hs (by simp [hz,h])
  · exact ha s hz
private theorem supported_smul (Valid : BasisState → Prop) (c : ℂ) (a : State)
    (ha : SupportedOn Valid a) : SupportedOn Valid (c • a) := by
  intro s hs
  apply ha s
  intro h
  exact hs (by simp [h])
private theorem inputUniform_supported (Valid : BasisState → Prop) (ws : List Wire)
    (hup : ∀ w∈ws, ∀ s, Valid s → ∀ b, Valid (s[w ↦ b])) (s : BasisState) (hs : Valid s) :
    SupportedOn Valid (inputUniform ws s) := by
  induction ws generalizing s with
  | nil => exact supportedOn_ket _ s hs
  | cons w ws ih =>
    apply supported_add
    · apply supported_smul
      exact ih (by intro q hq; exact hup q (List.mem_cons_of_mem _ hq)) _ (hup w (List.mem_cons_self) s hs false)
    · apply supported_smul
      exact ih (by intro q hq; exact hup q (List.mem_cons_of_mem _ hq)) _ (hup w (List.mem_cons_self) s hs true)

def scalarPhaseWires : List Wire := List.range' 855 257++List.range' 1127 257
private theorem scalarPhaseWires_nodup : scalarPhaseWires.Nodup := by decide +kernel
private theorem phase_update_ready (w : Wire) (hw : w∈scalarPhaseWires) (s : BasisState)
    (hs : ScalarComputeValid s) (b : Bool) : ScalarComputeValid (s[w ↦ b]) := by
  have hw' := hw
  simp only [scalarPhaseWires,List.mem_append,List.mem_range'_1] at hw'
  refine ⟨?_,?_,?_⟩
  · intro q hq
    rw [upd_other _ _ _ (by dsimp only [Wire] at *; omega)]
    exact hs.1 q hq
  · have he : wireValues (List.range' (windowBankStart 0+257) 15) (s[w ↦ b])=
        wireValues (List.range' (windowBankStart 0+257) 15) s := by
      apply List.map_congr_left
      intro q hq
      apply upd_other
      simp only [List.mem_range'_1,windowBankStart] at hq
      dsimp only [Wire] at *; omega
    exact he.trans hs.2.1
  · have he : wireValues (List.range' (windowBankStart 17+257) 15) (s[w ↦ b])=
        wireValues (List.range' (windowBankStart 17+257) 15) s := by
      apply List.map_congr_left
      intro q hq
      apply upd_other
      simp only [List.mem_range'_1,windowBankStart] at hq
      dsimp only [Wire] at *; omega
    exact he.trans hs.2.2

def scalarPhasePrepare : Circuit := inputHadamards scalarPhaseWires

theorem scalarPhasePrepare_supported (s : BasisState) (hs : ScalarComputeValid s)
    (hz : Clean scalarPhaseWires s) :
    SupportedOn ScalarComputeValid (Quantum.run scalarPhasePrepare (ket s)) := by
  rw [scalarPhasePrepare,inputHadamards_ket scalarPhaseWires scalarPhaseWires_nodup s hz]
  exact inputUniform_supported ScalarComputeValid _ phase_update_ready s hs

def ScalarPhaseInitial (s : BasisState) : Prop := ScalarComputeValid s ∧ Clean scalarPhaseWires s

def preparedScalarProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary scalarPhasePrepare .done).seq (scalarComputeProgram P Q hP hQ hrP hrQ)

theorem preparedScalar_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (preparedScalarProgram P Q hP hQ hrP hrQ)
      ((Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)).comp (Quantum.run scalarPhasePrepare))
      ScalarPhaseInitial :=
  (CoherentlyImplementsOn.unitary scalarPhasePrepare ScalarPhaseInitial).seq
    (scalarCompute_coherent P Q hP hQ hrP hrQ) (fun s hs => scalarPhasePrepare_supported s hs.1 hs.2)

theorem scalarPhasePrepare_support : circuitWires scalarPhasePrepare ⊆ scalarPhaseWires := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  exact hw ▸ hv

theorem preparedScalar_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (preparedScalarProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 := by
  intro w hw
  rw [preparedScalarProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · simp only [AdaptiveCircuit.wires,List.append_nil] at hw
    have h := scalarPhasePrepare_support hw
    apply List.mem_append_right
    simp only [scalarPhaseWires,List.mem_append,List.mem_range'_1] at h
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *; omega
  · exact scalarCompute_support P Q hP hQ hrP hrQ hw

theorem preparedScalar_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (preparedScalarProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (preparedScalarProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (preparedScalar_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

theorem scalarPhasePrepare_length : scalarPhasePrepare.length=514 := by
  simp only [scalarPhasePrepare,inputHadamards,List.length_map,scalarPhaseWires,
    List.length_append,List.length_range']
private theorem hadamard_T (ws : List Wire) : tCount (inputHadamards ws)=0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simpa only [inputHadamards,List.map_cons,tCount,List.sum_cons,tCost,Nat.zero_add] using ih

theorem scalarPhasePrepare_tCount : tCount scalarPhasePrepare=0 := hadamard_T _
private theorem unitary_T (c : Circuit) : (AdaptiveCircuit.unitary c .done).tCount=tCount c := by
  change tCount c+0=tCount c
  exact Nat.add_zero _
private theorem phase_prefix_T (body : AdaptiveCircuit) :
    ((AdaptiveCircuit.unitary scalarPhasePrepare .done).seq body).tCount=body.tCount := by
  have h := modularGateCount_seq tCost (AdaptiveCircuit.unitary scalarPhasePrepare .done) body
  have hz : (AdaptiveCircuit.unitary scalarPhasePrepare .done).tCount=0 := by
    rw [unitary_T,scalarPhasePrepare_tCount]
  simpa only [gidneyGateCount_tCount,hz,Nat.zero_add] using h
private theorem phase_prefix_M (body : AdaptiveCircuit) :
    ((AdaptiveCircuit.unitary scalarPhasePrepare .done).seq body).measurementCount=body.measurementCount := by
  rw [modularMeasurements_seq]
  exact Nat.zero_add _

theorem preparedScalar_tCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (preparedScalarProgram P Q hP hQ hrP hrQ).tCount=
      (scalarWindowsProgram P Q hP hQ hrP hrQ).tCount :=
  (phase_prefix_T _).trans (scalarCompute_tCount P Q hP hQ hrP hrQ)
theorem preparedScalar_measurementCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (preparedScalarProgram P Q hP hQ hrP hrQ).measurementCount=
      (scalarWindowsProgram P Q hP hQ hrP hrQ).measurementCount :=
  (phase_prefix_M _).trans (scalarCompute_measurementCount P Q hP hQ hrP hrQ)

end
end ShorECDLP.Paper2607_13816
