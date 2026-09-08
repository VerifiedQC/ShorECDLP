import ShorECDLP.Submission.«2607_13816».EEA.Preprocess

/-! # Resources of the concrete preprocessing prefix -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
set_option maxRecDepth 10000

private theorem preprocess_input_cons :
    (List.range' 266 256).reverse = 521 :: (List.range' 266 255).reverse := by decide

private theorem preprocess_add_metrics (constant : List Bool) (hbits : constant.length = 255)
    (cx : Nat)
    (href : gidneyCnotCount (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      (true :: constant) 2 560 561 562) = cx) :
    let ac := controlledGidneyAddConst (List.range' 266 256).reverse (List.range' 4 255)
      (true :: constant) 2 560 561 562
    gidneyToffoliCount ac = 764 ∧ gidneyCnotCount ac = cx ∧
      ac.tCount = 5348 ∧ ac.measurementCount = 255 := by
  have ht := controlledGidneyAddConst_toffoli_exact 521 4 2 560 561 562
    (List.range' 266 255).reverse (List.range' 5 254) constant (by simp [hbits]) (by simp)
  have htc := controlledGidneyAddConst_tCount_exact 521 4 2 560 561 562
    (List.range' 266 255).reverse (List.range' 5 254) constant (by simp [hbits]) (by simp)
  have hc := controlledGidneyAddConst_cnot_congr 521 4 2 560 561 562 4 260 2 560 561 562
    (List.range' 266 255).reverse (List.range' 5 254) (List.range' 5 255) (List.range' 261 254)
    constant (by simp [hbits]) (by simp) (by simp [hbits]) (by simp)
  have hm := controlledGidneyAddConst_measurementCount (List.range' 266 256).reverse (List.range' 4 255)
    (true :: constant) 2 560 561 562 (by simp [hbits]) (by simp)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [preprocess_input_cons]; simpa using ht
  · rw [preprocess_input_cons]; exact hc.trans href
  · rw [preprocess_input_cons]; simpa using htc
  · simpa using hm

private theorem preprocess_increment_metrics :
    let ac := controlledGidneyAddConst (List.range' 266 256).reverse (List.range' 4 255)
      ((List.range 256).map (Nat.testBit 1)) 2 560 561 562
    gidneyToffoliCount ac = 764 ∧ gidneyCnotCount ac = 1284 ∧
      ac.tCount = 5348 ∧ ac.measurementCount = 255 := by
  have hb : ((List.range 256).map (Nat.testBit 1)) =
      true :: (List.range' 1 255).map (Nat.testBit 1) := by decide
  have hr := (secp256k1Increment_counts 2 560 561 562).2.1
  dsimp only at hr ⊢
  rw [hb] at hr ⊢
  exact preprocess_add_metrics _ (by simp) _ hr

private theorem preprocess_modulus_metrics :
    let ac := controlledGidneyAddConst (List.range' 266 256).reverse (List.range' 4 255)
      (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) 2 560 561 562
    gidneyToffoliCount ac = 764 ∧ gidneyCnotCount ac = 3765 ∧
      ac.tCount = 5348 ∧ ac.measurementCount = 255 := by
  have hb : constantBits 256 (2 ^ 256 - 2 ^ 32 - 977) =
      true :: (List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)) := by decide
  have hr := (secp256k1ModulusAdd_counts 2 560 561 562).2.1
  have hm : secp256k1ModulusBits = constantBits 256 (2 ^ 256 - 2 ^ 32 - 977) := by decide
  dsimp only at hr ⊢
  rw [hm,hb] at hr
  rw [hb]
  exact preprocess_add_metrics _ (by simp) _ hr

private theorem preprocess_length_table :
    let cases := lengthInitializeCases (List.range' 266 256) (List.range' 549 9).length
    (cases.map (fun row => 2 * mcxVChainToffoliCost row.1.length)).sum = 131068 ∧
    (cases.map (fun row => 2 * mcxVChainCnotCost row.1.length + lowBitCount (List.range' 549 9).length row.2.2)).sum = 1035 ∧
    (cases.map (fun row => 14 * mcxVChainToffoliCost row.1.length)).sum = 917476 := by
  simp only [lengthInitializeCases, List.map_append, List.map_map, Function.comp_def,
    List.length_take, List.length_range']
  decide

attribute [local irreducible] lengthInitialize xorConstant

private theorem preprocess_xor_prefix (a b : List Wire) (v w : Nat) (g : Circuit) :
    eeaToffoliCount (xorConstant a v ++ xorConstant b w ++ g) = eeaToffoliCount g ∧
    eeaCnotCount (xorConstant a v ++ xorConstant b w ++ g) = eeaCnotCount g ∧
    ShorECDLP.tCount (xorConstant a v ++ xorConstant b w ++ g) = ShorECDLP.tCount g := by
  simp only [eeaToffoliCount_append, eeaCnotCount_append, tCount_append,
    xorConstant_toffoliCount, xorConstant_cnotCount, xorConstant_tCount, zero_add, and_self]

private theorem preprocess_length_metrics :
    eeaToffoliCount eeaLengthSetup = 131068 ∧ eeaCnotCount eeaLengthSetup = 1035 ∧
      ShorECDLP.tCount eeaLengthSetup = 917476 := by
  have h := lengthInitialize_counts (List.range' 266 256) (List.range' 549 9) 558
    ((List.range' 7 256).reverse.take 254) (2 ^ 256 - 2 ^ 32 - 977) (by simp)
  have hc := preprocess_length_table
  have hdef : eeaLengthSetup = xorConstant (List.range' 531 9) 511 ++
      xorConstant (List.range' 540 9) 511 ++
      lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
        ((List.range' 7 256).reverse.take 254) (2 ^ 256 - 2 ^ 32 - 977) := rfl
  have hp := preprocess_xor_prefix (List.range' 531 9) (List.range' 540 9) 511 511
    (lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
      ((List.range' 7 256).reverse.take 254) (2 ^ 256 - 2 ^ 32 - 977))
  exact ⟨(congrArg eeaToffoliCount hdef).trans (hp.1.trans (h.1.trans hc.1)),
    (congrArg eeaCnotCount hdef).trans (hp.2.1.trans (h.2.1.trans hc.2.1)),
    (congrArg ShorECDLP.tCount hdef).trans (hp.2.2.trans (h.2.2.trans hc.2.2))⟩

private theorem preprocess_seq_ccx (a b : AdaptiveCircuit) :
    gidneyToffoliCount (a.seq b) = gidneyToffoliCount a + gidneyToffoliCount b :=
  modularGateCount_seq _ a b
private theorem preprocess_seq_cx (a b : AdaptiveCircuit) :
    gidneyCnotCount (a.seq b) = gidneyCnotCount a + gidneyCnotCount b :=
  modularGateCount_seq _ a b
private theorem preprocess_seq_t (a b : AdaptiveCircuit) :
    (a.seq b).tCount = a.tCount + b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
private theorem preprocess_unitary_ccx (g : Circuit) (a : AdaptiveCircuit) :
    gidneyToffoliCount (.unitary g a) = eeaToffoliCount g + gidneyToffoliCount a := rfl
private theorem preprocess_unitary_cx (g : Circuit) (a : AdaptiveCircuit) :
    gidneyCnotCount (.unitary g a) = eeaCnotCount g + gidneyCnotCount a := rfl

private theorem preprocess_compare_metrics :
    let ac := gidneyCompareGE (List.range' 266 256).reverse (List.range' 4 256)
      ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1) 560 561 562 2
    gidneyToffoliCount ac = 767 ∧ gidneyCnotCount ac = 1537 ∧
      ac.tCount = 5369 ∧ ac.measurementCount = 256 := by
  have h := gidneyCompareGE_metrics 521 (List.range' 266 255).reverse (List.range' 4 256)
    ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1) 560 561 562 2 (by simp) (by decide) (by simp)
  dsimp only
  rw [preprocess_input_cons]
  exact ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2.1,
    by simpa using h.2.2.2.1⟩

private theorem preprocess_flip_metrics :
    eeaToffoliCount (((List.range' 266 256).reverse.map (Gate.CX 2))) = 0 ∧
    eeaCnotCount (((List.range' 266 256).reverse.map (Gate.CX 2))) = 256 ∧
    ShorECDLP.tCount (((List.range' 266 256).reverse.map (Gate.CX 2))) = 0 := by decide

attribute [local irreducible] controlledGidneyAddConst gidneyCompareGE

private theorem preprocess_center_algebra (cmp inc modulus : AdaptiveCircuit) (flip : Circuit)
    (hc : gidneyToffoliCount cmp = 767 ∧ gidneyCnotCount cmp = 1537 ∧
      cmp.tCount = 5369 ∧ cmp.measurementCount = 256)
    (hi : gidneyToffoliCount inc = 764 ∧ gidneyCnotCount inc = 1284 ∧
      inc.tCount = 5348 ∧ inc.measurementCount = 255)
    (hm : gidneyToffoliCount modulus = 764 ∧ gidneyCnotCount modulus = 3765 ∧
      modulus.tCount = 5348 ∧ modulus.measurementCount = 255)
    (hf : eeaToffoliCount flip = 0 ∧ eeaCnotCount flip = 256 ∧ ShorECDLP.tCount flip = 0) :
    let ac := cmp.seq (.unitary flip (inc.seq modulus))
    gidneyToffoliCount ac = 2295 ∧ gidneyCnotCount ac = 6842 ∧
      ac.tCount = 16065 ∧ ac.measurementCount = 766 := by
  simp only [preprocess_seq_ccx, preprocess_seq_cx, preprocess_seq_t, modularMeasurements_seq,
    preprocess_unitary_ccx, preprocess_unitary_cx, AdaptiveCircuit.tCount, AdaptiveCircuit.measurementCount,
    hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2,
    hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, hf.1, hf.2.1, hf.2.2]
  decide

private theorem preprocess_center_eq : eeaCenter (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977) 560 561 562 2 =
  (gidneyCompareGE (List.range' 266 256).reverse (List.range' 4 256)
    ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1) 560 561 562 2).seq
    (.unitary ((List.range' 266 256).reverse.map (Gate.CX 2))
      ((controlledGidneyAddConst (List.range' 266 256).reverse (List.range' 4 255)
        ((List.range 256).map (Nat.testBit 1)) 2 560 561 562).seq
        (controlledGidneyAddConst (List.range' 266 256).reverse (List.range' 4 255)
          (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) 2 560 561 562))) := by
  have htake : (List.range' 4 256).take 255 = List.range' 4 255 := by decide
  simp only [eeaCenter, controlledConstMinus, List.length_reverse, List.length_range',
    show 256-1 = 255 from rfl, htake]
  rfl

private theorem preprocess_center_metrics :
    let ac := eeaCenter (List.range' 266 256).reverse (List.range' 4 256)
      (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977) 560 561 562 2
    gidneyToffoliCount ac = 2295 ∧ gidneyCnotCount ac = 6842 ∧
      ac.tCount = 16065 ∧ ac.measurementCount = 766 := by
  have hdef := preprocess_center_eq
  have h := preprocess_center_algebra _ _ _ _ preprocess_compare_metrics
    preprocess_increment_metrics preprocess_modulus_metrics preprocess_flip_metrics
  exact ⟨(congrArg gidneyToffoliCount hdef).trans h.1,
    (congrArg gidneyCnotCount hdef).trans h.2.1,
    (congrArg AdaptiveCircuit.tCount hdef).trans h.2.2.1,
    (congrArg AdaptiveCircuit.measurementCount hdef).trans h.2.2.2⟩

attribute [local irreducible] eeaCenter eeaLengthSetup workRegistersPrepare

private theorem preprocess_full_algebra (prepare length : Circuit) (center : AdaptiveCircuit)
    (hp : eeaToffoliCount prepare = 0 ∧ eeaCnotCount prepare = 390 ∧ ShorECDLP.tCount prepare = 0)
    (hc : gidneyToffoliCount center = 2295 ∧ gidneyCnotCount center = 6842 ∧
      center.tCount = 16065 ∧ center.measurementCount = 766)
    (hl : eeaToffoliCount length = 131068 ∧ eeaCnotCount length = 1035 ∧
      ShorECDLP.tCount length = 917476) :
    let ac := AdaptiveCircuit.unitary prepare (center.seq (.unitary length .done))
    gidneyToffoliCount ac = 133363 ∧ gidneyCnotCount ac = 8267 ∧
      ac.tCount = 933541 ∧ ac.measurementCount = 766 := by
  simp only [preprocess_unitary_ccx, preprocess_unitary_cx,
    preprocess_seq_ccx, preprocess_seq_cx, preprocess_seq_t, modularMeasurements_seq,
    AdaptiveCircuit.tCount, AdaptiveCircuit.measurementCount,
    hp.1, hp.2.1, hp.2.2, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hl.1, hl.2.1, hl.2.2]
  decide

private theorem preprocess_add_support (constant : List Bool) (hlen : constant.length = 255)
    (w : Wire) (hw : w ∈ (controlledGidneyAddConst (List.range' 266 256).reverse
      (List.range' 4 255) (true :: constant) 2 560 561 562).wires) : (w : Nat) < 580 := by
  rw [preprocess_input_cons] at hw
  have h := (controlledGidneyAddConst_wires 521 4 2 560 561 562
    (List.range' 266 255).reverse (List.range' 5 254) constant (by simp [hlen]) (by simp) w).mp hw
  simp at h
  rcases h with rfl | rfl | rfl | rfl | rfl | h | rfl | h <;> first | decide | exact Nat.lt_trans h.2 (by decide)

private theorem preprocess_center_support (w : Wire)
    (hw : w ∈ (eeaCenter (List.range' 266 256).reverse (List.range' 4 256)
      (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977) 560 561 562 2).wires) :
    (w : Nat) < 580 := by
  rw [preprocess_center_eq] at hw
  simp only [modularWires_seq, AdaptiveCircuit.wires, List.mem_append] at hw
  rcases hw with hc | hf | hi | hm
  · have h := gidneyCompareGE_metrics 521 (List.range' 266 255).reverse (List.range' 4 256)
      ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1) 560 561 562 2 (by simp) (by decide) (by simp)
    rw [preprocess_input_cons] at hc
    have hs := (h.2.2.2.2 w).mp hc
    simp at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | hs | hs <;> first | decide | exact Nat.lt_trans hs.2 (by decide)
  · obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · decide
    · simp at ha; exact Nat.lt_trans ha.2 (by decide)
  · have he : ((List.range 256).map (Nat.testBit 1)) =
        true :: (List.range' 1 255).map (Nat.testBit 1) := by decide
    rw [he] at hi
    exact preprocess_add_support _ (by simp) w hi
  · have he : constantBits 256 (2 ^ 256 - 2 ^ 32 - 977) =
        true :: (List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)) := by decide
    rw [he] at hm
    exact preprocess_add_support _ (by simp) w hm

private theorem preprocess_classical_support (g : Circuit)
    (h : PaperCircuitUsesOnly (List.range 580) g) (w : Wire) (hw : w ∈ circuitWires g) : (w : Nat) < 580 := by
  obtain ⟨gate,hg,hw⟩ := List.mem_flatMap.mp hw
  exact List.mem_range.mp (h gate hg w hw)

/-- The complete forward preprocessing prefix stays within the existing allocation. -/
theorem eeaPreprocess_qubitCount : eeaPreprocess.qubitCount ≤ 580 := by
  have hp : PaperCircuitUsesOnly (List.range 580) workRegistersPrepare :=
    workRegistersPrepare_usesOnly.mono (by intro w hw; simp at hw ⊢; omega)
  have hsub : eeaPreprocess.wires.dedup.toFinset ⊆ (List.range 580).toFinset := by
    intro w hw
    simp only [List.mem_toFinset, List.mem_dedup] at hw ⊢
    change w ∈ (AdaptiveCircuit.unitary workRegistersPrepare
      ((eeaCenter (List.range' 266 256).reverse (List.range' 4 256)
        (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977)
        560 561 562 2).seq (.unitary eeaLengthSetup .done))).wires at hw
    simp only [AdaptiveCircuit.wires, modularWires_seq, List.mem_append, List.not_mem_nil, or_false] at hw
    apply List.mem_range.mpr
    rcases hw with hw | hw | hw
    · exact preprocess_classical_support _ hp w hw
    · exact preprocess_center_support w hw
    · exact preprocess_classical_support _ eeaLengthSetup_usesOnly w hw
  have hc := (Finset.card_le_card hsub).trans (List.toFinset_card_le (List.range 580))
  simpa only [AdaptiveCircuit.qubitCount, List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.length_range] using hc

/-- Exact aggregate costs of the same concrete preprocessing circuit whose
full measurement-branch semantics are proved in `eeaPreprocess_branch_correct`. -/
theorem eeaPreprocess_resources :
    eeaPreprocess.WellFormed ∧ gidneyToffoliCount eeaPreprocess = 133363 ∧
    gidneyCnotCount eeaPreprocess = 8267 ∧ eeaPreprocess.tCount = 933541 ∧
    eeaPreprocess.measurementCount = 766 ∧ eeaPreprocess.qubitCount ≤ 580 := by
  have hp := workRegistersPrepare_resources
  have h := preprocess_full_algebra workRegistersPrepare eeaLengthSetup _
    ⟨hp.2.2.2.1, hp.2.2.1, hp.2.2.2.2⟩ preprocess_center_metrics preprocess_length_metrics
  have hdef : eeaPreprocess = .unitary workRegistersPrepare
    ((eeaCenter (List.range' 266 256).reverse (List.range' 4 256)
      (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977)
      560 561 562 2).seq (.unitary eeaLengthSetup .done)) := rfl
  exact ⟨eeaPreprocess_wellFormed, (congrArg gidneyToffoliCount hdef).trans h.1,
    (congrArg gidneyCnotCount hdef).trans h.2.1,
    (congrArg AdaptiveCircuit.tCount hdef).trans h.2.2.1,
    (congrArg AdaptiveCircuit.measurementCount hdef).trans h.2.2.2, eeaPreprocess_qubitCount⟩

/-- Same-circuit operational and aggregate-resource certificate for the prefix. -/
theorem eeaPreprocess_correct_resources (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (branch : InstrumentBranch) (hb : branch ∈ eeaPreprocess.run) :
    branch.kraus (ket state) = registerXResetMagnitude branch.history.length •
      ket (eeaPreprocessIdealState state) ∧
    eeaPreprocess.WellFormed ∧ gidneyToffoliCount eeaPreprocess = 133363 ∧
    gidneyCnotCount eeaPreprocess = 8267 ∧ eeaPreprocess.tCount = 933541 ∧
    eeaPreprocess.measurementCount = 766 ∧ eeaPreprocess.qubitCount ≤ 580 :=
  ⟨eeaPreprocess_branch_correct state hclean branch hb, eeaPreprocess_resources⟩

end
end ShorECDLP.Paper2607_13816
