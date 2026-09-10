import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveWrapper
import ShorECDLP.Submission.«2607_13816».EEA.AdaptivePhysicalSupport
/-! Complete EEA wrapper support, including the actual borrowed banks and all adaptive branches. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem constMinus256_wires (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hi : input.length=256) (hd : dirty.length=255) (hb : bits.length=255) :
    (controlledConstMinus input dirty (true::bits) q c r t).wires ⊆
      [q,c,r,t] ++ input ++ dirty := by
  have hone : (List.range input.length).map (Nat.testBit 1) = true :: List.replicate 255 false := by
    rw [hi]; decide +kernel
  cases input with
  | nil => simp at hi
  | cons a rest =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      have hinc := controlledGidneyAddConst_wires a d q c r t rest ds (List.replicate 255 false)
        (by simp only [List.length_cons] at hi hd; simp only [List.length_replicate]; omega) (by simp only [List.length_cons] at hi hd; omega)
      have hmod := controlledGidneyAddConst_wires a d q c r t rest ds bits (by simp only [List.length_cons] at hi; omega) (by simp only [List.length_cons] at hi hd; omega)
      intro w hw
      change w ∈ (AdaptiveCircuit.unitary ((a::rest).map (Gate.CX q))
        ((controlledGidneyAddConst (a::rest) (d::ds) ((List.range (a::rest).length).map (Nat.testBit 1)) q c r t).seq
          (controlledGidneyAddConst (a::rest) (d::ds) (true::bits) q c r t))).wires at hw
      rw [hone] at hw
      simp only [AdaptiveCircuit.wires,List.mem_append,modularWires_seq,hinc,hmod] at hw
      rcases hw with hw | hw | hw
      · obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
        obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
        simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl | rfl
        · simp
        · simp only [List.mem_append]; exact Or.inl (Or.inr hv)
      · simpa only [List.mem_append] using hw
      · simpa only [List.mem_append] using hw
private theorem compare256_wires (input dirty : List Wire) (p : Nat) (c r t f : Wire)
    (hi : input.length=256) (hd : dirty.length=256) (hp0 : 0<p) (hp : p<2^256) :
    (gidneyCompareGE input dirty p c r t f).wires ⊆ [c,r,t,f] ++ input ++ dirty := by
  cases input with
  | nil => simp at hi
  | cons a rest =>
    have h := gidneyCompareGE_metrics a rest dirty p c r t f
      (by omega) hp0 (by simpa only [hi] using hp)
    intro w hw
    exact (h.2.2.2.2 w).mp hw
private theorem center256_wires (input dirty : List Wire) (bits : List Bool) (p : Nat)
    (c r t iter : Wire) (hi : input.length=256) (hd : dirty.length=256)
    (hb : bits.length=255) (hp0 : 0<p/2+1) (hp : p/2+1<2^256) :
    (eeaCenter input dirty (true::bits) p c r t iter).wires ⊆ [iter,c,r,t] ++ input ++ dirty := by
  have hc := compare256_wires input dirty (p/2+1) c r t iter hi hd hp0 hp
  have hm := constMinus256_wires input (dirty.take (input.length-1)) bits iter c r t hi
    (by rw [List.length_take,hi,hd]; decide) hb
  intro w hw
  simp only [eeaCenter,modularWires_seq] at hw
  rcases hw with hw | hw
  · have h := hc hw
    simpa only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc,or_comm,or_left_comm] using h
  · have h := hm hw
    simp only [List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_take h)
private theorem uncenter256_wires (input dirty : List Wire) (bits : List Bool) (p : Nat)
    (c r t iter : Wire) (hi : input.length=256) (hd : dirty.length=256)
    (hb : bits.length=255) (hp0 : 0<p/2+1) (hp : p/2+1<2^256) :
    (eeaUncenter input dirty (true::bits) p c r t iter).wires ⊆ [iter,c,r,t] ++ input ++ dirty := by
  intro w hw
  apply center256_wires input dirty bits p c r t iter hi hd hb hp0 hp
  simpa only [eeaUncenter,eeaCenter,modularWires_seq,or_comm] using hw
private theorem support580 (ws : List Wire) (h : ws.all (fun w => decide (w<580))=true) :
    ws ⊆ List.range 580 := by
  intro w hw
  exact List.mem_range.mpr (of_decide_eq_true ((List.all_eq_true.mp h) w hw))
private theorem unitary_wires_support (c : Circuit) (h : PaperCircuitUsesOnly (List.range 580) c) :
    circuitWires c ⊆ List.range 580 := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  exact h g hg w hw

private def modulusTail : List Bool := (List.range' 1 255).map (Nat.testBit (2^256-2^32-977))
private theorem modulus_split : constantBits 256 (2^256-2^32-977) = true::modulusTail := by decide +kernel
private theorem modulus_tail_length : modulusTail.length=255 := by simp only [modulusTail,List.length_map,List.length_range']
private theorem center_production_support :
    (eeaCenter (List.range' 266 256).reverse (List.range' 4 256)
      (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2).wires ⊆ List.range 580 := by
  rw [modulus_split]
  exact (center256_wires _ _ _ _ _ _ _ _ (by simp) (by simp) modulus_tail_length
    (by decide +kernel) (by decide +kernel)).trans (support580 _ (by decide +kernel))
private theorem uncenter_production_support :
    (eeaUncenter (List.range' 266 256).reverse (List.range' 4 256)
      (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2).wires ⊆ List.range 580 := by
  rw [modulus_split]
  exact (uncenter256_wires _ _ _ _ _ _ _ _ (by simp) (by simp) modulus_tail_length
    (by decide +kernel) (by decide +kernel)).trans (support580 _ (by decide +kernel))
private theorem lengthUndo_support : circuitWires eeaLengthUndo ⊆ List.range 580 := by
  have h := unitary_wires_support eeaLengthSetup eeaLengthSetup_usesOnly
  intro w hw
  apply h
  simpa only [eeaLengthUndo,eeaLengthSetup,circuitWires,List.flatMap_append,List.mem_append,
    or_assoc,or_comm,or_left_comm] using hw

theorem eeaPreprocess_wires_subset : eeaPreprocess.wires ⊆ List.range 580 := by
  have hp := unitary_wires_support workRegistersPrepare
    (workRegistersPrepare_usesOnly.mono (fun _ hw => support580 _ (by decide +kernel) hw))
  have hc := center_production_support
  have hl := unitary_wires_support eeaLengthSetup eeaLengthSetup_usesOnly
  intro w hw
  simp only [eeaPreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,
    List.not_mem_nil,or_false] at hw
  rcases hw with hw | hw | hw
  · exact hp hw
  · exact hc hw
  · exact hl hw

theorem eeaUnpreprocess_wires_subset : eeaUnpreprocess.wires ⊆ List.range 580 := by
  have hr := unitary_wires_support workRegistersRestore
    (workRegistersRestore_usesOnly.mono (fun _ hw => support580 _ (by decide +kernel) hw))
  have hc := uncenter_production_support
  intro w hw
  simp only [eeaUnpreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,
    List.not_mem_nil,or_false] at hw
  rcases hw with hw | hw | hw
  · exact lengthUndo_support hw
  · exact hc hw
  · exact hr hw

theorem secp256k1EEAParityCorrection_wires_subset : secp256k1EEAParityCorrection.wires ⊆ List.range 580 := by
  have hm : (controlledConstMinus (List.range' 263 256) (List.range' 4 255) secp256k1ModulusBits 2 560 561 562).wires ⊆ List.range 580 := by
    rw [show secp256k1ModulusBits=true::modulusTail by decide +kernel]
    exact (constMinus256_wires _ _ _ _ _ _ _ (by simp) (by simp) modulus_tail_length).trans
      (support580 _ (by decide +kernel))
  intro w hw
  simp only [secp256k1EEAParityCorrection,eeaParityCorrection,AdaptiveCircuit.wires,
    modularWires_seq,List.mem_append,List.not_mem_nil,or_false] at hw
  rcases hw with hw | hw | hw
  · have hw2 : w=2 := by simpa [circuitWires,gateWires] using hw
    subst w
    exact List.mem_range.mpr (by decide)
  · exact hm hw
  · have hw2 : w=2 := by simpa [circuitWires,gateWires] using hw
    subst w
    exact List.mem_range.mpr (by decide)

private theorem epoch_wires_support : circuitWires terminalEpochCompression ⊆ List.range 580 :=
  support580 _ (by decide +kernel)
private theorem terminal_clear_wires_support : circuitWires terminalWork1Clear ⊆ List.range 580 :=
  unitary_wires_support _ ((xorConstant_usesOnly _ _).mono
    (fun _ hw => support580 _ (by decide +kernel) hw))

attribute [local irreducible] eeaPreprocess eeaUnpreprocess secp256k1EEAForwardAdaptive
  secp256k1EEAReverseAdaptive secp256k1EEAParityCorrection canonicalWork2Rotation
  canonicalWork2InverseRotation terminalEpochCompression terminalWork1Clear

/-- Complete forward wrapper, including preprocessing and every measurement correction. -/
theorem secp256k1EEAForwardWrapper_wires_subset : secp256k1EEAForwardWrapper.wires ⊆ List.range 580 := by
  have hp := eeaPreprocess_wires_subset
  have hs := secp256k1EEAForwardAdaptive_wires_subset
  have hc := unitary_wires_support _ canonicalWork2Rotation_usesOnly
  have he := epoch_wires_support
  have hpar := secp256k1EEAParityCorrection_wires_subset
  have ht := terminal_clear_wires_support
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hp hs hc he hpar ht
  intro w hw
  simp only [secp256k1EEAForwardWrapper,modularWires_seq,AdaptiveCircuit.wires,
    circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw
  aesop

/-- The literal reverse wrapper reuses the same physical allocation in all branches. -/
theorem secp256k1EEAReverseWrapper_wires_subset : secp256k1EEAReverseWrapper.wires ⊆ List.range 580 := by
  have hp := eeaUnpreprocess_wires_subset
  have hs := secp256k1EEAReverseAdaptive_wires_subset
  have hc := unitary_wires_support _ canonicalWork2InverseRotation_usesOnly
  have he := epoch_wires_support
  have hpar := secp256k1EEAParityCorrection_wires_subset
  have ht := terminal_clear_wires_support
  simp only [List.subset_def,circuitWires,List.mem_flatMap] at hp hs hc he hpar ht
  intro w hw
  simp only [secp256k1EEAReverseWrapper,secp256k1EEAReversePostprocessing,
    modularWires_seq,AdaptiveCircuit.wires,circuitWires,List.flatMap_append,
    List.mem_append,List.not_mem_nil,or_false] at hw
  aesop
private theorem adaptive_count580 (p : AdaptiveCircuit) (h : p.wires ⊆ List.range 580) : p.qubitCount ≤ 580 := by
  have hs : p.wires.dedup.toFinset ⊆ (List.range 580).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h (by simpa using hw))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range (n := 580))] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc

theorem secp256k1EEAForwardWrapper_qubitCount : secp256k1EEAForwardWrapper.qubitCount ≤ 580 :=
  adaptive_count580 _ secp256k1EEAForwardWrapper_wires_subset

theorem secp256k1EEAReverseWrapper_qubitCount : secp256k1EEAReverseWrapper.qubitCount ≤ 580 :=
  adaptive_count580 _ secp256k1EEAReverseWrapper_wires_subset

end ShorECDLP.Paper2607_13816
