import ShorECDLP.Submission.«2607_13816».Window.StreamGateCounts
/-! A tighter support certificate for the unchanged streaming program.
The raw arithmetic avoids flags 837 and 838, but initial point lookup still uses
838 for infinity. Only 837 can be removed from the full allocation. This is an
upper bound of 854 distinct wires, not the paper's 835-wire construction. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq
private def sparseLookup : List Wire := List.range 837 ++ List.range' 839 16
private theorem core_sparse : List.range 837 ⊆ sparseLookup := List.subset_append_left _ _
private theorem bounded_banks (start : Nat) (hs : start+256≤837) :
    [836,559,560,561,558]++List.range' start 256++List.range' 7 256 ⊆ List.range 837 := by
  intro w hw
  simp at hw ⊢
  omega
private theorem point_negate_support : fig14Negate.wires ⊆ List.range 837 := by
  exact List.Subset.trans (controlledModularNegate256_wires_subset _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp)) (bounded_banks 263 (by decide))
private theorem point_square_support : fig14SquareSubtract.wires ⊆ List.range 837 := by
  have hc : secp256k1ReductionConstantBits=true::secp256k1ReductionConstantBits.tail := by decide +kernel
  have hm : constantBits 256 ShorECDLP.p=true::(constantBits 256 ShorECDLP.p).tail := by decide +kernel
  have hh := squareSubtract256_wires_subset (List.range' 263 256) (List.range' 580 256) (List.range' 7 256)
    secp256k1ReductionConstantBits.tail (constantBits 256 ShorECDLP.p).tail ShorECDLP.p
    836 558 559 561 562 560 (by simp) (by simp) (by simp) (by decide +kernel) (by simp)
    ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
  rw [←hc,←hm] at hh
  apply List.Subset.trans hh
  intro w hw
  simp at hw ⊢
  dsimp only [Wire] at *
  omega
private theorem lookup_modular256_support (table : Nat → Nat) (bits paths input acc : List Wire)
    (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) :
    (lookupModularAddProgram table bits paths input acc secp256k1ReductionConstantBits
      ShorECDLP.p q c r t f).wires ⊆ [q,c,r,t,f]++bits++paths++input++acc := by
  have hm (label : Nat) : tableWordMask input (table label) ⊆ input := tableBitsMask_subset _ _
  have hl := tableLookupProgram_support (fun label => tableWordMask input (table label)) bits paths input q hm
  have hb' : (controlledModularAdd input acc secp256k1ReductionConstantBits ShorECDLP.p q c r t f).wires ⊆
      [q,c,r,t,f]++input++acc := by
    have h := controlledModularAdd256_wires input acc (secp256k1ReductionConstantBits.tail) ShorECDLP.p
      q c r t f hi ha (by simp [secp256k1ReductionConstantBits])
      ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
    exact h
  intro w hw
  simp only [lookupModularAddProgram,modularWires_seq] at hw
  rcases hw with (hw | hw) | hw
  · have h := hl hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop
  · have h := hb' hw
    simp only [List.mem_append] at h ⊢
    aesop
  · have h := hl hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop

private theorem lookupX_sparse (table : Nat → Nat) : (fig14LookupX table).wires ⊆ sparseLookup := by
  have h := lookup_modular256_support table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 263 256) 836 559 560 561 558 (by simp) (by simp)
  intro w hw
  have hh := h hw
  simp only [pointLookupAddress,pointLookupPath,sparseLookup,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,List.mem_range'_1,List.mem_range] at hh ⊢
  dsimp only [Wire] at *
  omega
private theorem lookupY_sparse (table : Nat → Nat) : (fig14LookupY table).wires ⊆ sparseLookup := by
  have h := lookup_modular256_support table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) 836 559 560 561 558 (by simp) (by simp)
  intro w hw
  have hh := h hw
  simp only [pointLookupAddress,pointLookupPath,sparseLookup,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,List.mem_range'_1,List.mem_range] at hh ⊢
  dsimp only [Wire] at *
  omega
private theorem signed_neg_sparse :
    (negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558).wires ⊆ sparseLookup := by
  intro w hw
  have h := negativeControlledModularNegate_wires _ _ _ 854 559 560 561 558 hw
  simp only [List.mem_cons] at h
  rcases h with rfl | h
  · simp [sparseLookup]
  · have hh := controlledModularNegate256_wires_subset (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558 (by simp) (by simp) (constantBits_length _ _) h
    simp only [sparseLookup,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1,List.mem_range] at hh ⊢
    dsimp only [Wire] at *
    omega

private theorem signed_lookup_sparse (table : Nat → Nat) : (signedPointLookupY table).wires ⊆ sparseLookup := by
  intro w hw
  simp only [signedPointLookupY,signedLookupModularAddProgram,modularWires_seq,List.length_range'] at hw
  rcases hw with (hw | hw) | hw
  · exact signed_neg_sparse hw
  · exact lookupY_sparse table hw
  · exact signed_neg_sparse hw


private theorem seq_support (a b : AdaptiveCircuit) (ws : List Wire)
    (ha : a.wires ⊆ ws) (hb : b.wires ⊆ ws) : (a.seq b).wires ⊆ ws := by
  intro w hw
  rw [modularWires_seq] at hw
  exact hw.elim (fun h => ha h) (fun h => hb h)
private theorem field_sparse (a : AdaptiveCircuit) (h : a.wires ⊆ List.range 836) :
    a.wires ⊆ sparseLookup := by
  intro w hw
  apply core_sparse
  have hh := h hw
  simp only [List.mem_range] at hh ⊢
  omega
private theorem raw_sparse (x y : Nat → Nat) :
    (signedRawProgram x y).wires ⊆ sparseLookup := by
  unfold signedRawProgram
  exact seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (lookupX_sparse _) (signed_lookup_sparse _)) (field_sparse _ secp256k1InPlaceDivision_wires_subset)) (point_square_support.trans core_sparse)) (lookupX_sparse _)) (field_sparse _ secp256k1InPlaceMultiplication_wires_subset)) (point_negate_support.trans core_sparse)) (lookupX_sparse _)) (signed_lookup_sparse _)
private theorem prepare_sparse (j : Nat) : circuitWires (windowPrepareCircuit j) ⊆
    List.range 837++List.range' (windowBankStart j) 16 := by
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

theorem preparedRawProgram_tight_support (x y : Nat → Nat → Nat) (j : Nat) :
    (preparedRawProgram x y j).wires ⊆ List.range 837++List.range' (windowBankStart j) 16 := by
  have hp : (AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).wires ⊆
      List.range 837++List.range' (windowBankStart j) 16 := by
    simpa only [AdaptiveCircuit.wires,List.append_nil] using prepare_sparse j
  rw [preparedRawProgram]
  apply seq_support _ _ _ (seq_support _ _ _ hp ?_) hp
  intro w hw
  rw [parkedRawProgram,AdaptiveCircuit.relabel_wires] at hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  have hb := raw_sparse (x j) (y j) hv
  simp only [sparseLookup,List.mem_append,List.mem_range,List.mem_range'_1] at hb
  have hs : 855≤windowBankStart j := by unfold windowBankStart; omega
  rcases hb with h | h
  · rw [windowAddressPerm_core _ hs v (by dsimp only [Wire] at *; omega)]
    exact List.mem_append_left _ (List.mem_range.mpr h)
  · have he : windowAddressPerm (windowBankStart j) hs v=windowBankStart j+(v-839) := by
      change windowAddressSwap (windowBankStart j) v=_
      rw [windowAddressSwap,if_pos (by dsimp only [Wire] at *; omega)]
    rw [he]
    apply List.mem_append_right
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *
    omega

/-- The whole raw trial omits flag 837 but retains point infinity wire 838. -/
def streamTightAllocation : List Wire := List.range 837 ++ (838 :: streamAddress)
private theorem address_tight : streamAddress ⊆ streamTightAllocation := by
  intro w hw
  exact List.mem_append_right _ (List.mem_cons_of_mem _ hw)
private theorem axis_support (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit)
    (hc : ∀ c∈calls, c.wires ⊆ streamTightAllocation) (ht : tail.wires ⊆ streamTightAllocation) :
    (streamAxis calls prior tail).wires ⊆ streamTightAllocation := by
  induction calls generalizing prior with
  | nil => exact ht
  | cons c cs ih =>
    intro w hw
    rw [streamAxis,modularWires_seq,modularWires_seq] at hw
    rcases hw with hw | hw | hw
    · simp only [AdaptiveCircuit.wires,circuitWires,List.flatMap_map,List.mem_append,List.not_mem_nil,or_false,List.mem_flatMap] at hw
      obtain ⟨v,hv,hw⟩ := hw
      simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
      subst w
      exact address_tight hv
    · exact hc c (by simp) hw
    · exact fourierContinue_support .inverse streamAddress.reverse prior _ streamTightAllocation
        (fun _ hv => address_tight (List.mem_reverse.mp hv))
        (fun bs => ih bs (by intro a ha; exact hc a (by simp [ha]))) hw
private theorem root_support : (AdaptiveCircuit.unitary [.X 836] .done).wires ⊆ streamTightAllocation := by
  intro w hw
  simp [AdaptiveCircuit.wires,circuitWires,gateWires] at hw
  subst w
  exact List.mem_append_left _ (List.mem_range.mpr (by decide))

attribute [local irreducible] preparedRawProgram

theorem streamRawTrial_tight_support (P Q : Point) :
    (streamRawTrial P Q).wires ⊆ streamTightAllocation := by
  have hc : ∀ R j, (streamRawCall R j).wires ⊆ streamTightAllocation := by
    intro R j w hw
    rw [streamRawCall] at hw
    have h := preparedRawProgram_tight_support (fun _ a => (oddWindowX R j a).val)
      (fun _ a => (oddWindowY R j a).val) 0 hw
    rw [List.mem_append] at h
    rcases h with h | h
    · exact List.mem_append_left _ h
    · exact address_tight h
  rw [streamRawTrial]
  apply seq_support _ _ _ root_support
  apply axis_support _ List.nil _ ?_ (axis_support _ List.nil _ ?_ root_support)
  · intro c h
    simp only [streamRawLeftCalls,List.mem_cons,List.mem_map] at h
    rcases h with rfl | ⟨j,hj,rfl⟩
    · intro w hw
      rw [physicalPointLookup] at hw
      have h := directPointLookup_support _ (List.range' 855 16) (List.range' 519 16) 836 hw
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
      simp only [streamTightAllocation,streamAddress,List.mem_append,List.mem_cons,List.mem_range,List.mem_range'_1]
      dsimp only [Wire] at *
      omega
    · exact hc _ _
  · intro c h
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    exact hc _ _
private theorem card_bound (a : AdaptiveCircuit) (h : a.wires ⊆ streamTightAllocation) : a.qubitCount≤854 := by
  have hs : a.wires.dedup.toFinset ⊆ streamTightAllocation.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,streamTightAllocation,streamAddress,List.length_append,
    List.length_range,List.length_range',List.length_cons] using hc

theorem streamRawTrial_qubits_854 (P Q : Point) : (streamRawTrial P Q).qubitCount≤854 :=
  card_bound _ (streamRawTrial_tight_support P Q)

theorem streamRepeatedProgram_qubits_854 (Q : Point) : (streamRepeatedProgram Q).qubitCount≤854 := by
  apply card_bound
  intro w hw
  have hr : (streamResetTrial Q).wires ⊆ streamTightAllocation := by
    intro v hv
    rw [streamResetTrial,modularWires_seq] at hv
    rcases hv with hv | hv
    · exact streamRawTrial_tight_support G Q hv
    · have h := resetRegister_support (streamResetWires Q) hv
      exact streamRawTrial_tight_support G Q (by simpa [streamResetWires] using h)
  exact hr (repeatWindowProgram_support _ _ hw)

/-- The full streaming program never touches the unused zero-test flag. -/
theorem streamRawTrial_avoids_837 (P Q : Point) : 837 ∉ (streamRawTrial P Q).wires := by
  intro h
  have hs := streamRawTrial_tight_support P Q h
  norm_num [streamTightAllocation,streamAddress,List.mem_range'_1] at hs

/-- Reset measures the actual support, so its measurement bound also tightens. -/
theorem streamRepeatedProgram_measurements_854 (Q : Point) :
    (streamRepeatedProgram Q).measurementCount ≤ 47471340504 := by
  have hn : (streamResetWires Q).length ≤ 854 := by
    simpa only [streamResetWires,AdaptiveCircuit.qubitCount] using streamRawTrial_qubits_854 G Q
  rw [streamRepeatedProgram,(repeatWindowProgram_resources _ _).2,streamResetTrial,
    modularMeasurements_seq,streamRawTrial_measurementCount,streamTrialReset,resetRegister_measurements]
  omega

/-- Tighter support and reset bounds with the same actual acceptance event and gates. -/
theorem streamRepeatedProgram_tight_certificate (Q : Point)
    (hG : G ≠ 0) (hQ : Q ≠ 0) (hrQ : order • Q=0) (d : Nat) (hd : Q=d • G) :
    (streamRepeatedProgram Q).qubitCount≤854 ∧
    (primitiveResources (streamRepeatedProgram Q)).toffoli=114286067336 ∧
    (streamRepeatedProgram Q).tCount≤800005504760 ∧
    (streamRepeatedProgram Q).measurementCount≤47471340504 ∧
    (99 : ℝ)/100 ≤ Instrument.bornMass ((streamRepeatedProgram Q).run.filter
      (fun b => (streamRepeatedCandidate Q b.history).isSome)) (ket zeroBasisState) ∧
    (∀ hist c, streamRepeatedCandidate Q hist=some c → c=(d : ZMod order)) :=
  ⟨streamRepeatedProgram_qubits_854 Q,(streamRepeatedProgram_gate_counts Q).1,
    streamRepeatedProgram_tCount_le Q,streamRepeatedProgram_measurements_854 Q,
    streamRepeatedCandidate_success Q hG hQ hrQ d hd,
    fun hist c hc => streamRepeatedCandidate_sound Q d hd hist c hc⟩
end
end ShorECDLP.Paper2607_13816
