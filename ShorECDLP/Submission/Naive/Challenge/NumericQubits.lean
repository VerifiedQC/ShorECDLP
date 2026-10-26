import ShorECDLP.Submission.Naive.Challenge.Certificate

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge Arithmetic
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

/-- Constant rows may denote arbitrary points; no subgroup premise is needed
for the physical wire envelope. -/
theorem trialGates_fixed_support (Q : Point) :
    circuitWires (trialGates.flatMap (TemplateGate.instantiate
      (readConstant naivePowerCoefficient Q))) ⊆ fixedResetWires := by
  let support := bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
    scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla]
  have hh : CircuitUsesOnly support (PhaseEstimation.hadamards (bitcoinAReg ++ bitcoinBReg)) := by
    apply usesOnly_mono (hadamards_usesOnly _)
    intro w hw
    simp only [support, List.mem_append] at hw ⊢
    tauto
  have hs (cs : List Wire) (points : List Point)
      (hc : ∀ w ∈ cs, w ∈ bitcoinAReg ++ bitcoinBReg) :
      CircuitUsesOnly support (scalarMulCore bitcoinPointReg bitcoinWorkStart cs points) := by
    apply usesOnly_mono (scalarMulCore_usesOnly cs bitcoinPointReg points bitcoinWorkStart)
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · have h := hc w hw
      simp only [support, List.mem_append] at h ⊢
      tauto
    · simp only [support, List.mem_append]; tauto
    · simp only [support, List.mem_append]; tauto
  have hq (cs : List Wire) (hc : ∀ w ∈ cs, w ∈ bitcoinAReg ++ bitcoinBReg) :
      CircuitUsesOnly support (iqft cs bitcoinQFTAncilla) := by
    apply usesOnly_mono (iqft_usesOnly cs bitcoinQFTAncilla)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · have h := hc w hw
      simp only [support, List.mem_append] at h ⊢
      tauto
    · simp only [support, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      tauto
  apply (ModAddSupport.circuitUsesOnly_iff_support _ _).mp
  apply usesOnly_mono (xs := support)
  · simp only [trialGates, List.flatMap_append, literalGates_instantiate, scalarGates_source]
    exact usesOnly_append (usesOnly_append (usesOnly_append hh
      (hs _ _ (fun _ h => List.mem_append_left _ h)))
      (hs _ _ (fun _ h => List.mem_append_right _ h)))
      (usesOnly_append (hq _ (fun _ h => List.mem_append_left _ h))
        (hq _ (fun _ h => List.mem_append_right _ h)))
  · exact bitcoinDeclaredWires_subset

theorem gateNative_wires {n : Nat} (read : ConstantBit n → Bool) (gs : List (TemplateGate n)) :
    (gateNative read gs).wires = circuitWires (gs.flatMap (TemplateGate.instantiate read)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [gateNative, AdaptiveCircuit.wires, ih, List.flatMap_cons,
      circuitWires, List.flatMap_append]

theorem resetNative_support (ws : List Wire) : (resetNative ws).wires ⊆ ws := by
  induction ws with
  | nil => exact List.Subset.refl _
  | cons w ws ih =>
    intro v hv
    simp only [resetNative, AdaptiveCircuit.wires, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · exact List.mem_cons_self
    all_goals exact List.mem_cons_of_mem _ (ih hv)

theorem observedNative_fixed_support (Q : Point) :
    (observedNative (readConstant naivePowerCoefficient Q)).wires ⊆ fixedResetWires := by
  intro w hw
  rw [observedNative, wires_seq] at hw
  rcases hw with hw | hw
  · rw [gateNative_wires] at hw
    exact trialGates_fixed_support Q hw
  · have h := zObserve_support _ hw
    apply bitcoinDeclaredWires_subset
    simp only [List.mem_append] at h ⊢
    tauto

theorem roundNative_fixed_support (Q : Point) :
    (roundNative (readConstant naivePowerCoefficient Q)).wires ⊆ fixedResetWires := by
  intro w hw
  rw [roundNative, wires_seq] at hw
  rcases hw with hw | hw
  · exact observedNative_fixed_support Q hw
  · exact resetNative_support _ hw

theorem repeatFixed_support (a : AdaptiveCircuit) (support : List Wire)
    (ha : a.wires ⊆ support) (n : Nat) : (repeatFixed a n).wires ⊆ support := by
  induction n with
  | zero => exact List.nil_subset _
  | succ n ih =>
    intro w hw
    rw [repeatFixed, wires_seq] at hw
    exact hw.elim (fun h => ha h) (fun h => ih h)

theorem naiveRepeatedEntry_fixed_support (Q : Point) :
    (naiveRepeatedEntry.instantiate Q).wires ⊆ fixedResetWires := by
  rw [naiveRepeatedEntry_instantiate]
  exact repeatFixed_support _ _ (roundNative_fixed_support Q) 26

theorem naiveRepeatedEntry_qubit_bound (Q : Point) :
    (resources (naiveRepeatedEntry.instantiate Q)).qubits ≤ 206624 := by
  have hs : (naiveRepeatedEntry.instantiate Q).wires.toFinset ⊆ fixedResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (naiveRepeatedEntry_fixed_support Q (List.mem_toFinset.mp hw))
  have hc := Finset.card_le_card hs
  simpa only [resources, AdaptiveCircuit.qubitCount, List.card_toFinset,
    fixedResetWires, List.dedup_eq_self.mpr List.nodup_range, List.length_range,
    bitcoinQubitCount] using hc

end ShorECDLP.NaiveChallenge
