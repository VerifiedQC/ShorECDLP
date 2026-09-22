import ShorECDLP.Submission.«2607_13816».Window.RawResources
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] preparedRawTrial rawRepeatedProgram rawTrialResetWires
private theorem adder_counts : pointLookupAdderPrimitives.toffoli=2813 ∧
    pointLookupAdderPrimitives.phase=0 ∧ pointLookupAdderPrimitives.measurements=511 := by
  decide +kernel
private theorem lookup_counts (table : Nat → Nat) :
    (pointLookupPrimitives table).toffoli=68347 ∧
    (pointLookupPrimitives table).phase=0 ∧ (pointLookupPrimitives table).measurements=66045 := by
  simp only [pointLookupPrimitives,lookupWordPrimitives,pointLookupAddress,List.length_range',
    PrimitiveResources.add,adder_counts.1,adder_counts.2.1,adder_counts.2.2]
  decide
private theorem core_counts (x y : Nat → Nat) :
    (signedRawPrimitives x y).toffoli=72884182 ∧
    (signedRawPrimitives x y).phase=0 ∧ (signedRawPrimitives x y).measurements=30272702 := by
  simp only [signedRawPrimitives,signedPointLookupPrimitives,PrimitiveResources.add,
    (lookup_counts _).1,(lookup_counts _).2.1,(lookup_counts _).2.2]
  decide
private theorem schedule_counts (x y : Nat → Nat → Nat) (js : List Nat) :
    (rawSchedulePrimitives x y js).toffoli=js.length*72884182 ∧
    (rawSchedulePrimitives x y js).phase=0 ∧
    (rawSchedulePrimitives x y js).measurements=js.length*30272702 := by
  induction js with
  | nil => simp [rawSchedulePrimitives]
  | cons j js ih =>
    simp only [rawSchedulePrimitives,preparedRawPrimitives,PrimitiveResources.add,
      (core_counts _ _).1,(core_counts _ _).2.1,(core_counts _ _).2.2,ih.1,ih.2.1,ih.2.2,
      List.length_cons,Nat.add_mul,Nat.one_mul,Nat.zero_add,Nat.add_zero]
    constructor
    · omega
    · constructor
      · trivial
      · omega
private theorem trial_counts (Q : Point) :
    (preparedRawTrialPrimitives Q).toffoli=2040822631 ∧
    (preparedRawTrialPrimitives Q).phase=54168 ∧
    (preparedRawTrialPrimitives Q).measurements=847701655 := by
  simp only [preparedRawTrialPrimitives,reducedRawPrimitives,physicalPointLookupPrimitives,
    PrimitiveResources.add,(schedule_counts _ _ _).1,(schedule_counts _ _ _).2.1,
    (schedule_counts _ _ _).2.2,reducedRawIndices,List.length_append,List.length_range']
  decide
private theorem counts_transfer (a : AdaptiveCircuit) (r : PrimitiveResources)
    (hr : primitiveResources a=r) (t p m : Nat)
    (h : r.toffoli=t ∧ r.phase=p ∧ r.measurements=m) :
    (primitiveResources a).toffoli=t ∧ (primitiveResources a).phase=p ∧ a.measurementCount=m := by
  change _ ∧ _ ∧ (primitiveResources a).measurements=m
  rw [hr]
  exact h
/-- Counts include preparation, the raw oracle and actual semiclassical Fourier measurements. -/
theorem preparedRawTrial_counts (Q : Point) :
    (primitiveResources (preparedRawTrial Q)).toffoli=2040822631 ∧
    (primitiveResources (preparedRawTrial Q)).phase=54168 ∧
    (preparedRawTrial Q).measurementCount=847701655 :=
  counts_transfer _ _ (preparedRawTrial_primitive Q) _ _ _ (trial_counts Q)
private theorem repeat_counts (r : PrimitiveResources) (n : Nat)
    (h : r.toffoli=2040822631 ∧ r.phase=54168 ∧ r.measurements=847701655) :
    (scalePrimitives 56 (r.add ⟨0,0,0,0,0,n⟩)).toffoli=114286067336 ∧
    (scalePrimitives 56 (r.add ⟨0,0,0,0,0,n⟩)).phase=3033408 ∧
    (scalePrimitives 56 (r.add ⟨0,0,0,0,0,n⟩)).measurements=56*(847701655+n) := by
  simp [scalePrimitives,PrimitiveResources.add,h.1,h.2.1,h.2.2]
/-- The full support reset contributes one measurement per distinct used wire. -/
theorem rawRepeatedProgram_counts (Q : Point) :
    (primitiveResources (rawRepeatedProgram Q)).toffoli=114286067336 ∧
    (primitiveResources (rawRepeatedProgram Q)).phase=3033408 ∧
    (rawRepeatedProgram Q).measurementCount=56*(847701655+(rawTrialResetWires Q).length) :=
  counts_transfer _ _ (rawRepeatedProgram_primitive Q) _ _ _
    (repeat_counts _ _ (trial_counts Q))
/-- Seven per Toffoli and one per phase gate: a logical cost model, not phase synthesis. -/
theorem rawRepeatedProgram_resource_bounds (Q : Point) :
    (rawRepeatedProgram Q).qubitCount≤1303 ∧
    (rawRepeatedProgram Q).tCount≤800005504760 ∧
    (rawRepeatedProgram Q).measurementCount≤47471365648 := by
  have h := rawRepeatedProgram_counts Q
  have ht := primitiveResources_T_le (rawRepeatedProgram Q)
  rw [h.1,h.2.1] at ht
  have hm := rawTrialResetWires_length Q
  exact ⟨rawRepeatedProgram_qubitCount Q,by omega,by omega⟩
/-- Resource and success contracts refer to exactly the same full 56-round program. -/
theorem rawRepeatedProgram_success_resources (Q : Point)
    (hG : G≠0) (hQ : Q≠0) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (rawRepeatedProgram Q).qubitCount≤1303 ∧
    (rawRepeatedProgram Q).tCount≤800005504760 ∧
    (rawRepeatedProgram Q).measurementCount≤47471365648 ∧
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((rawRepeatedProgram Q).run.filter (fun b => (rawRepeatedCandidate Q b.history).isSome))
      (ket zeroBasisState) := by
  exact ⟨(rawRepeatedProgram_resource_bounds Q).1,
    (rawRepeatedProgram_resource_bounds Q).2.1,(rawRepeatedProgram_resource_bounds Q).2.2,
    rawRepeatedCandidate_success Q hG hQ hrQ d hQd⟩
end
end ShorECDLP.Paper2607_13816
