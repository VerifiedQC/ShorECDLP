import ShorECDLP.Submission.«2607_13816».Window.RawWeight
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

attribute [local irreducible] AdaptiveCircuit.WellFormed controlledModularNegate squareSubtract
  negativeControlledModularNegate
  secp256k1InPlaceDivision secp256k1InPlaceMultiplication

private theorem lookup_wf (table : Nat → Nat) (acc : List Wire)
    (hl : acc.length=256)
    (hn : ([836,559,560,561,558]++List.range' 7 256++acc).Nodup) :
    (lookupModularAddProgram table pointLookupAddress pointLookupPath
      (List.range' 7 256) acc secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558).WellFormed := by
  have ht : (tableLookupProgram (fun label => tableWordMask (List.range' 7 256) (table label))
      pointLookupAddress 836 pointLookupPath).WellFormed := by
    apply tableLookupProgram_wellFormed _ _ _ _ (by decide +kernel) (by decide +kernel)
    intro label w hw hm
    have hh : w∈List.range' 7 256 := tableBitsMask_subset _ _ hm
    simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'_1] at hw hh
    dsimp only [Wire] at *
    omega
  exact (ht.seq (controlledModularAdd_wellFormed _ _ _ _ _ _ _ _ _
    (by simpa using hl.symm) (by omega)
    (by simpa [secp256k1ReductionConstantBits] using hl) hn)).seq ht

attribute [local irreducible] lookupModularAddProgram

private theorem y_negate_layout :
    ([854,559,560,561,558]++List.range' 580 256++List.range' 7 256).Nodup := by decide +kernel
private theorem y_lookup_layout :
    ([836,559,560,561,558]++List.range' 7 256++List.range' 580 256).Nodup := by decide +kernel
private theorem square_layout :
    ([558,559,561,562,560]++List.range' 580 256++(7::List.range' 8 255)).Nodup := by decide +kernel
private theorem subtract_layout :
    ([836,558,560,561,559]++(7::List.range' 8 255)++List.range' 263 256).Nodup := by decide +kernel

private theorem signed_y_wf (table : Nat → Nat) : (signedPointLookupY table).WellFormed := by
  have hn : (negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558).WellFormed := by
    rw [negativeControlledModularNegate]
    have hx : (AdaptiveCircuit.unitary [.X 854] .done).WellFormed := by
      rw [AdaptiveCircuit.WellFormed, AdaptiveCircuit.WellFormed]
      exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], trivial⟩
    exact (hx.seq (controlledModularNegate_wellFormed (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558
      (by simp) (by simp) (by simp) y_negate_layout)).seq hx
  rw [signedPointLookupY, signedLookupModularAddProgram, List.length_range']
  exact (hn.seq (lookup_wf table (List.range' 580 256) (by simp) y_lookup_layout)).seq hn

private theorem square_wf : fig14SquareSubtract.WellFormed := by
  rw [fig14SquareSubtract]
  exact squareSubtract_wellFormed (List.range' 263 256) (List.range' 580 256) 7 (List.range' 8 255)
    secp256k1ReductionConstantBits (constantBits 256 ShorECDLP.p) ShorECDLP.p 836 558 559 561 562 560
    (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp)
    square_layout subtract_layout
private theorem negate_wf : fig14Negate.WellFormed := by
  rw [fig14Negate]
  exact controlledModularNegate_wellFormed (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558
    (by simp) (by simp) (by simp) (by decide +kernel)

attribute [local irreducible] fig14SquareSubtract fig14Negate signedPointLookupY fig14LookupX

/-- The raw five-query core is well formed on the entire state space. -/
theorem signedRawProgram_wellFormed (x y : Nat → Nat) : (signedRawProgram x y).WellFormed := by
  have hx (table : Nat → Nat) : (fig14LookupX table).WellFormed := by
    rw [fig14LookupX]
    exact lookup_wf table (List.range' 263 256) (by simp) (by decide +kernel)
  exact ((((((((hx _).seq (signed_y_wf _)).seq secp256k1InPlace_wellFormed.1).seq
    square_wf).seq (hx _)).seq secp256k1InPlace_wellFormed.2).seq negate_wf).seq
    (hx _)).seq (signed_y_wf _)

/-- Address parking and preparation preserve global well-formedness. -/
theorem preparedRawProgram_wellFormed (x y : Nat → Nat → Nat) (j : Nat) :
    (preparedRawProgram x y j).WellFormed := by
  have hp : (parkedRawProgram x y j).WellFormed := by
    simpa only [parkedRawProgram, AdaptiveCircuit.relabel_wellFormed] using
      signedRawProgram_wellFormed (x j) (y j)
  have hu : (AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).WellFormed :=
    by
      rw [AdaptiveCircuit.WellFormed, AdaptiveCircuit.WellFormed]
      exact ⟨windowPrepareCircuit_wellFormed j, trivial⟩
  exact (hu.seq hp).seq hu

theorem rawWindowSchedule_wellFormed (x y : Nat → Nat → Nat) (js : List Nat) :
    (rawWindowSchedule x y js).WellFormed := by
  induction js with
  | nil => simp only [rawWindowSchedule, AdaptiveCircuit.WellFormed]
  | cons j js ih => exact (preparedRawProgram_wellFormed x y j).seq ih

private theorem physical_lookup_wf (table : Nat → Point) : (physicalPointLookup table).WellFormed := by
  apply tableLookupProgram_wellFormed _ _ _ _ (by decide +kernel) (by decide +kernel)
  intro label w hw hm
  have hh : w∈pointLogicalWires := tableBitsMask_subset _ _ hm
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_cons,
    List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at hw hh
  dsimp only [Wire] at *
  omega

/-- Initialization and every raw call are normalized even outside the good-input domain. -/
theorem initializedRawProgram_wellFormed (A P : Point) (x y : Nat → Nat → Nat) (js : List Nat) :
    (initializedRawProgram A P x y js).WellFormed :=
  (physical_lookup_wf _).seq (rawWindowSchedule_wellFormed x y js)

theorem reducedRawProgram_wellFormed (P Q : Point) : (reducedRawProgram P Q).WellFormed :=
  initializedRawProgram_wellFormed _ _ _ _ _

/-- Summing all unnormalized measurement histories preserves every input's Born mass. -/
theorem reducedRawProgram_bornMass (P Q : Point) (ψ : State) :
    (reducedRawProgram P Q).run.bornMass ψ = normSq ψ :=
  AdaptiveCircuit.run_preservesBornMass _ (reducedRawProgram_wellFormed P Q) ψ
/-- The actual Hadamard/root preparation has unit mass. -/
theorem reducedRawEntryState_normSq : normSq reducedRawEntryState = 1 := by
  have hh : CircuitWellFormed reducedPhasePrepare := by
    intro g hg
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
    trivial
  rw [reducedRawEntryState, normSq_run _ (by simp [CircuitWellFormed, Gate.WellFormed]),
    normSq_run _ hh, normSq_ket]

/-- The raw arithmetic output is a normalized instrument on the physical entry. -/
theorem reducedRawProgram_entry_bornMass (P Q : Point) :
    (reducedRawProgram P Q).run.bornMass reducedRawEntryState = 1 := by
  rw [reducedRawProgram_bornMass, reducedRawEntryState_normSq]

attribute [local instance] Classical.propDecidable

/-- Feeding only the excluded input component preserves its small total mass.
This does not bound a measured failure event or interference with the good component. -/
theorem reducedRawProgram_excluded_bornMass (P Q : Point) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrP : order • P = 0) (hrQ : order • Q = 0) :
    (reducedRawProgram P Q).run.bornMass (reducedRawEntryState.filter
      (fun s => ¬reducedRawExclusions P Q hP hQ hrP hrQ s)) ≤ (7 : ℝ) / 4096 := by
  rw [reducedRawProgram_bornMass]
  exact reducedRawEntry_excluded_mass P Q hP hQ hrP hrQ

end
end ShorECDLP.Paper2607_13816
