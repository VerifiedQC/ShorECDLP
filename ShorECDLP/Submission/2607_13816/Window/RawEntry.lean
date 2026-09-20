import ShorECDLP.Submission.«2607_13816».Window.RawUniform
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

/-- The physical arithmetic entry is prepared by the emitted Hadamards, then root X. -/
def reducedRawEntryState : State :=
  Quantum.run [.X 836] (Quantum.run reducedPhasePrepare (ket zeroBasisState))

theorem scalarRootFlip_phaseWordState (ws : List Wire) (bs : List Bool)
    (s : BasisState) (h : 836 ∉ ws) :
    scalarRootFlip (phaseWordState ws bs s) = phaseWordState ws bs (scalarRootFlip s) := by
  induction ws generalizing bs s with
  | nil => rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      have hh : 836 ≠ w ∧ 836 ∉ ws := by simpa only [List.mem_cons, not_or] using h
      rw [phaseWordState, ih bs _ hh.2, phaseWordState]
      congr 1
      funext q
      simp only [scalarRootFlip, upd]
      split_ifs <;> simp_all

private theorem root_ket (s : BasisState) :
    Quantum.run [.X 836] (ket s) = ket (scalarRootFlip s) := by
  have h := Quantum.run_ket_agrees_classical [.X 836] s (by simp [HPFree])
  simpa [ket,Classical.run,Classical.applyGate,scalarRootFlip] using h

/-- Root setup preserves the uniform assignment family and flips only its fixed background. -/
theorem reducedRawEntryState_uniform : reducedRawEntryState =
    (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) •
      phaseUniformSum reducedPhaseWires (scalarRootFlip zeroBasisState) := by
  rw [reducedRawEntryState, reducedPhasePrepare_uniform, map_smul]
  unfold phaseUniformSum
  rw [stateLinear_list_sum]
  simp only [List.map_map, Function.comp_def]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro bs _
  rw [root_ket, scalarRootFlip_phaseWordState _ _ _ (by decide +kernel)]

/-- Born mass of any event at the actual root-enabled arithmetic entry. -/
theorem reducedRawEntryState_filtered_mass (p : BasisState → Prop) [DecidablePred p] :
    normSq (reducedRawEntryState.filter p) =
      (((fourierOutcomes 464).filter
        (fun bs => p (phaseWordState reducedPhaseWires bs (scalarRootFlip zeroBasisState)))).length : ℝ) /
        2^464 := by
  rw [reducedRawEntryState_uniform, Finsupp.filter_smul]
  have hf := phaseBasisSum_filter
    ((fourierOutcomes reducedPhaseWires.length).map
      (fun bs => phaseWordState reducedPhaseWires bs (scalarRootFlip zeroBasisState))) p
  simp only [List.map_map, Function.comp_def, List.filter_map] at hf
  unfold phaseUniformSum
  rw [hf]
  have h := phaseUniformSum_filtered_normalized_mass reducedPhaseWires
    (by decide +kernel) (scalarRootFlip zeroBasisState) p
  simpa only [reducedPhaseWires, List.length_append, List.length_range'] using h

/-- Every emitted entry assignment has its root control enabled. -/
theorem reducedRawEntryWord_root (bs : List Bool) :
    phaseWordState reducedPhaseWires bs (scalarRootFlip zeroBasisState) 836 = true := by
  rw [phaseWordState_frame _ _ _ _ (by decide +kernel)]
  simp [scalarRootFlip, zeroBasisState]
/-- Root-enabled entry assignments satisfy the clean arithmetic initialization contract. -/
theorem reducedRawEntryWord_ready (bs : List Bool) :
    PointInitializeValid
      (phaseWordState reducedPhaseWires bs (scalarRootFlip zeroBasisState)) := by
  rw [← scalarRootFlip_phaseWordState _ _ _ (by decide +kernel)]
  apply (scalarRootFlip_ready _ ?_).1
  have hz (w : Wire) (hw : w ∉ reducedPhaseWires) :
      phaseWordState reducedPhaseWires bs zeroBasisState w = false :=
    phaseWordState_frame _ _ _ _ hw
  constructor
  · intro w hw
    apply hz
    simp only [reducedPhaseWires,List.mem_append,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have hp (j : Nat) (hj : j=0 ∨ j=17) :
        ScalarPaddingClean j (phaseWordState reducedPhaseWires bs zeroBasisState) := by
      unfold ScalarPaddingClean wireValues
      have he : (List.range' (windowBankStart j+257) 15).map
          (phaseWordState reducedPhaseWires bs zeroBasisState) =
          (List.range' (windowBankStart j+257) 15).map (fun _ => false) := by
        apply List.map_congr_left
        intro w hw
        apply hz
        simp only [reducedPhaseWires,List.mem_append,List.mem_range'_1,windowBankStart] at *
        rcases hj with rfl | rfl <;> omega
      rw [he]
      simp
    exact ⟨hp 0 (Or.inl rfl), hp 17 (Or.inr rfl)⟩

end
end ShorECDLP.Paper2607_13816
