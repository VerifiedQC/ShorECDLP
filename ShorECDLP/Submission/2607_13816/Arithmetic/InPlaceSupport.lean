import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerSupport
import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlaceResources
import ShorECDLP.Submission.«2607_13816».EEA.WrapperSupport

/-!
# Complete Figure 15 physical allocation

The actual programs use labels 0 through 835, including the borrowed data bank,
every adaptive correction, and final physical swaps. This proves an upper bound
of 836 wires; it does not claim the source paper's tighter 835-wire target.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem work_layout :
    [558,560,561,559]++List.range' 263 256++List.range' 580 256++List.range' 7 256 ⊆ List.range 836 := by
  intro w hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range',List.mem_range] at hw ⊢
  omega
private theorem data_layout :
    [558,560,561,559]++List.range' 263 256++List.range' 7 256++List.range' 580 256 ⊆ List.range 836 := by
  intro w hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range',List.mem_range] at hw ⊢
  omega
private theorem reduction_split : secp256k1ReductionConstantBits = true::secp256k1ReductionConstantBits.tail := by decide +kernel
private theorem modulus_split : constantBits 256 ShorECDLP.p = true::(constantBits 256 ShorECDLP.p).tail := by decide +kernel

theorem fig15MultiplyToWork_wires_subset : fig15MultiplyToWork.wires ⊆ List.range 836 := by
  unfold fig15MultiplyToWork
  rw [reduction_split]
  exact List.Subset.trans (hornerMul256_wires_subset _ _ _ _ _ _ _ _ _
    List.length_range' List.length_range' (by decide +kernel) (by decide +kernel) (by decide +kernel)) work_layout

theorem fig15MultiplyToData_wires_subset : fig15MultiplyToData.wires ⊆ List.range 836 := by
  unfold fig15MultiplyToData
  rw [reduction_split]
  exact List.Subset.trans (hornerMul256_wires_subset _ _ _ _ _ _ _ _ _
    List.length_range' List.length_range' (by decide +kernel) (by decide +kernel) (by decide +kernel)) data_layout

theorem fig15MultiplyToDataInverse_wires_subset : fig15MultiplyToDataInverse.wires ⊆ List.range 836 := by
  unfold fig15MultiplyToDataInverse
  rw [modulus_split]
  exact List.Subset.trans (hornerMulInverse256_wires_subset _ _ _ _ _ _ _ _ _
    List.length_range' List.length_range' (by decide +kernel) (by decide +kernel) (by decide +kernel)) data_layout

private theorem exchange_bound (w : Wire) (hw : w ∈ List.range 580) : eeaWorkspaceExchange w ∈ List.range 836 := by
  simp only [List.mem_range] at hw ⊢
  by_cases ha : 7 ≤ w ∧ w < 263
  · obtain ⟨hlo,hhi⟩ := ha
    have he := eeaWorkspaceExchange_work (w-7) (by dsimp only [Wire] at *; omega)
    have hh : 7+(w-7)=w := by dsimp only [Wire] at *; omega
    rw [hh] at he
    rw [he]; dsimp only [Wire] at *; omega
  · have hy : ¬ (580 ≤ w ∧ w < 836) := by
      intro h; obtain ⟨hlo,hhi⟩ := h; dsimp only [Wire] at *; omega
    rw [eeaWorkspaceExchange_frame w ha hy]; omega
private theorem relabel_support (p : AdaptiveCircuit) (hp : p.wires ⊆ List.range 580) :
    (p.relabel eeaWorkspaceExchange).wires ⊆ List.range 836 := by
  rw [AdaptiveCircuit.relabel_wires]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact exchange_bound v (hp hv)
theorem secp256k1EEAForwardInDataBank_wires_subset : secp256k1EEAForwardInDataBank.wires ⊆ List.range 836 :=
  relabel_support _ secp256k1EEAForwardWrapper_wires_subset
theorem secp256k1EEAReverseInDataBank_wires_subset : secp256k1EEAReverseInDataBank.wires ⊆ List.range 836 :=
  relabel_support _ secp256k1EEAReverseWrapper_wires_subset
private theorem correction_support (targets : List Wire) (outcomes : List Bool) :
    circuitWires (registerZCorrection targets outcomes) ⊆ targets := by
  induction targets generalizing outcomes with
  | nil => simp [registerZCorrection,circuitWires]
  | cons t ts ih =>
    cases outcomes with
    | nil => simp [registerZCorrection,circuitWires]
    | cons b bs =>
      have hh := ih bs
      intro w hw
      cases b <;> simp only [registerZCorrection,Bool.false_eq_true,if_false,if_true,
        List.nil_append,circuitWires,List.flatMap_append,pauliZ,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,gateWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] at hw
      · exact List.mem_cons_of_mem t (hh hw)
      · rcases hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem t (hh hw)
private theorem swap_support : circuitWires fig15SwapOutput ⊆ List.range 836 := by
  intro w hw
  simp only [circuitWires,fig15SwapOutput,List.mem_flatMap] at hw
  obtain ⟨g,⟨i,hi,hg⟩,hw⟩ := hw
  simp only [List.mem_range] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw <;>
    simp only [List.mem_range] <;> dsimp only [Wire] at * <;> omega
private theorem data_support : List.range' 580 256 ⊆ List.range 836 := by
  intro w hw
  simp only [List.mem_range',List.mem_range] at hw ⊢
  omega
private theorem measured_support (targets : List Wire) (next : List Bool → AdaptiveCircuit)
    (ht : targets ⊆ List.range 836) (hn : ∀ bs, (next bs).wires ⊆ List.range 836) :
    (measureResetThen targets next).wires ⊆ List.range 836 := by
  induction targets generalizing next with
  | nil => exact hn []
  | cons t ts ih =>
    have hm : t ∈ List.range 836 := ht List.mem_cons_self
    have hs : ts ⊆ List.range 836 := fun _ hw => ht (List.mem_cons_of_mem t hw)
    have h0 := ih (fun bs => next (false::bs)) hs (fun bs => hn (false::bs))
    have h1 := ih (fun bs => next (true::bs)) hs (fun bs => hn (true::bs))
    intro w hw
    simp only [measureResetThen,AdaptiveCircuit.wires,List.mem_cons,List.mem_append] at hw
    rcases hw with rfl | hw | hw
    · exact hm
    · exact h0 hw
    · exact h1 hw
private theorem seq_support (a b : AdaptiveCircuit)
    (ha : a.wires ⊆ List.range 836) (hb : b.wires ⊆ List.range 836) :
    (a.seq b).wires ⊆ List.range 836 := by
  intro w hw
  rw [modularWires_seq] at hw
  exact hw.elim (fun h => ha h) (fun h => hb h)
private theorem unitary_support836 (c : Circuit) (hc : circuitWires c ⊆ List.range 836) :
    (AdaptiveCircuit.unitary c .done).wires ⊆ List.range 836 := by
  simpa only [AdaptiveCircuit.wires,List.append_nil] using hc
attribute [local irreducible] fig15MultiplyToWork fig15MultiplyToData fig15MultiplyToDataInverse
  secp256k1EEAForwardWrapper secp256k1EEAForwardInDataBank secp256k1EEAReverseInDataBank
private theorem division_after_support (bs : List Bool) : (fig15DivisionAfterReset bs).wires ⊆ List.range 836 := by
  exact seq_support _ _ (seq_support _ _ (seq_support _ _
    (seq_support _ _ secp256k1EEAReverseInDataBank_wires_subset fig15MultiplyToData_wires_subset)
    (unitary_support836 _ (List.Subset.trans (correction_support _ bs) data_support)))
    fig15MultiplyToDataInverse_wires_subset) (unitary_support836 _ swap_support)
private theorem multiplication_after_support (bs : List Bool) : (fig15MultiplicationAfterReset bs).wires ⊆ List.range 836 := by
  exact seq_support _ _ (seq_support _ _ (seq_support _ _ (seq_support _ _
    (seq_support _ _ secp256k1EEAForwardInDataBank_wires_subset fig15MultiplyToData_wires_subset)
    (unitary_support836 _ (List.Subset.trans (correction_support _ bs) data_support)))
    fig15MultiplyToDataInverse_wires_subset) secp256k1EEAReverseInDataBank_wires_subset)
    (unitary_support836 _ swap_support)
/-- Every branch of the complete division uses only the concrete 0–835 allocation. -/
theorem secp256k1InPlaceDivision_wires_subset : secp256k1InPlaceDivision.wires ⊆ List.range 836 := by
  have hf : secp256k1EEAForwardWrapper.wires ⊆ List.range 836 := by
    intro w hw
    have h := secp256k1EEAForwardWrapper_wires_subset hw
    simp only [List.mem_range] at h ⊢; omega
  exact seq_support _ _ (seq_support _ _ hf fig15MultiplyToWork_wires_subset)
    (measured_support _ _ data_support division_after_support)
/-- Every branch of the complete multiplication uses only the concrete 0–835 allocation. -/
theorem secp256k1InPlaceMultiplication_wires_subset : secp256k1InPlaceMultiplication.wires ⊆ List.range 836 :=
  seq_support _ _ fig15MultiplyToWork_wires_subset
    (measured_support _ _ data_support multiplication_after_support)
private theorem adaptive_count836 (p : AdaptiveCircuit) (h : p.wires ⊆ List.range 836) : p.qubitCount ≤ 836 := by
  have hs : p.wires.dedup.toFinset ⊆ (List.range 836).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h (by simpa using hw))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range (n := 836))] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc
/-- Direct physical upper bound on the same circuit as the division contract. -/
theorem secp256k1InPlaceDivision_qubitCount : secp256k1InPlaceDivision.qubitCount ≤ 836 :=
  adaptive_count836 _ secp256k1InPlaceDivision_wires_subset
/-- Direct physical upper bound on the same circuit as the multiplication contract. -/
theorem secp256k1InPlaceMultiplication_qubitCount : secp256k1InPlaceMultiplication.qubitCount ≤ 836 :=
  adaptive_count836 _ secp256k1InPlaceMultiplication_wires_subset


/-- Coherence and resources of the literal complete division program. -/
theorem secp256k1InPlaceDivision_certificate :
    CoherentlyImplementsOn secp256k1InPlaceDivision
      (Finsupp.lmapDomain ℂ ℂ fig15DivisionOutputState) Secp256k1InPlaceInputValid ∧
    secp256k1InPlaceDivision.tCount = 269605707 ∧
    secp256k1InPlaceDivision.measurementCount = 11343835 ∧
    secp256k1InPlaceDivision.qubitCount ≤ 836 :=
  ⟨secp256k1InPlaceDivision_coherent,secp256k1InPlaceDivision_T,
    secp256k1InPlaceDivision_measurements,secp256k1InPlaceDivision_qubitCount⟩
/-- Coherence and resources of the literal complete multiplication program. -/
theorem secp256k1InPlaceMultiplication_certificate :
    CoherentlyImplementsOn secp256k1InPlaceMultiplication
      (Finsupp.lmapDomain ℂ ℂ fig15MultiplicationOutputState) Secp256k1InPlaceInputValid ∧
    secp256k1InPlaceMultiplication.tCount = 269605707 ∧
    secp256k1InPlaceMultiplication.measurementCount = 11343835 ∧
    secp256k1InPlaceMultiplication.qubitCount ≤ 836 :=
  ⟨secp256k1InPlaceMultiplication_coherent,secp256k1InPlaceMultiplication_T,
    secp256k1InPlaceMultiplication_measurements,secp256k1InPlaceMultiplication_qubitCount⟩

end ShorECDLP.Paper2607_13816
