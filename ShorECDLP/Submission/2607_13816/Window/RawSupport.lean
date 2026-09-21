import ShorECDLP.Submission.«2607_13816».Window.RawRepetition
import ShorECDLP.Submission.«2607_13816».Window.ReducedReset
import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlaceSupport
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem seq_support (a b : AdaptiveCircuit) (ws : List Wire)
    (ha : a.wires ⊆ ws) (hb : b.wires ⊆ ws) : (a.seq b).wires ⊆ ws := by
  intro w hw
  rw [modularWires_seq] at hw
  exact hw.elim (fun h => ha h) (fun h => hb h)
private theorem field_support (a : AdaptiveCircuit) (h : a.wires ⊆ List.range 836) :
    a.wires ⊆ List.range 855 := by
  intro w hw
  have hh := h hw
  simp only [List.mem_range] at hh ⊢
  omega
private theorem square_support : fig14SquareSubtract.wires ⊆ List.range 855 := by
  intro w hw
  have hh : w ∈ (fig14CoordinateProgram 0 0).wires := by
    simp only [fig14CoordinateProgram,modularWires_seq]
    aesop
  have h := fig14CoordinateProgram_wires_subset 0 0 hh
  simp only [List.mem_range] at h ⊢
  omega
private theorem negate_support : fig14Negate.wires ⊆ List.range 855 := by
  intro w hw
  have hh : w ∈ (fig14CoordinateProgram 0 0).wires := by
    simp only [fig14CoordinateProgram,modularWires_seq]
    aesop
  have h := fig14CoordinateProgram_wires_subset 0 0 hh
  simp only [List.mem_range] at h ⊢
  omega

theorem signedRawProgram_support (x y : Nat → Nat) :
    (signedRawProgram x y).wires ⊆ List.range 855 := by
  unfold signedRawProgram
  exact seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (seq_support _ _ _ (fig14LookupX_wires _) (signedPointLookupY_wires _)) (field_support _ secp256k1InPlaceDivision_wires_subset)) (square_support)) (fig14LookupX_wires _)) (field_support _ secp256k1InPlaceMultiplication_wires_subset)) (negate_support)) (fig14LookupX_wires _)) (signedPointLookupY_wires _)

theorem preparedRawProgram_support (x y : Nat → Nat → Nat) (j : Nat) :
    (preparedRawProgram x y j).wires ⊆ List.range 839++List.range' (windowBankStart j) 16 := by
  have hp : (AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).wires ⊆
      List.range 839++List.range' (windowBankStart j) 16 := by
    simpa only [AdaptiveCircuit.wires,List.append_nil] using windowPrepareCircuit_support j
  rw [preparedRawProgram]
  apply seq_support _ _ _ (seq_support _ _ _ hp ?_) hp
  intro w hw
  rw [parkedRawProgram,AdaptiveCircuit.relabel_wires] at hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  have hb := List.mem_range.mp (signedRawProgram_support (x j) (y j) hv)
  have hs : 855≤windowBankStart j := by unfold windowBankStart; omega
  by_cases h : v<839
  · rw [windowAddressPerm_core _ hs v h]
    exact List.mem_append_left _ (List.mem_range.mpr h)
  · have he : windowAddressPerm (windowBankStart j) hs v=windowBankStart j+(v-839) := by
      change windowAddressSwap (windowBankStart j) v=_
      rw [windowAddressSwap,if_pos (by dsimp only [Wire] at *; omega)]
    rw [he]
    apply List.mem_append_right
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *
    omega
private theorem schedule_support (x y : Nat → Nat → Nat) (js : List Nat)
    (hj : ∀ j∈js, j∈reducedRawIndices) :
    (rawWindowSchedule x y js).wires ⊆ reducedResetWires := by
  induction js with
  | nil => simp [rawWindowSchedule,AdaptiveCircuit.wires]
  | cons j js ih =>
    rw [rawWindowSchedule]
    apply seq_support
    · intro w hw
      have h := preparedRawProgram_support x y j hw
      have hb := hj j (by simp)
      simp only [reducedRawIndices,List.mem_append,List.mem_range'_1] at hb
      simp only [List.mem_append,List.mem_range,List.mem_range'_1,windowBankStart] at h
      simp only [reducedResetWires,reducedPhaseWires,List.mem_append,List.mem_range,List.mem_range'_1]
      dsimp only [Wire] at *
      omega
    · exact ih (fun k hk => hj k (by simp [hk]))
theorem reducedRawProgram_support (P Q : Point) :
    (reducedRawProgram P Q).wires ⊆ reducedResetWires := by
  rw [reducedRawProgram,initializedRawProgram]
  apply seq_support
  · intro w hw
    rw [physicalPointLookup] at hw
    have h := directPointLookup_support
      (firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13) P)
      (List.range' 855 16) (List.range' 519 16) 836 hw
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
    simp only [reducedResetWires,reducedPhaseWires,List.mem_append,List.mem_range,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · exact schedule_support _ _ _ (fun _ h => h)
theorem preparedRawTrial_support (Q : Point) :
    (preparedRawTrial Q).wires ⊆ reducedResetWires := by
  intro w hw
  simp only [preparedRawTrial,AdaptiveCircuit.wires,List.mem_append] at hw
  rcases hw with hw | hw
  · exact List.mem_append_right _ (reducedPhasePrepare_support hw)
  · rcases hw with hw | hw
    · simp only [circuitWires,gateWires,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at hw
      subst w
      exact List.mem_append_left _ (List.mem_range.mpr (by decide))
    · rw [reducedRawFourierProgram,modularWires_seq] at hw
      exact hw.elim (fun h => reducedRawProgram_support G Q h)
        (fun h => List.mem_append_right _ (reducedFourierProgram_support h))
theorem rawTrialResetWires_length (Q : Point) : (rawTrialResetWires Q).length≤1303 := by
  have hs : (rawTrialResetWires Q).toFinset ⊆ reducedResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (preparedRawTrial_support Q (by simpa [rawTrialResetWires] using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (show (rawTrialResetWires Q).Nodup from List.nodup_dedup _)] at hc
  simpa only [reducedResetWires,reducedPhaseWires,List.length_append,List.length_range,List.length_range'] using hc

theorem rawRepeatedProgram_qubitCount (Q : Point) : (rawRepeatedProgram Q).qubitCount≤1303 := by
  have hs : (rawRepeatedProgram Q).wires.dedup.toFinset ⊆ reducedResetWires.toFinset := by
    intro w hw
    have hm : w∈(resetRawTrial Q).wires := repeatWindowProgram_support _ 56 (by simpa [rawRepeatedProgram] using hw)
    rw [resetRawTrial,modularWires_seq] at hm
    apply List.mem_toFinset.mpr
    rcases hm with hm | hm
    · exact preparedRawTrial_support Q hm
    · have hh := resetRegister_support (rawTrialResetWires Q) hm
      exact preparedRawTrial_support Q (by simpa [rawTrialResetWires] using hh)
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,reducedResetWires,reducedPhaseWires,
    List.length_append,List.length_range,List.length_range'] using hc
end
end ShorECDLP.Paper2607_13816
