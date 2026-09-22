import ShorECDLP.Submission.«2607_13816».Window.RawCounts
import ShorECDLP.Submission.«2607_13816».Window.RawBankReuse
import ShorECDLP.Submission.«2607_13816».Window.StreamHistory

/-! The existing streaming schedule now calls the current raw arithmetic, including
measured inversion. These are support, reset and measurement certificates for this
actual program. Its full sampling equivalence is not established here. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq preparedRawProgram physicalPointLookup

/-- Weighted raw addition on the single reused bank, with the current field operations. -/
def streamRawCall (P : Point) (j : Nat) : AdaptiveCircuit :=
  preparedRawProgram (fun _ a => (oddWindowX P j a).val) (fun _ a => (oddWindowY P j a).val) 0

def streamRawLeftCalls (P Q : Point) : List AdaptiveCircuit :=
  physicalPointLookup (firstWindowTable (axisWindowOffset P 16 + axisWindowOffset Q 13)
    ((2^(16*15)) • P)) :: (List.range 15).reverse.map (streamRawCall P)

def streamRawRightCalls (Q : Point) : List AdaptiveCircuit :=
  (List.range 13).reverse.map (streamRawCall Q)

/-- Same high-to-low schedule, replacing every corrected call with the current raw call.
Each axis has its own Fourier history; each block measures and clears the reused bank. -/
def streamRawTrial (P Q : Point) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary [.X 836] .done).seq
    (streamAxis (streamRawLeftCalls P Q) List.nil
      (streamAxis (streamRawRightCalls Q) List.nil (AdaptiveCircuit.unitary [.X 836] .done)))

theorem streamRawCall_support (P : Point) (j : Nat) :
    (streamRawCall P j).wires ⊆ streamAllocation :=
  preparedRawProgram_support _ _ 0

private theorem control_support :
    (AdaptiveCircuit.unitary [.X 836] .done).wires ⊆ streamAllocation := by
  intro w hw
  simp [AdaptiveCircuit.wires,circuitWires,gateWires] at hw
  subst w
  exact List.mem_append_left _ (List.mem_range.mpr (by decide))

theorem streamRawTrial_support (P Q : Point) :
    (streamRawTrial P Q).wires ⊆ streamAllocation := by
  intro w hw
  rw [streamRawTrial,modularWires_seq] at hw
  rcases hw with hw | hw
  · exact control_support hw
  · apply streamAxis_support _ List.nil _ ?_ ?_ hw
    · intro c hc
      simp only [streamRawLeftCalls,List.mem_cons,List.mem_map] at hc
      rcases hc with rfl | ⟨j,hj,rfl⟩
      · exact streamPointLookup_support _
      · exact streamRawCall_support _ _
    · apply streamAxis_support _ List.nil _ ?_ control_support
      intro c hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      exact streamRawCall_support _ _

theorem streamRawTrial_qubitCount (P Q : Point) :
    (streamRawTrial P Q).qubitCount ≤ 855 := by
  have hs : (streamRawTrial P Q).wires.dedup.toFinset ⊆ streamAllocation.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (streamRawTrial_support P Q (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,streamAllocation,streamAddress,List.length_append,
    List.length_range,List.length_range'] using hc

private theorem control_clean (b : InstrumentBranch)
    (hb : b ∈ (AdaptiveCircuit.unitary [.X 836] .done).run) (ψ : State)
    (hin : SupportedOn (Clean streamAddress) ψ) :
    SupportedOn (Clean streamAddress) (b.kraus ψ) := by
  intro s hs w hw
  apply (AdaptiveCircuit.unitary [.X 836] .done).branch_frame w false _ b hb ψ _ s hs
  · intro hm
    simp [AdaptiveCircuit.wires,circuitWires,gateWires] at hm
    subst w
    simp [streamAddress] at hw
  · intro t ht
    exact hin t ht w hw

/-- Address reset holds for every retained branch, not only successful inputs. -/
theorem streamRawTrial_clean (P Q : Point) (b : InstrumentBranch)
    (hb : b ∈ (streamRawTrial P Q).run) (ψ : State)
    (hin : SupportedOn (Clean streamAddress) ψ) :
    SupportedOn (Clean streamAddress) (b.kraus ψ) := by
  rw [streamRawTrial,AdaptiveCircuit.run_seq] at hb
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hm
  exact streamAxis_clean _ List.nil _
    (fun d hd φ hφ => streamAxis_clean _ List.nil _ control_clean d hd φ hφ)
    c hc _ (control_clean a ha ψ hin)

/-- All raw arithmetic measurements and all 464 Fourier measurements are retained. -/
theorem streamRawTrial_measurements (P Q : Point) :
    (streamRawTrial P Q).measurementCount =
      ((streamRawLeftCalls P Q).map AdaptiveCircuit.measurementCount).sum +
      ((streamRawRightCalls Q).map AdaptiveCircuit.measurementCount).sum + 464 := by
  rw [streamRawTrial,modularMeasurements_seq,streamAxis_measurements,streamAxis_measurements]
  simp only [streamRawLeftCalls,streamRawRightCalls,List.length_cons,List.length_map,
    List.length_reverse,List.length_range,AdaptiveCircuit.measurementCount]
  omega

/-- Concrete measurement count includes measured inversion at all 28 raw additions. -/
theorem streamRawTrial_measurementCount (P Q : Point) :
    (streamRawTrial P Q).measurementCount = 847701655 := by
  have hc : ∀ R j, (streamRawCall R j).measurementCount = 30272702 := by
    intro R j
    exact (preparedRawProgram_counts _ _ 0).2.2
  rw [streamRawTrial_measurements]
  simp only [streamRawLeftCalls, streamRawRightCalls, List.map_cons, List.map_map,
    List.sum_cons, Function.comp_def, hc]
  have hl := (physicalPointLookup_resources
    (firstWindowTable (axisWindowOffset P 16 + axisWindowOffset Q 13)
      ((2^(16*15)) • P))).2.1
  rw [hl]
  norm_num

/-- Concrete raw block relocation uses the same table and all measurement histories. -/
theorem streamRawCall_bank_run (P : Point) (j k : Nat) (hk : k ≠ 0)
    (prior : List Bool) (ψ : State)
    (hin : SupportedOn (Clean (streamAddress ++ List.range' (windowBankStart k) 16)) ψ) :
    ((measuredRawBankBlock (fun a => (oddWindowX P j a).val) (fun a => (oddWindowY P j a).val) k prior).run.map
      (fun b => (b.history,b.kraus ψ))) =
    ((measuredStreamBlock (streamRawCall P j) prior).run.map
      (fun b => (b.history,b.kraus ψ))) :=
  measuredRawBankBlock_run _ _ k hk prior ψ hin
/-- Reusing one raw arithmetic block remains exact through the remaining adaptive
axis and arbitrary tail; this does not identify the global sampling distribution. -/
theorem streamRawCall_continuation_reuse (P : Point) (j k : Nat) (hk : k ≠ 0)
    (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit)
    (ψ : State)
    (hin : SupportedOn (Clean (streamAddress ++ List.range' (windowBankStart k) 16)) ψ) :
    ((streamAxis (streamRawCall P j :: calls) prior tail).run.map
      (fun b => (b.history, b.kraus ψ))) =
      (((measuredStreamBlock (streamRawCall P j) prior).relabel (streamBankPerm k)).run.flatMap
        (fun b => (streamAxis calls (b.history.reverse.take 16 ++ prior) tail).run.map
          (fun next => (b.history ++ next.history, next.kraus (b.kraus ψ))))) := by
  apply streamAxis_cons_reuse_run _ calls prior tail k hk _ ψ hin
  intro w hw
  have hs := streamRawCall_support P j hw
  simpa only [streamAllocation, List.mem_append, List.mem_range] using hs

end
end ShorECDLP.Paper2607_13816
