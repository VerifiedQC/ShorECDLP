import ShorECDLP.Submission.«2607_13816».Challenge.Reset
import ShorECDLP.Submission.«2607_13816».Window.StreamTightSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Secp256k1

/-- Wire 837 is absent from the raw arithmetic and initial point load.
Wire 838 remains: the initial load stores its infinity flag there.
The old lookup address/sign wires 839–854 are relocated by
`windowAddressPerm` to the reused streaming bank 855–870. This equality
connects the fixed reset list to the existing gate-level support proof. -/
theorem resetWires_eq_streamTightAllocation : resetWires = streamTightAllocation := by
  simp only [resetWires, streamTightAllocation, streamAddress, List.append_assoc, List.singleton_append]

theorem rawTrial_support_resetWires (P Q : Point) :
    (streamRawTrial P Q).wires ⊆ resetWires := by
  rw [resetWires_eq_streamTightAllocation]
  exact streamRawTrial_tight_support P Q

theorem resetWires_avoids_837 : (837 : Wire) ∉ resetWires := by
  simp [resetWires]

theorem resetWires_avoids_oldAddress (w : Wire) (hlo : 839 ≤ w) (hhi : w < 855) :
    w ∉ resetWires := by
  simp only [resetWires, List.mem_append, List.mem_range, List.mem_singleton,
    List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem rawTrial_avoids_oldAddress (P Q : Point) (w : Wire)
    (hlo : 839 ≤ w) (hhi : w < 855) : w ∉ (streamRawTrial P Q).wires :=
  fun hw => resetWires_avoids_oldAddress w hlo hhi (rawTrial_support_resetWires P Q hw)

theorem rawTrial_avoids_resetGap (P Q : Point) : (837 : Wire) ∉ (streamRawTrial P Q).wires :=
  fun hw => resetWires_avoids_837 (rawTrial_support_resetWires P Q hw)

theorem resetWires_nodup : resetWires.Nodup := by
  rw [resetWires, List.nodup_append, List.nodup_append]
  refine ⟨⟨List.nodup_range, List.nodup_singleton _, ?_⟩, List.nodup_range', ?_⟩
  · intro w hw v hv he
    subst v
    simp only [List.mem_range, List.mem_singleton] at hw hv
    dsimp only [Wire] at *
    omega
  · intro w hw v hv he
    subst v
    simp only [List.mem_append, List.mem_range, List.mem_singleton, List.mem_range'_1] at hw hv
    dsimp only [Wire] at *
    omega

/-- A reset of the fixed support restores the complete zero state, including
unused gaps, which remain zero by the circuit frame theorem. -/
theorem reset_supported_program_zero (c : AdaptiveCircuit)
    (hc : c.wires ⊆ resetWires) (b : InstrumentBranch)
    (hb : b ∈ (c.seq (measureResetWithCorrection resetWires (fun _ => []))).run) :
    SupportedOn (fun s => s = zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  have hsupport : (c.seq (measureResetWithCorrection resetWires (fun _ => []))).wires ⊆ resetWires := by
    intro w hw
    rcases (modularWires_seq _ _ w).mp hw with hw | hw
    · exact hc hw
    · exact resetRegister_support _ hw
  have hclean : SupportedOn (Clean resetWires) (b.kraus (ket zeroBasisState)) := by
    rw [AdaptiveCircuit.run_seq] at hb
    obtain ⟨before, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨after, ha, rfl⟩ := List.mem_map.mp hb
    exact resetRegister_clean _ resetWires_nodup after ha (before.kraus (ket zeroBasisState))
  intro s hs
  funext w
  by_cases hw : w ∈ resetWires
  · exact hclean s hs w hw
  · exact AdaptiveCircuit.branch_frame _ w false (fun h => hw (hsupport h)) b hb
      (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs

theorem rawTrial_fixedReset_zero (P Q : Point) (b : InstrumentBranch)
    (hb : b ∈ ((streamRawTrial P Q).seq
      (measureResetWithCorrection resetWires (fun _ => []))).run) :
    SupportedOn (fun s => s = zeroBasisState) (b.kraus (ket zeroBasisState)) :=
  reset_supported_program_zero _ (rawTrial_support_resetWires P Q) b hb

end ShorECDLP.Paper2607_13816.ChallengeMigration
