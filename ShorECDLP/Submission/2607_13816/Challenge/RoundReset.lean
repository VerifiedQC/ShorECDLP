import ShorECDLP.Submission.«2607_13816».Challenge.RoundBoundary
import ShorECDLP.Submission.«2607_13816».Challenge.CompleteSupport
import ShorECDLP.Submission.«2607_13816».Window.PhysicalRepetition
import ShorECDLP.Submission.«2607_13816».Challenge.ActualPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] actualFirstSource actualOddSource streamAddress fourierOutcomes Quantum.run batchedOuterPlan actualFirstWindow actualBatchedWindow

theorem batchedResetWires_nodup : batchedResetWires.Nodup := by
  simp only [batchedResetWires,resetWires,List.nodup_append,List.nodup_range,
    List.nodup_range' 1, List.nodup_singleton,true_and]
  simp only [List.mem_append,List.mem_range,List.mem_range'_1,List.mem_singleton]
  repeat' constructor
  all_goals intros; dsimp only [Wire] at *; omega

theorem actualRound_support (start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate read history).wires ⊆ completeBatchedSupport := by
  apply OuterPlan.round_support
  · intro w hw
    simp only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact List.mem_cons_of_mem 837 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))
  · simpa only [batchedOuterPlan,standardOuterPlan] using
      (List.subset_cons_of_subset 837 (List.Subset.refl batchedResetWires))
  · simp [completeBatchedSupport,batchedResetWires,resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_static window _ cursor
    simpa only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

theorem actualRoundTail_clean (b : InstrumentBranch)
    (hb : b ∈ (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection batchedResetWires (fun _ => []))).run) (ψ : State) :
    SupportedOn (Clean batchedResetWires) (b.kraus ψ) := by
  rw [AdaptiveCircuit.run] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  exact resetRegister_clean _ batchedResetWires_nodup c hc _

theorem actualRoundSource_clean (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    SupportedOn (Clean batchedResetWires) (b.kraus (ket zeroBasisState)) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,actualLeftSources_indices,actualRightSources_indices] at hb
  rw [AdaptiveCircuit.run, ← selectedSourceTwoAxes_constant] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  change SupportedOn (Clean batchedResetWires) (c.kraus (Quantum.run [.X 836] (ket zeroBasisState)))
  rw [hx]
  exact actualSourceTwoAxes_supported Q hQ hn leftOddIndices rightOddIndices _ _
    (fun _ _ b hb ψ _ => actualRoundTail_clean b hb ψ) _
    (supportedOn_ket _ _ firstWindowInput_start) c hc

theorem actualCompiledRound_zero_support (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    SupportedOn (fun s => s=zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  intro s hs
  funext w
  by_cases hw : w ∈ batchedResetWires
  · have hb' := hb
    rw [batchedOuterPlan_round_run Q hQ start history] at hb'
    exact actualRoundSource_clean Q hQ hn b hb' s hs w hw
  · by_cases he : w=837
    · subst w
      exact actualCompiledRound_zeroFlag Q hQ hn start history b hb s hs
    · exact AdaptiveCircuit.branch_frame _ w false
        (fun h => (List.mem_cons.mp (actualRound_support start _ history h)).elim he hw)
        b hb (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs

theorem actualCompiledRound_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  supportedZero_scalar _ (actualCompiledRound_zero_support Q hQ hn start history b hb)

theorem actualRoundSource_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  apply actualCompiledRound_zero_branch Q hQ hn 0 Fin.elim0 b
  rwa [batchedOuterPlan_round_run Q hQ]

theorem actualRoundSource_total (Q : Point) (hQ : order • Q=0) :
    (actualRoundSource Q).run.bornMass (ket zeroBasisState)=1 := by
  rw [← batchedOuterPlan_round_run Q hQ 0 Fin.elim0]
  exact AdaptiveCircuit.run_bornMass_eq_one _
    (Straight.instantiate_wellFormed _ _ _ (batchedOuterPlan_round_wellFormed 0)) _ (normSq_ket _)

theorem actualCompiledRepeat_retry_mass (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (count start : Nat) (history : Fin start → Bool) (accept : List Bool → Bool) :
    Instrument.bornMass
      ((((batchedOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run).filter
        (fun b => !repeatWindowFailed (actualRoundSource Q) accept count b.history)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (Instrument.bornMass ((actualRoundSource Q).run.filter (fun b => accept b.history)) (ket zeroBasisState)) count := by
  rw [batchedOuterPlan_repeat_run Q hQ count start history]
  exact repeatWindowSuccess_mass _ accept (actualRoundSource_zero_branch Q hQ hn) (actualRoundSource_total Q hQ) count

theorem actualCompiledRepeat_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (count start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  rw [batchedOuterPlan_repeat_run Q hQ count start history] at hb
  exact repeatWindowProgram_zero _ (actualRoundSource_zero_branch Q hQ hn) count b hb
end ShorECDLP.Paper2607_13816.ChallengeMigration
