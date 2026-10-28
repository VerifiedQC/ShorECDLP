import ShorECDLP.Submission.«2607_13816».Challenge.TaggedTwoAxes
import ShorECDLP.Submission.«2607_13816».Challenge.SourceAxis
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] actualFirstWindow actualBatchedWindow actualFirstSource actualOddSource
attribute [local irreducible] streamAddress fourierOutcomes streamAxis sourceOuterRound measureResetWithCorrection batchedResetWires actualRoundSource selectedIdealTwoAxes

def leftOddIndices : List OddWindow := List.ofFn (fun k : Fin 15 => .left ⟨14-k.val,by omega⟩)
def rightOddIndices : List OddWindow := List.ofFn (fun k : Fin 13 => .right ⟨12-k.val,by omega⟩)

theorem actualLeftSources_indices (Q : Point) : actualLeftSources Q =
    actualFirstSource Q :: leftOddIndices.map (actualOddSource Q) := by
  simp only [actualLeftSources,leftOddIndices,List.map_ofFn,Function.comp_def]
theorem actualRightSources_indices (Q : Point) : actualRightSources Q =
    rightOddIndices.map (actualOddSource Q) := by
  simp only [actualRightSources,rightOddIndices,List.map_ofFn,Function.comp_def]
theorem actualLeftWindows_indices : actualLeftWindows =
    actualFirstWindow :: leftOddIndices.map actualBatchedWindow := by
  simp only [actualLeftWindows,leftOddIndices,List.map_ofFn,Function.comp_def]
theorem actualRightWindows_indices : actualRightWindows =
    rightOddIndices.map actualBatchedWindow := by
  simp only [actualRightWindows,rightOddIndices,List.map_ofFn,Function.comp_def]

theorem unitary_history_filter_mass (g : Circuit) (next : AdaptiveCircuit)
    (accept : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((AdaptiveCircuit.unitary g next).run.filter (fun b => accept b.history)) ψ =
      Instrument.bornMass (next.run.filter (fun b => accept b.history)) (Quantum.run g ψ) := by
  simp only [AdaptiveCircuit.run,List.filter_map,Instrument.bornMass,List.map_map,Function.comp_def]
  rfl

def actualRoundFixedAccept (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  fixedPairAccept (batchedOuterPlan.positions ⟨0,by decide⟩).left.toList
    (batchedOuterPlan.positions ⟨0,by decide⟩).right.toList accept history

private theorem positions_zero {n : Nat} (p : OuterPlan n) :
    (p.positions ⟨0,by decide⟩).left.toList = axisPositions p.left.toList 0 ∧
    (p.positions ⟨0,by decide⟩).right.toList = axisPositions p.right.toList (axisCount p.left.toList) := by
  simp only [OuterPlan.positions,Vector.toList,List.toList_toArray,Nat.zero_mul,Nat.zero_add]
  trivial

private theorem actual_left : batchedOuterPlan.left.toList = actualLeftWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]
private theorem actual_right : batchedOuterPlan.right.toList = actualRightWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]

theorem actualRoundFixedAccept_positions (accept : Nat → Nat → Bool) (history : List Bool) :
    actualRoundFixedAccept accept history =
      fixedPairAccept (axisPositions (actualFirstWindow :: leftOddIndices.map actualBatchedWindow) 0)
        (axisPositions (rightOddIndices.map actualBatchedWindow)
          (axisCount (actualFirstWindow :: leftOddIndices.map actualBatchedWindow))) accept history := by
  rw [actualRoundFixedAccept,(positions_zero batchedOuterPlan).1,(positions_zero batchedOuterPlan).2,
    actual_left,actual_right,actualLeftWindows_indices,actualRightWindows_indices]

/-- Fixed positions of the actual layout select the same event in the actual round and ideal two-axis model. -/
theorem actualRoundSource_fixedPair_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (accept : Nat → Nat → Bool) :
    Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept accept b.history)) (ket zeroBasisState) =
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,unitary_history_filter_mass]
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  rw [hx,actualLeftSources_indices,actualRightSources_indices]
  simp only [actualRoundFixedAccept_positions]
  exact actualSources_fixedPair_mass Q hQ hn leftOddIndices rightOddIndices _ accept


noncomputable def wrappedPairAccept (params : DecoderParams) (Q : Point) (left right : Nat) : Bool := by
  classical
  exact ((fixedCandidates params left right).toList.find? (fun c => decide (c.val • G = Q))).isSome

def actualSingleRoundLayout : DecodeLayout :=
  ⟨.wrappedShift,legacyDecoderParams,[batchedOuterPlan.positions ⟨0,by decide⟩],by decide⟩

theorem wrappedTrial_verified_isSome (params : DecoderParams) (Q : Point)
    (positions : TrialPositions params) (history : List Bool) :
    (verifiedCandidate ⟨.wrappedShift,params,[positions],by simp⟩ Q history).isSome =
      fixedPairAccept positions.left.toList positions.right.toList (wrappedPairAccept params Q) history := by
  classical
  simp only [verifiedCandidate,candidates,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    decodeTrial,trialCandidates,fixedPairAccept]
  cases hl : readWord history positions.left.toList <;>
    cases hr : readWord history positions.right.toList <;>
    simp only [Option.bind_none,Option.bind_some,Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,List.find?_nil,Option.isSome_none,fixedCandidates_take]
  rfl

theorem actualSingleRound_verified_isSome (Q : Point) (history : List Bool) :
    (verifiedCandidate actualSingleRoundLayout Q history).isSome =
      actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) history :=
  wrappedTrial_verified_isSome _ Q _ history

/-- The compiled round's acceptance is evaluated by the protected verifiedCandidate function. -/
theorem actualCompiledRound_verified_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    Instrument.bornMass
      (((batchedOuterPlan.round 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate actualSingleRoundLayout Q b.history).isSome)) (ket zeroBasisState) =
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if wrappedPairAccept legacyDecoderParams Q (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) := by
  rw [batchedOuterPlan_round_run Q hQ 0 Fin.elim0]
  simp only [actualSingleRound_verified_isSome]
  exact actualRoundSource_fixedPair_mass Q hQ hn _
end ShorECDLP.Paper2607_13816.ChallengeMigration
