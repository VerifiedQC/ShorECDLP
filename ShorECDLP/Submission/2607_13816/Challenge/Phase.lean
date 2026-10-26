import ShorECDLP.Submission.«2607_13816».Challenge.Sequence
import ShorECDLP.Submission.«2607_13816».Challenge.VChain
import ShorECDLP.Submission.«2607_13816».EEA.PhaseUpdate
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
def phaseCoreGates (registers : PhaseUpdateRegisters) : Circuit :=
  [.X registers.zeroRPrime,
    .CCX registers.zeroQ registers.zeroRPrime registers.condition,
    .X registers.zeroRPrime,
    .CX registers.sign registers.temporary,
    .CX registers.phase1 registers.temporary,
    .CCX registers.condition registers.temporary registers.phase2,
    .CX registers.phase1 registers.temporary,
    .CX registers.sign registers.temporary,
    .CCX registers.condition registers.phase2 registers.sign,
    .X registers.zeroRPrime,
    .CCX registers.zeroQ registers.zeroRPrime registers.condition,
    .X registers.zeroRPrime,
    .CX registers.zeroS registers.phase1,
    .CX registers.zeroS registers.phase2]

def phaseInverseCoreGates (registers : PhaseUpdateRegisters) : Circuit :=
  [.CX registers.zeroS registers.phase2,
    .CX registers.zeroS registers.phase1,
    .X registers.zeroRPrime,
    .CCX registers.zeroQ registers.zeroRPrime registers.condition,
    .X registers.zeroRPrime,
    .CCX registers.condition registers.phase2 registers.sign,
    .CX registers.sign registers.temporary,
    .CX registers.phase1 registers.temporary,
    .CCX registers.condition registers.temporary registers.phase2,
    .CX registers.phase1 registers.temporary,
    .CX registers.sign registers.temporary,
    .X registers.zeroRPrime,
    .CCX registers.zeroQ registers.zeroRPrime registers.condition,
    .X registers.zeroRPrime]

def phaseSources (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit) : List AdaptiveCircuit :=
  let inner := r.withShiftEpoch shift
  let a := mcxVChainAdaptive inner.lengthQ inner.zeroQ inner.equalityScratch
  let b := mcxVChainAdaptive inner.lengthRPrime inner.zeroRPrime inner.equalityScratch
  let c := mcxVChainAdaptive inner.lengthS inner.zeroS inner.equalityScratch
  let x := AdaptiveCircuit.unitary [.X shift] .done
  ([a, b, x, c, x, .unitary core .done, x, c, x, b, a] : List AdaptiveCircuit)

def phaseSegments (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit) : List (FixedSegment n) :=
  let inner := r.withShiftEpoch shift
  let a := fun start => vchainProgram n start inner.lengthQ inner.zeroQ inner.equalityScratch
  let b := fun start => vchainProgram n start inner.lengthRPrime inner.zeroRPrime inner.equalityScratch
  let c := fun start => vchainProgram n start inner.lengthS inner.zeroS inner.equalityScratch
  let x : FixedSegment n := fun _ => ⟨0, literalProgram [.X shift]⟩
  ([a, b, x, c, x, (fun _ => ⟨0, literalProgram core⟩), x, c, x, b, a] : List (FixedSegment n))
theorem phaseSegments_run (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit)
    (read : ConstantBit n → Bool) :
    List.Forall₂ (fun p source => ∀ start history, compiledRun (p start) read history = source.run)
      (phaseSegments n r shift core) (phaseSources r shift core) := by
  unfold phaseSegments phaseSources
  dsimp only
  repeat' apply List.Forall₂.cons
  all_goals first | exact List.Forall₂.nil | (intro start history)
  all_goals first | exact vchainProgram_run n start _ _ _ read history | exact literalProgram_run _ read history

theorem phaseSegments_tCount (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit)
    (read : ConstantBit n → Bool) :
    List.Forall₂ (fun p source => ∀ start history, compiledTCount (p start) read history = source.tCount)
      (phaseSegments n r shift core) (phaseSources r shift core) := by
  unfold phaseSegments phaseSources
  dsimp only
  repeat' apply List.Forall₂.cons
  all_goals first | exact List.Forall₂.nil | (intro start history)
  all_goals first | exact vchainProgram_tCount n start _ _ _ read history | simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

theorem phaseSources_forward (r : PhaseUpdateRegisters) (shift : Wire) :
    sequenceCircuit (phaseSources r shift (phaseCoreGates (r.withShiftEpoch shift))) = phaseUpdateEpochAdaptive r shift := by
  let inner := r.withShiftEpoch shift
  let a := mcxVChainAdaptive inner.lengthQ inner.zeroQ inner.equalityScratch
  let b := mcxVChainAdaptive inner.lengthRPrime inner.zeroRPrime inner.equalityScratch
  let c := mcxVChainAdaptive inner.lengthS inner.zeroS inner.equalityScratch
  let x := AdaptiveCircuit.unitary [.X shift] .done
  let core := AdaptiveCircuit.unitary (phaseCoreGates inner) .done
  change sequenceCircuit [a,b,x,c,x,core,x,c,x,b,a] =
    (((((a.seq b).seq x).seq c).seq x).seq core).seq ((((x.seq c).seq x).seq b).seq a)
  simp only [sequenceCircuit, adaptive_seq_assoc, adaptive_seq_done]

theorem phaseSources_inverse (r : PhaseUpdateRegisters) (shift : Wire) :
    sequenceCircuit (phaseSources r shift (phaseInverseCoreGates (r.withShiftEpoch shift))) = phaseUpdateEpochInverseAdaptive r shift := by
  let inner := r.withShiftEpoch shift
  let a := mcxVChainAdaptive inner.lengthQ inner.zeroQ inner.equalityScratch
  let b := mcxVChainAdaptive inner.lengthRPrime inner.zeroRPrime inner.equalityScratch
  let c := mcxVChainAdaptive inner.lengthS inner.zeroS inner.equalityScratch
  let x := AdaptiveCircuit.unitary [.X shift] .done
  let core := AdaptiveCircuit.unitary (phaseInverseCoreGates inner) .done
  change sequenceCircuit [a,b,x,c,x,core,x,c,x,b,a] =
    (((((a.seq b).seq x).seq c).seq x).seq core).seq ((((x.seq c).seq x).seq b).seq a)
  simp only [sequenceCircuit, adaptive_seq_assoc, adaptive_seq_done]

def phaseProgram (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (phaseSegments n r shift (phaseCoreGates (r.withShiftEpoch shift))) start
theorem phaseProgram_run (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (phaseProgram n start r shift) read history = (phaseUpdateEpochAdaptive r shift).run := by
  unfold phaseProgram
  rw [sequenceProgram_run n _ _ read (phaseSegments_run n r shift _ read), phaseSources_forward]

theorem phaseProgram_tCount (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (phaseProgram n start r shift) read history = (phaseUpdateEpochAdaptive r shift).tCount := by
  unfold phaseProgram
  rw [sequenceProgram_tCount n _ _ read (phaseSegments_tCount n r shift _ read), phaseSources_forward]

def phaseInverseProgram (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (phaseSegments n r shift (phaseInverseCoreGates (r.withShiftEpoch shift))) start
theorem phaseInverseProgram_run (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (phaseInverseProgram n start r shift) read history = (phaseUpdateEpochInverseAdaptive r shift).run := by
  unfold phaseInverseProgram
  rw [sequenceProgram_run n _ _ read (phaseSegments_run n r shift _ read), phaseSources_inverse]

theorem phaseInverseProgram_tCount (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (phaseInverseProgram n start r shift) read history = (phaseUpdateEpochInverseAdaptive r shift).tCount := by
  unfold phaseInverseProgram
  rw [sequenceProgram_tCount n _ _ read (phaseSegments_tCount n r shift _ read), phaseSources_inverse]

end ShorECDLP.Paper2607_13816.ChallengeMigration
