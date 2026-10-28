import ShorECDLP.Submission.«2607_13816».Challenge.EEACoreSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem phaseCoreGates_support (r : PhaseUpdateRegisters) :
    circuitWires (phaseCoreGates r) ⊆ r.allWires := by
  intro w hw
  simp only [phaseCoreGates,circuitWires,List.flatMap_cons,List.flatMap_nil,gateWires,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hw
  simp only [PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false]
  tauto

theorem phaseInverseCoreGates_support (r : PhaseUpdateRegisters) :
    circuitWires (phaseInverseCoreGates r) ⊆ r.allWires := by
  intro w hw
  simp only [phaseInverseCoreGates,circuitWires,List.flatMap_cons,List.flatMap_nil,gateWires,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hw
  simp only [PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false]
  tauto

theorem phaseSegments_support (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (core : Circuit) (hcore : circuitWires core ⊆ r.epochWires shift) :
    ∀ seg ∈ phaseSegments n r shift core, ∀ start,
      straightWires (seg start).2 ⊆ r.epochWires shift := by
  have hq cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthQ
    (r.withShiftEpoch shift).zeroQ (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hr cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthRPrime
    (r.withShiftEpoch shift).zeroRPrime (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hs cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthS
    (r.withShiftEpoch shift).zeroS (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hx : circuitWires [.X shift] ⊆ r.epochWires shift := by
    simp [circuitWires,gateWires,PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.withShiftEpoch,PhaseUpdateRegisters.allWires]
  intro seg hseg start
  simp only [phaseSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hq _ | exact hr _ | exact hs _ | simpa only [literalProgram_support] using hx | simpa only [literalProgram_support] using hcore

theorem phaseProgram_support (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    straightWires (phaseProgram n start r shift).2 ⊆ r.epochWires shift := by
  exact sequenceProgram_support n _ _ (phaseSegments_support n r shift _ (phaseCoreGates_support _)) start

theorem phaseInverseProgram_support (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    straightWires (phaseInverseProgram n start r shift).2 ⊆ r.epochWires shift := by
  exact sequenceProgram_support n _ _ (phaseSegments_support n r shift _ (phaseInverseCoreGates_support _)) start
end ShorECDLP.Paper2607_13816.ChallengeMigration
