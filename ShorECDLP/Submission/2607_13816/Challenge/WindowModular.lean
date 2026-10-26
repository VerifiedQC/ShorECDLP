import ShorECDLP.Submission.«2607_13816».Challenge.ModularAdd
import ShorECDLP.Submission.«2607_13816».Challenge.OddFields

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

def fieldLookupAddProgram (field : PointField) (acc : List Wire) (start : Nat) :
    (count : Nat) × Straight 32768 start (start+count) :=
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  appendCompiled ⟨32767, fieldLoadProgram field start⟩
    (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)

attribute [local irreducible] fieldLoadProgram modularAddProgram

theorem fieldLookupAddProgram_run (w : OddWindow) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hQ : order • Q = 0) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledRun (fieldLookupAddProgram field acc start) (readConstant (oddWindowCoefficients w) Q) history =
      (lookupModularAddProgram (fun l => fieldValue (windowPoint Q w l) field)
        pointLookupAddress pointLookupPath (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).run := by
  let read := readConstant (oddWindowCoefficients w) Q
  let lookup := tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (windowPoint Q w l) field))
    pointLookupAddress 836 pointLookupPath
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  let target := controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558
  have addRun : ∀ h, (add.2.instantiate read h).run = target.run := by
    intro h
    exact modularAddProgram_run 32768 _ _ acc _ _ _ _ _ _ _
      (by simp [hl]) (by simp [secp256k1ReductionConstantBits, hl]) (by omega) read h
  have suffixRun : ∀ h, compiledRun
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩) read h =
      (target.seq lookup).run := by
    intro h
    rw [appendCompiled_run add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩ read h lookup
      (fun h => fieldLoadProgram_run w field _ Q hQ h),
      AdaptiveCircuit.run_seq, addRun h, ← AdaptiveCircuit.run_seq]
  change compiledRun
    (appendCompiled ⟨32767, fieldLoadProgram field start⟩
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)) read history = _
  rw [appendCompiled_run _ _ _ _ (target.seq lookup) suffixRun,
    AdaptiveCircuit.run_seq, fieldLoadProgram_run w field start Q hQ history,
    ← AdaptiveCircuit.run_seq]
  rw [← adaptive_seq_assoc]
  rfl

theorem fieldLookupAddProgram_records (field : PointField) (acc : List Wire) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ compiledRun (fieldLookupAddProgram field acc start) read history) :
    b.history.length = (fieldLookupAddProgram field acc start).1 := by
  have h := straight_history_length (fieldLookupAddProgram field acc start).2 read history b hb
  simpa using h

theorem fieldLookupAddProgram_tCount (w : OddWindow) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hQ : order • Q = 0) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) (readConstant (oddWindowCoefficients w) Q) history =
      229369 + (controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount + 229369 := by
  let read := readConstant (oddWindowCoefficients w) Q
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  let target := controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558
  have addT : ∀ h, (add.2.instantiate read h).tCount = target.tCount := by
    intro h
    exact modularAddProgram_tCount 32768 _ _ acc _ _ _ _ _ _ _
      (by simp [hl]) (by simp [secp256k1ReductionConstantBits, hl]) (by omega) read h
  have suffixT : ∀ h, compiledTCount
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩) read h =
      target.tCount + 229369 := by
    intro h
    rw [appendCompiled_tCount add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩ read h 229369
      (fun h => fieldLoadProgram_tCount w field _ Q hQ h), addT h]
  change compiledTCount
    (appendCompiled ⟨32767, fieldLoadProgram field start⟩
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)) read history = _
  rw [appendCompiled_tCount _ _ _ _ (target.tCount+229369) suffixT,
    fieldLoadProgram_tCount w field start Q hQ history]
  exact (Nat.add_assoc _ _ _).symm

theorem fig14LookupX_compiled (w : OddWindow) (field : PointField) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (fieldLookupAddProgram field (List.range' 263 256) start)
      (readConstant (oddWindowCoefficients w) Q) history =
      (fig14LookupX (fun l => fieldValue (windowPoint Q w l) field)).run := by
  exact fieldLookupAddProgram_run w field _ start Q hQ (by simp) history

end ShorECDLP.Paper2607_13816.ChallengeMigration
