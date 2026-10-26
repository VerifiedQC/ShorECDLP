import ShorECDLP.Submission.«2607_13816».Challenge.ModularNegate
import ShorECDLP.Submission.«2607_13816».Challenge.WindowModular

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

def yNegateProgram (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  negativeNegateProgram 32768 start (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558

def signedFieldProgram (field : PointField) (start : Nat) :
    (count : Nat) × Straight 32768 start (start+count) :=
  let before := yNegateProgram start
  let lookup := fieldLookupAddProgram field (List.range' 580 256) (start+before.1)
  let after := yNegateProgram (start+before.1+lookup.1)
  appendCompiled before (appendCompiled lookup after)

theorem yNegateProgram_run (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    compiledRun (yNegateProgram start) read history =
      (negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
        (constantBits 256 ShorECDLP.p) 854 559 560 561 558).run := by
  exact negativeNegateProgram_run 32768 start _ _ _ _ _ _ _ _
    (by simp) (by rw [constantBits_length, List.length_range']) (by simp) read history

theorem signedFieldProgram_run (w : OddWindow) (field : PointField) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (signedFieldProgram field start) (readConstant (oddWindowCoefficients w) Q) history =
      (signedPointLookupY (fun l => fieldValue (windowPoint Q w l) field)).run := by
  unfold signedFieldProgram
  dsimp only
  unfold signedPointLookupY signedLookupModularAddProgram
  simp only [List.length_range']
  rw [adaptive_seq_assoc]
  apply appendCompiled_run_eq
  · exact yNegateProgram_run start _ history
  · intro h
    apply appendCompiled_run_eq
    · exact fieldLookupAddProgram_run w field _ _ Q hQ (by simp) h
    · intro h
      exact yNegateProgram_run _ _ h

theorem fieldLookupAddProgram_tCount_source (w : OddWindow) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hQ : order • Q = 0) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) (readConstant (oddWindowCoefficients w) Q) history =
      (lookupModularAddProgram (fun l => fieldValue (windowPoint Q w l) field)
        pointLookupAddress pointLookupPath (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount := by
  rw [fieldLookupAddProgram_tCount w field acc start Q hQ hl history]
  simp only [lookupModularAddProgram, adaptive_tCount_seq]
  rw [tableLookupProgram_tCount _ _ _ _ (by decide) (by decide)]
  rfl

theorem yNegateProgram_tCount (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    compiledTCount (yNegateProgram start) read history =
      (negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
        (constantBits 256 ShorECDLP.p) 854 559 560 561 558).tCount := by
  exact negativeNegateProgram_tCount 32768 start _ _ _ _ _ _ _ _
    (by simp) (by rw [constantBits_length, List.length_range']) (by simp) read history

theorem signedFieldProgram_tCount (w : OddWindow) (field : PointField) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (signedFieldProgram field start) (readConstant (oddWindowCoefficients w) Q) history =
      (signedPointLookupY (fun l => fieldValue (windowPoint Q w l) field)).tCount := by
  unfold signedFieldProgram
  dsimp only
  unfold signedPointLookupY signedLookupModularAddProgram
  simp only [List.length_range']
  rw [adaptive_seq_assoc]
  apply appendCompiled_tCount_eq
  · exact yNegateProgram_tCount start _ history
  · intro h
    apply appendCompiled_tCount_eq
    · exact fieldLookupAddProgram_tCount_source w field _ _ Q hQ (by simp) h
    · intro h
      exact yNegateProgram_tCount _ _ h

theorem signedFieldProgram_records (field : PointField) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ compiledRun (signedFieldProgram field start) read history) :
    b.history.length = (signedFieldProgram field start).1 := by
  have h := straight_history_length (signedFieldProgram field start).2 read history b hb
  simpa using h

end ShorECDLP.Paper2607_13816.ChallengeMigration
