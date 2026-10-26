import ShorECDLP.Submission.«2607_13816».Challenge.Reindex
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
def leftCoefficients (j a : Nat) : PointCoeff := coefficients (oddCoefficient j a) 0
def rightCoefficients (j a : Nat) : PointCoeff := coefficients 0 (oddCoefficient j a)
def coefficientAt (i : Fin 983040) : PointCoeff :=
  if i.val < 65536 then firstWindowCoefficients i.val
  else if i.val < 557056 then
    leftCoefficients (14 - (i.val - 65536) / 32768) ((i.val - 65536) % 32768)
  else rightCoefficients (12 - (i.val - 557056) / 32768) ((i.val - 557056) % 32768)

def coefficientTable : List PointCoeff := List.ofFn coefficientAt

theorem coefficientTable_length : coefficientTable.length = 983040 := by
  exact List.length_ofFn

def firstIndex (a : Fin 65536) : Fin 983040 := ⟨a.val, by omega⟩
def leftIndex (j : Fin 15) (a : Fin 32768) : Fin 983040 :=
  ⟨65536 + (14-j.val)*32768+a.val, by omega⟩
def rightIndex (j : Fin 13) (a : Fin 32768) : Fin 983040 :=
  ⟨557056 + (12-j.val)*32768+a.val, by omega⟩

theorem coefficientAt_first (a : Fin 65536) :
    coefficientAt (firstIndex a) = firstWindowCoefficients a.val := by
  simp [coefficientAt, firstIndex, a.isLt]

theorem coefficientAt_left (j : Fin 15) (a : Fin 32768) :
    coefficientAt (leftIndex j a) = leftCoefficients j.val a.val := by
  have h1 : ¬(leftIndex j a).val < 65536 := by dsimp [leftIndex]; omega
  have h2 : (leftIndex j a).val < 557056 := by dsimp [leftIndex]; omega
  have hj : 14 - ((leftIndex j a).val - 65536) / 32768 = j.val := by dsimp [leftIndex]; omega
  have ha : ((leftIndex j a).val - 65536) % 32768 = a.val := by dsimp [leftIndex]; omega
  simp [coefficientAt, h1, h2, hj, ha]

theorem coefficientAt_right (j : Fin 13) (a : Fin 32768) :
    coefficientAt (rightIndex j a) = rightCoefficients j.val a.val := by
  have h1 : ¬(rightIndex j a).val < 65536 := by dsimp [rightIndex]; omega
  have h2 : ¬(rightIndex j a).val < 557056 := by dsimp [rightIndex]; omega
  have hj : 12 - ((rightIndex j a).val - 557056) / 32768 = j.val := by dsimp [rightIndex]; omega
  have ha : ((rightIndex j a).val - 557056) % 32768 = a.val := by dsimp [rightIndex]; omega
  simp [coefficientAt, h1, h2, hj, ha]

def windowIndex : OddWindow → Fin 32768 → Fin 983040
  | .left j => leftIndex j
  | .right j => rightIndex j

theorem coefficientAt_window (w : OddWindow) (a : Fin 32768) :
    coefficientAt (windowIndex w a) = oddWindowCoefficients w a := by
  cases w with
  | left j => exact coefficientAt_left j a
  | right j => exact coefficientAt_right j a

def sharedCoordinateProgram (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  reindexCompiled (windowIndex w) (coordinateProgram start)

theorem sharedCoordinateProgram_run (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (sharedCoordinateProgram w start) (readConstant coefficientAt Q) history =
      (signedLookupCoordinateProgram (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).run := by
  unfold sharedCoordinateProgram reindexCompiled compiledRun
  rw [reindexStraight_instantiate, readConstant_reindex _ _ _ Q (coefficientAt_window w)]
  exact coordinateProgram_run w start Q hQ history

theorem sharedCoordinateProgram_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (sharedCoordinateProgram w start) (readConstant coefficientAt Q) history =
      (signedLookupCoordinateProgram (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).tCount := by
  unfold sharedCoordinateProgram reindexCompiled compiledTCount
  rw [reindexStraight_instantiate, readConstant_reindex _ _ _ Q (coefficientAt_window w)]
  exact coordinateProgram_tCount w start Q hQ history

def sharedFirstWindowProgram (start : Nat) : Straight 983040 start (start+65551) :=
  reindexStraight firstIndex (firstWindowProgram start)

theorem sharedFirstWindowProgram_instantiate (start : Nat) (Q : Point) (history : Fin start → Bool) :
    (sharedFirstWindowProgram start).instantiate (readConstant coefficientAt Q) history =
      (firstWindowProgram start).instantiate (readConstant (fun i => firstWindowCoefficients i.val) Q) history := by
  unfold sharedFirstWindowProgram
  rw [reindexStraight_instantiate, readConstant_reindex _ _ _ Q coefficientAt_first]

end ShorECDLP.Paper2607_13816.ChallengeMigration
