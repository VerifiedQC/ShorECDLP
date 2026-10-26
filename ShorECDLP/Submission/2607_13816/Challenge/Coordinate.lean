import ShorECDLP.Submission.«2607_13816».Challenge.InPlace
import ShorECDLP.Submission.«2607_13816».Challenge.SignedWindow
import ShorECDLP.Submission.«2607_13816».Challenge.Square
import ShorECDLP.Submission.«2607_13816».Window.SignedCoordinate
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
local instance : NeZero ShorECDLP.p := ⟨by decide⟩
attribute [local irreducible] divisionProgram multiplicationProgram squareSubtractProgram modularNegateProgram
  secp256k1InPlaceDivision secp256k1InPlaceMultiplication

def zeroDivisionProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  surroundCompiled fig15ZeroPrepare fig15ZeroRestore (divisionProgram n start)

theorem zeroDivisionProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (zeroDivisionProgram n start) read history = secp256k1ZeroAllowedDivision.run := by
  unfold zeroDivisionProgram secp256k1ZeroAllowedDivision
  rw [adaptive_seq_assoc]
  exact surroundCompiled_run fig15ZeroPrepare fig15ZeroRestore (divisionProgram n start) secp256k1InPlaceDivision read history (divisionProgram_run n start read history)

theorem zeroDivisionProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (zeroDivisionProgram n start) read history = secp256k1ZeroAllowedDivision.tCount := by
  unfold zeroDivisionProgram secp256k1ZeroAllowedDivision
  rw [adaptive_seq_assoc]
  exact surroundCompiled_tCount fig15ZeroPrepare fig15ZeroRestore (divisionProgram n start) secp256k1InPlaceDivision read history (divisionProgram_tCount n start read history)

def zeroMultiplicationProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  surroundCompiled fig15ZeroPrepare fig15ZeroRestore (multiplicationProgram n start)

theorem zeroMultiplicationProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (zeroMultiplicationProgram n start) read history = secp256k1ZeroAllowedMultiplication.run := by
  unfold zeroMultiplicationProgram secp256k1ZeroAllowedMultiplication
  rw [adaptive_seq_assoc]
  exact surroundCompiled_run fig15ZeroPrepare fig15ZeroRestore (multiplicationProgram n start) secp256k1InPlaceMultiplication read history (multiplicationProgram_run n start read history)

theorem zeroMultiplicationProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (zeroMultiplicationProgram n start) read history = secp256k1ZeroAllowedMultiplication.tCount := by
  unfold zeroMultiplicationProgram secp256k1ZeroAllowedMultiplication
  rw [adaptive_seq_assoc]
  exact surroundCompiled_tCount fig15ZeroPrepare fig15ZeroRestore (multiplicationProgram n start) secp256k1InPlaceMultiplication read history (multiplicationProgram_tCount n start read history)

def xNegateProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  modularNegateProgram n start (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558

theorem xNegateProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (xNegateProgram n start) read history = fig14Negate.run := by
  exact modularNegateProgram_run n start _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) read history

theorem xNegateProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (xNegateProgram n start) read history = fig14Negate.tCount := by
  exact modularNegateProgram_tCount n start _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) read history

def pointSquareProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  squareSubtractProgram n start (List.range' 263 256) (List.range' 580 256) (7::List.range' 8 255)
    secp256k1ReductionConstantBits (constantBits 256 ShorECDLP.p) ShorECDLP.p 836 558 559 561 562 560

theorem pointSquareProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (pointSquareProgram n start) read history = fig14SquareSubtract.run := by
  exact squareSubtractProgram_run n start _ _ _ _ _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) (by simp) read history

theorem pointSquareProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (pointSquareProgram n start) read history = fig14SquareSubtract.tCount := by
  exact squareSubtractProgram_tCount n start _ _ _ _ _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) (by simp) read history


theorem field_negX (P : Point) : fieldValue P .negX = (ShorECDLP.p - fieldValue P .x) % ShorECDLP.p := by
  simp only [fieldValue, ZMod.neg_val']
theorem field_negY (P : Point) : fieldValue P .negY = (ShorECDLP.p - fieldValue P .y) % ShorECDLP.p := by
  simp only [fieldValue, ZMod.neg_val']
theorem field_tripleX (P : Point) : fieldValue P .tripleX = (3 * fieldValue P .x) % ShorECDLP.p := by
  simp only [fieldValue, ZMod.val_mul]
  have h : (3 : ShorECDLP.Fp).val = 3 := by norm_num [ZMod.val_ofNat, ShorECDLP.p]
  rw [h]
theorem field_x_mod (P : Point) : fieldValue P .x % ShorECDLP.p = fieldValue P .x := by
  exact Nat.mod_eq_of_lt (ZMod.val_lt ((pointCoordinates P).2.1))

def coordinateSources (Q : Point) (w : OddWindow) : List AdaptiveCircuit :=
  [fig14LookupX (fun l => fieldValue (windowPoint Q w l) .negX),
   signedPointLookupY (fun l => fieldValue (windowPoint Q w l) .negY),
   secp256k1ZeroAllowedDivision, fig14SquareSubtract,
   fig14LookupX (fun l => fieldValue (windowPoint Q w l) .tripleX),
   secp256k1ZeroAllowedMultiplication, fig14Negate,
   fig14LookupX (fun l => fieldValue (windowPoint Q w l) .x),
   signedPointLookupY (fun l => fieldValue (windowPoint Q w l) .negY)]

theorem coordinateSources_eq (Q : Point) (w : OddWindow) :
    sequenceCircuit (coordinateSources Q w) =
      signedLookupCoordinateProgram (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y) := by
  simp only [coordinateSources, sequenceCircuit, signedLookupCoordinateProgram,
    adaptive_seq_assoc, adaptive_seq_done, field_negX, field_negY, field_tripleX, field_x_mod]

def coordinateSegments : List (FixedSegment 32768) :=
  [fieldLookupAddProgram .negX (List.range' 263 256), signedFieldProgram .negY,
   zeroDivisionProgram 32768, pointSquareProgram 32768,
   fieldLookupAddProgram .tripleX (List.range' 263 256), zeroMultiplicationProgram 32768,
   xNegateProgram 32768, fieldLookupAddProgram .x (List.range' 263 256), signedFieldProgram .negY]

def coordinateProgram (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  sequenceProgram 32768 coordinateSegments start

theorem coordinateProgram_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledRun (coordinateProgram start) (readConstant (oddWindowCoefficients w) Q) history =
      (signedLookupCoordinateProgram (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).run := by
  unfold coordinateProgram
  rw [← coordinateSources_eq]
  apply sequenceProgram_run
  unfold coordinateSegments coordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fig14LookupX_compiled w .negX cursor Q hQ h
  · intro cursor h
    exact signedFieldProgram_run w .negY cursor Q hQ h
  · intro cursor h
    exact zeroDivisionProgram_run 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled w .tripleX cursor Q hQ h
  · intro cursor h
    exact zeroMultiplicationProgram_run 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled w .x cursor Q hQ h
  · intro cursor h
    exact signedFieldProgram_run w .negY cursor Q hQ h

theorem coordinateProgram_tCount (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledTCount (coordinateProgram start) (readConstant (oddWindowCoefficients w) Q) history =
      (signedLookupCoordinateProgram (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).tCount := by
  unfold coordinateProgram
  rw [← coordinateSources_eq]
  apply sequenceProgram_tCount
  unfold coordinateSegments coordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source w .negX _ cursor Q hQ (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount w .negY cursor Q hQ h
  · intro cursor h
    exact zeroDivisionProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source w .tripleX _ cursor Q hQ (by simp) h
  · intro cursor h
    exact zeroMultiplicationProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source w .x _ cursor Q hQ (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount w .negY cursor Q hQ h

end ShorECDLP.Paper2607_13816.ChallengeMigration
