import ShorECDLP.Challenge.Decoder

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Challenge

/-- Positions for the legacy 256/208-bit, 56-trial layout with fixed 854-wire
reset. Bounds below certify index arithmetic, not correspondence to a compiled
arithmetic program; that correspondence is a separate migration obligation. -/
def legacyDecoderParams : DecoderParams := ⟨256, 208, by decide, by decide, by decide, by decide⟩

def legacyTrialStride : Nat := 847702509

def fourierPosition (r : Fin 56) (block : Fin 29) (bit : Fin 16) : Nat :=
  r.val * legacyTrialStride + 65535 + block.val * 30272718 + bit.val

theorem fourierPosition_before_reset (r : Fin 56) (block : Fin 29) (bit : Fin 16) :
    r.val * legacyTrialStride ≤ fourierPosition r block bit ∧
    fourierPosition r block bit < r.val * legacyTrialStride + 847701655 := by
  dsimp [fourierPosition]; omega

theorem fourierPosition_lt_total (r : Fin 56) (block : Fin 29) (bit : Fin 16) :
    fourierPosition r block bit < 47471340504 := by
  dsimp [fourierPosition, legacyTrialStride]; omega

def leftPosition (r : Fin 56) (i : Fin 256) : Nat :=
  fourierPosition r ⟨i.val / 16, by omega⟩ ⟨i.val % 16, by omega⟩

def rightPosition (r : Fin 56) (i : Fin 208) : Nat :=
  fourierPosition r ⟨16 + i.val / 16, by omega⟩ ⟨i.val % 16, by omega⟩

theorem leftPosition_strictMono (r : Fin 56) : StrictMono (leftPosition r) := by
  intro a b hab
  dsimp [leftPosition, fourierPosition]
  have ha := a.isLt
  have hb := b.isLt
  change a.val < b.val at hab
  omega

theorem rightPosition_strictMono (r : Fin 56) : StrictMono (rightPosition r) := by
  intro a b hab
  dsimp [rightPosition, fourierPosition]
  change a.val < b.val at hab
  omega

theorem leftPosition_lt_rightPosition (r : Fin 56) (a : Fin 256) (b : Fin 208) :
    leftPosition r a < rightPosition r b := by
  dsimp [leftPosition, rightPosition, fourierPosition]
  omega

def legacyTrialPositions (r : Fin 56) : TrialPositions legacyDecoderParams :=
  ⟨Vector.ofFn (leftPosition r), Vector.ofFn (rightPosition r)⟩

def legacyDecodeLayout : DecodeLayout :=
  ⟨.wrappedShift, legacyDecoderParams, List.ofFn legacyTrialPositions,
    by rw [List.length_ofFn]⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration
