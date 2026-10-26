import ShorECDLP.Submission.«2607_13816».Challenge.Horner
import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareSubtract

/-! Fixed copied-control squaring and its measured inverse, followed by the
source square/subtract/uncompute composition. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def squareAddProgram (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  let body := modularAddProgram n start input acc bits p copied c r t f
  prependCompiled [.CX q copied] (appendCompiled body ⟨0, literalProgram [.CX q copied]⟩)

theorem squareAddProgram_run (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (squareAddProgram n start input acc bits p q copied c r t f) read history =
      (squareAdd input acc bits p q copied c r t f).run := by
  unfold squareAddProgram squareAdd
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact modularAddProgram_run n _ input acc bits p copied c r t f hd hk hpos read history
  · intro h
    exact literalProgram_run _ read h

theorem squareAddProgram_tCount (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (squareAddProgram n start input acc bits p q copied c r t f) read history =
      (squareAdd input acc bits p q copied c r t f).tCount := by
  unfold squareAddProgram squareAdd
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact modularAddProgram_tCount n _ input acc bits p copied c r t f hd hk hpos read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def squareSubProgram (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  let body := modularSubProgram n start input acc bits p copied c r t f
  prependCompiled [.CX q copied] (appendCompiled body ⟨0, literalProgram [.CX q copied]⟩)

theorem squareSubProgram_run (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (squareSubProgram n start input acc bits p q copied c r t f) read history =
      (squareSub input acc bits p q copied c r t f).run := by
  unfold squareSubProgram squareSub
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact modularSubProgram_run n _ input acc bits p copied c r t f hd hk hpos read history
  · intro h
    exact literalProgram_run _ read h

theorem squareSubProgram_tCount (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (squareSubProgram n start input acc bits p q copied c r t f) read history =
      (squareSub input acc bits p q copied c r t f).tCount := by
  unfold squareSubProgram squareSub
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact modularSubProgram_tCount n _ input acc bits p copied c r t f hd hk hpos read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def squareProgram (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  match controls with
  | [] => ⟨0, .done⟩
  | q::qs =>
    let before := squareProgram n start qs input acc bits p copied c r t f
    let after := if qs = [] then squareAddProgram n (start+before.1) input acc bits p q copied c r t f else
      let dbl := modularDoubleProgram n (start+before.1) acc input bits p f r t c
      appendCompiled dbl (squareAddProgram n (start+before.1+dbl.1) input acc bits p q copied c r t f)
    appendCompiled before after

theorem squareProgram_run (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (squareProgram n start controls input acc bits p copied c r t f) read history =
      (squareLoop controls input acc bits p copied c r t f).run := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold squareProgram squareLoop
    dsimp only
    apply appendCompiled_run_eq
    · exact ih start history
    · intro h
      split
      · exact squareAddProgram_run n _ input acc bits p q copied c r t f hd hk hpos read h
      · apply appendCompiled_run_eq
        · exact modularDoubleProgram_run n _ acc input bits p f r t c hd.symm hk read h
        · intro h
          exact squareAddProgram_run n _ input acc bits p q copied c r t f hd hk hpos read h

theorem squareProgram_tCount (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (squareProgram n start controls input acc bits p copied c r t f) read history =
      (squareLoop controls input acc bits p copied c r t f).tCount := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold squareProgram squareLoop
    dsimp only
    apply appendCompiled_tCount_eq
    · exact ih start history
    · intro h
      split
      · exact squareAddProgram_tCount n _ input acc bits p q copied c r t f hd hk hpos read h
      · apply appendCompiled_tCount_eq
        · exact modularDoubleProgram_tCount n _ acc input bits p f r t c hd.symm hk read h
        · intro h
          exact squareAddProgram_tCount n _ input acc bits p q copied c r t f hd hk hpos read h

def squareInverseProgram (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  match controls with
  | [] => ⟨0, .done⟩
  | q::qs =>
    let sub := squareSubProgram n start input acc bits p q copied c r t f
    let after := if qs = [] then ⟨0, Straight.done⟩ else
      let half := modularHalveProgram n (start+sub.1) acc input bits p f r t c
      appendCompiled half (squareInverseProgram n (start+sub.1+half.1) qs input acc bits p copied c r t f)
    appendCompiled sub after

theorem squareInverseProgram_run (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (squareInverseProgram n start controls input acc bits p copied c r t f) read history =
      (squareLoopInverse controls input acc bits p copied c r t f).run := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold squareInverseProgram squareLoopInverse
    dsimp only
    apply appendCompiled_run_eq
    · exact squareSubProgram_run n _ input acc bits p q copied c r t f hd hk hpos read history
    · intro h
      split
      · rfl
      · apply appendCompiled_run_eq
        · exact modularHalveProgram_run n _ acc input bits p f r t c hd.symm hk read h
        · intro h
          exact ih _ h

theorem squareInverseProgram_tCount (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (squareInverseProgram n start controls input acc bits p copied c r t f) read history =
      (squareLoopInverse controls input acc bits p copied c r t f).tCount := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold squareInverseProgram squareLoopInverse
    dsimp only
    apply appendCompiled_tCount_eq
    · exact squareSubProgram_tCount n _ input acc bits p q copied c r t f hd hk hpos read history
    · intro h
      split
      · rfl
      · apply appendCompiled_tCount_eq
        · exact modularHalveProgram_tCount n _ acc input bits p f r t c hd.symm hk read h
        · intro h
          exact ih _ h

def squareSubtractProgram (n start : Nat) (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  let sq := squareProgram n start y y acc correction p copied c r t f
  let sub := modularSubProgram n (start+sq.1) acc x modulus p q copied f r c
  appendCompiled sq (appendCompiled sub
    (squareInverseProgram n (start+sq.1+sub.1) y y acc modulus p copied c r t f))

theorem squareSubtractProgram_run (n start : Nat) (x y acc : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire)
    (hx : x.length = acc.length) (hy : y.length = acc.length)
    (hk : correction.length = acc.length) (hm : modulus.length = acc.length)
    (hpos : 0 < acc.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (squareSubtractProgram n start x y acc correction modulus p q copied c r t f) read history =
      (squareSubtract x y acc correction modulus p q copied c r t f).run := by
  unfold squareSubtractProgram squareSubtract
  dsimp only
  apply appendCompiled_run_eq
  · exact squareProgram_run n _ y y acc correction p copied c r t f hy hk hpos read history
  · intro h
    apply appendCompiled_run_eq
    · exact modularSubProgram_run n _ acc x modulus p q copied f r c hx.symm
        (hm.trans hx.symm) (hx.symm ▸ hpos) read h
    · intro h
      exact squareInverseProgram_run n _ y y acc modulus p copied c r t f hy hm hpos read h

theorem squareSubtractProgram_tCount (n start : Nat) (x y acc : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire)
    (hx : x.length = acc.length) (hy : y.length = acc.length)
    (hk : correction.length = acc.length) (hm : modulus.length = acc.length)
    (hpos : 0 < acc.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (squareSubtractProgram n start x y acc correction modulus p q copied c r t f) read history =
      (squareSubtract x y acc correction modulus p q copied c r t f).tCount := by
  unfold squareSubtractProgram squareSubtract
  dsimp only
  apply appendCompiled_tCount_eq
  · exact squareProgram_tCount n _ y y acc correction p copied c r t f hy hk hpos read history
  · intro h
    apply appendCompiled_tCount_eq
    · exact modularSubProgram_tCount n _ acc x modulus p q copied f r c hx.symm
        (hm.trans hx.symm) (hx.symm ▸ hpos) read h
    · intro h
      exact squareInverseProgram_tCount n _ y y acc modulus p copied c r t f hy hm hpos read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
