import ShorECDLP.Submission.«2607_13816».Challenge.ModularNegate
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerInverse

/-! Fixed measured arithmetic schedules for modular subtraction, doubling, halving,
and Horner multiplication in both directions. All control flow depends only on
submitted wire lists; measurement outcomes only enter the compiled record gates.
Execution and T-count equalities preserve the original source stage ordering. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def modularSubProgram (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  let add := gidneyProgram n start acc (input.take (acc.length-1)) modulus f c r t
  let test := uncontrolledCompareProgram n (start+add.1) acc input p c r t f
  prependCompiled (controlledCompareLT acc input q c f)
    (appendCompiled add (appendCompiled test ⟨0, literalProgram (controlledSubCarry input acc q c f)⟩))

attribute [local irreducible] gidneyProgram uncontrolledCompareProgram

theorem modularSubProgram_run (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (hd : input.length = acc.length)
    (hk : modulus.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (modularSubProgram n start input acc modulus p q c r t f) read history =
      (controlledModularSub input acc modulus p q c r t f).run := by
  have ht : acc.length = (input.take (acc.length-1)).length+1 := by
    rw [List.length_take, hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold modularSubProgram controlledModularSub
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact gidneyProgram_run n _ acc _ modulus f c r t ht hk read history
  · intro h
    apply appendCompiled_run_eq
    · exact uncontrolledCompareProgram_run n _ acc input p c r t f hd.symm read h
    · intro h
      exact literalProgram_run _ read h

theorem modularSubProgram_tCount (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (hd : input.length = acc.length)
    (hk : modulus.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (modularSubProgram n start input acc modulus p q c r t f) read history =
      (controlledModularSub input acc modulus p q c r t f).tCount := by
  have ht : acc.length = (input.take (acc.length-1)).length+1 := by
    rw [List.length_take, hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold modularSubProgram controlledModularSub
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact gidneyProgram_tCount n _ acc _ modulus f c r t ht hk read history
  · intro h
    apply appendCompiled_tCount_eq
    · exact uncontrolledCompareProgram_tCount n _ acc input p c r t f hd.symm read h
    · intro h
      simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]


def modularDoubleProgram (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  match acc with
  | [] => ⟨0, .done⟩
  | a::rest =>
    let test := uncontrolledCompareProgram n start (a::rest) dirty p c r t f
    let add := gidneyProgram n (start+test.1) (a::rest) (dirty.take rest.length) bits f c r t
    prependCompiled (doublingShift (a::rest) f) (appendCompiled test (appendCompiled add ⟨0, literalProgram ([.CX a f])⟩))

theorem modularDoubleProgram_run (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : acc.length = dirty.length)
    (hk : bits.length = acc.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (modularDoubleProgram n start acc dirty bits p c r t f) read history =
      (modularDouble acc dirty bits p c r t f).run := by
  cases acc with
  | nil => rfl
  | cons a rest =>
    have ht : (a::rest).length = (dirty.take rest.length).length+1 := by
      rw [List.length_take, ← hd, List.length_cons, Nat.min_eq_left (by omega)]
    unfold modularDoubleProgram modularDouble
    dsimp only
    apply prependCompiled_run_eq
    apply appendCompiled_run_eq
    · exact uncontrolledCompareProgram_run n _ (a::rest) dirty p c r t f hd read history
    · intro h
      apply appendCompiled_run_eq
      · exact gidneyProgram_run n _ (a::rest) _ bits f c r t ht hk read h
      · intro h
        exact literalProgram_run _ read h

theorem modularDoubleProgram_tCount (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : acc.length = dirty.length)
    (hk : bits.length = acc.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (modularDoubleProgram n start acc dirty bits p c r t f) read history =
      (modularDouble acc dirty bits p c r t f).tCount := by
  cases acc with
  | nil => rfl
  | cons a rest =>
    have ht : (a::rest).length = (dirty.take rest.length).length+1 := by
      rw [List.length_take, ← hd, List.length_cons, Nat.min_eq_left (by omega)]
    unfold modularDoubleProgram modularDouble
    dsimp only
    apply prependCompiled_tCount_eq
    apply appendCompiled_tCount_eq
    · exact uncontrolledCompareProgram_tCount n _ (a::rest) dirty p c r t f hd read history
    · intro h
      apply appendCompiled_tCount_eq
      · exact gidneyProgram_tCount n _ (a::rest) _ bits f c r t ht hk read h
      · intro h
        simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def modularHalveProgram (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  match acc with
  | [] => ⟨0, .done⟩
  | a::rest =>
    let add := gidneyProgram n start (a::rest) (dirty.take rest.length) bits f c r t
    let test := uncontrolledCompareProgram n (start+add.1) (a::rest) dirty p c r t f
    prependCompiled ([.CX a f]) (appendCompiled add (appendCompiled test ⟨0, literalProgram ((doublingShift (a::rest) f).adjoint)⟩))

theorem modularHalveProgram_run (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : acc.length = dirty.length)
    (hk : bits.length = acc.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (modularHalveProgram n start acc dirty bits p c r t f) read history =
      (modularHalve acc dirty bits p c r t f).run := by
  cases acc with
  | nil => rfl
  | cons a rest =>
    have ht : (a::rest).length = (dirty.take rest.length).length+1 := by
      rw [List.length_take, ← hd, List.length_cons, Nat.min_eq_left (by omega)]
    unfold modularHalveProgram modularHalve
    dsimp only
    apply prependCompiled_run_eq
    apply appendCompiled_run_eq
    · exact gidneyProgram_run n _ (a::rest) _ bits f c r t ht hk read history
    · intro h
      apply appendCompiled_run_eq
      · exact uncontrolledCompareProgram_run n _ (a::rest) dirty p c r t f hd read h
      · intro h
        exact literalProgram_run _ read h

theorem modularHalveProgram_tCount (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : acc.length = dirty.length)
    (hk : bits.length = acc.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (modularHalveProgram n start acc dirty bits p c r t f) read history =
      (modularHalve acc dirty bits p c r t f).tCount := by
  cases acc with
  | nil => rfl
  | cons a rest =>
    have ht : (a::rest).length = (dirty.take rest.length).length+1 := by
      rw [List.length_take, ← hd, List.length_cons, Nat.min_eq_left (by omega)]
    unfold modularHalveProgram modularHalve
    dsimp only
    apply prependCompiled_tCount_eq
    apply appendCompiled_tCount_eq
    · exact gidneyProgram_tCount n _ (a::rest) _ bits f c r t ht hk read history
    · intro h
      apply appendCompiled_tCount_eq
      · exact uncontrolledCompareProgram_tCount n _ (a::rest) dirty p c r t f hd read h
      · intro h
        simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def hornerProgram (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  match controls with
  | [] => ⟨0, .done⟩
  | q::qs =>
    let before := hornerProgram n start qs input acc bits p c r t f
    let after := if qs = [] then modularAddProgram n (start+before.1) input acc bits p q c r t f else
      let dbl := modularDoubleProgram n (start+before.1) acc input bits p f r t c
      appendCompiled dbl (modularAddProgram n (start+before.1+dbl.1) input acc bits p q c r t f)
    appendCompiled before after

theorem hornerProgram_run (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (hornerProgram n start controls input acc bits p c r t f) read history =
      (hornerMul controls input acc bits p c r t f).run := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold hornerProgram hornerMul
    dsimp only
    apply appendCompiled_run_eq
    · exact ih start history
    · intro h
      split
      · exact modularAddProgram_run n _ input acc bits p q c r t f hd hk hpos read h
      · apply appendCompiled_run_eq
        · exact modularDoubleProgram_run n _ acc input bits p f r t c hd.symm hk read h
        · intro h
          exact modularAddProgram_run n _ input acc bits p q c r t f hd hk hpos read h

theorem hornerProgram_tCount (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (hornerProgram n start controls input acc bits p c r t f) read history =
      (hornerMul controls input acc bits p c r t f).tCount := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold hornerProgram hornerMul
    dsimp only
    apply appendCompiled_tCount_eq
    · exact ih start history
    · intro h
      split
      · exact modularAddProgram_tCount n _ input acc bits p q c r t f hd hk hpos read h
      · apply appendCompiled_tCount_eq
        · exact modularDoubleProgram_tCount n _ acc input bits p f r t c hd.symm hk read h
        · intro h
          exact modularAddProgram_tCount n _ input acc bits p q c r t f hd hk hpos read h

def hornerInverseProgram (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  match controls with
  | [] => ⟨0, .done⟩
  | q::qs =>
    let sub := modularSubProgram n start input acc bits p q c r t f
    let after := if qs = [] then ⟨0, Straight.done⟩ else
      let half := modularHalveProgram n (start+sub.1) acc input bits p f r t c
      appendCompiled half (hornerInverseProgram n (start+sub.1+half.1) qs input acc bits p c r t f)
    appendCompiled sub after

theorem hornerInverseProgram_run (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (hornerInverseProgram n start controls input acc bits p c r t f) read history =
      (hornerMulInverse controls input acc bits p c r t f).run := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold hornerInverseProgram hornerMulInverse
    dsimp only
    apply appendCompiled_run_eq
    · exact modularSubProgram_run n _ input acc bits p q c r t f hd hk hpos read history
    · intro h
      split
      · rfl
      · apply appendCompiled_run_eq
        · exact modularHalveProgram_run n _ acc input bits p f r t c hd.symm hk read h
        · intro h
          exact ih _ h

theorem hornerInverseProgram_tCount (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hd : input.length = acc.length)
    (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (hornerInverseProgram n start controls input acc bits p c r t f) read history =
      (hornerMulInverse controls input acc bits p c r t f).tCount := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold hornerInverseProgram hornerMulInverse
    dsimp only
    apply appendCompiled_tCount_eq
    · exact modularSubProgram_tCount n _ input acc bits p q c r t f hd hk hpos read history
    · intro h
      split
      · rfl
      · apply appendCompiled_tCount_eq
        · exact modularHalveProgram_tCount n _ acc input bits p f r t c hd.symm hk read h
        · intro h
          exact ih _ h

end ShorECDLP.Paper2607_13816.ChallengeMigration
