import ShorECDLP.Submission.«2607_13816».Challenge.Dual
import ShorECDLP.Submission.«2607_13816».Challenge.VChain
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def equalityProgram (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) : (count : Nat) × Straight n start (start+count) :=
  let body := vchainProgram n start register flag scratch
  prependCompiled (zeroMask register value)
    (appendCompiled body ⟨0, literalProgram (zeroMask register value)⟩)
theorem equalityProgram_run (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (equalityProgram n start register value flag scratch) read history =
      (computeEqConstAdaptive register value flag scratch).run := by
  unfold equalityProgram computeEqConstAdaptive
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact vchainProgram_run n start register flag scratch read history
  · intro h
    exact literalProgram_run _ read h

theorem equalityProgram_tCount (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (equalityProgram n start register value flag scratch) read history =
      (computeEqConstAdaptive register value flag scratch).tCount := by
  unfold equalityProgram computeEqConstAdaptive
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact vchainProgram_tCount n start register flag scratch read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def toggleEqualityProgram (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) : (count : Nat) × Straight n start (start+count) :=
  let first := equalityProgram n start register value flag scratch
  appendCompiled first (prependCompiled [.CCX root flag acc]
    (equalityProgram n (start+first.1) register value flag scratch))
theorem toggleEqualityProgram_run (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (toggleEqualityProgram n start root register value acc flag scratch) read history =
      (toggleEqConstUnderControlAdaptive root register value acc flag scratch).run := by
  unfold toggleEqualityProgram toggleEqConstUnderControlAdaptive
  dsimp only
  apply appendCompiled_run_eq
  · exact equalityProgram_run n start register value flag scratch read history
  · intro h
    apply prependCompiled_run_eq
    exact equalityProgram_run n _ register value flag scratch read h

theorem toggleEqualityProgram_tCount (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (toggleEqualityProgram n start root register value acc flag scratch) read history =
      (toggleEqConstUnderControlAdaptive root register value acc flag scratch).tCount := by
  unfold toggleEqualityProgram toggleEqConstUnderControlAdaptive
  dsimp only
  apply appendCompiled_tCount_eq
  · exact equalityProgram_tCount n start register value flag scratch read history
  · intro h
    apply prependCompiled_tCount_eq
    exact equalityProgram_tCount n _ register value flag scratch read h

def intervalFirstProgram (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) : (count : Nat) × Straight n start (start+count) :=
  let body := rippleFirstProgram n start mode acc target addend carry scratch
  prependCompiled (endpointLeafToggle topSpecial label rightTop rightControl acc)
    (appendCompiled body ⟨0, literalProgram (endpointLeafToggle topSpecial label leftTop leftControl acc)⟩)
theorem intervalFirstProgram_run (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl) read history =
      (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).run := by
  unfold intervalFirstProgram intervalFirstLeafAdaptive
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact rippleFirstProgram_run n start mode acc target addend carry scratch read history
  · intro h
    exact literalProgram_run _ read h

theorem intervalFirstProgram_tCount (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl) read history =
      (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).tCount := by
  unfold intervalFirstProgram intervalFirstLeafAdaptive
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact rippleFirstProgram_tCount n start mode acc target addend carry scratch read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def intervalSecondProgram (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) : (count : Nat) × Straight n start (start+count) :=
  let body := rippleSecondProgram n start mode acc target addend carry scratch
  prependCompiled (endpointLeafToggle topSpecial label leftTop leftControl acc)
    (appendCompiled body ⟨0, literalProgram (endpointLeafToggle topSpecial label rightTop rightControl acc)⟩)
theorem intervalSecondProgram_run (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl) read history =
      (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).run := by
  unfold intervalSecondProgram intervalSecondLeafAdaptive
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact rippleSecondProgram_run n start mode acc target addend carry scratch read history
  · intro h
    exact literalProgram_run _ read h

theorem intervalSecondProgram_tCount (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl) read history =
      (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).tCount := by
  unfold intervalSecondProgram intervalSecondLeafAdaptive
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact rippleSecondProgram_tCount n start mode acc target addend carry scratch read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def topFirstProgram (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) : (count : Nat) × Straight n start (start+count) :=
  let first := toggleEqualityProgram n start rightRoot rightRegister value acc flag scratch
  let cell := rippleFirstProgram n (start+first.1) mode acc target addend carry work
  appendCompiled first (appendCompiled cell
    (toggleEqualityProgram n (start+first.1+cell.1) leftRoot leftRegister value acc flag scratch))
theorem topFirstProgram_run (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot) read history =
      (topSpecialFirstLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).run := by
  unfold topFirstProgram topSpecialFirstLeafAdaptive
  dsimp only
  apply appendCompiled_run_eq
  · exact toggleEqualityProgram_run n start rightRoot rightRegister value acc flag scratch read history
  · intro h
    apply appendCompiled_run_eq
    · exact rippleFirstProgram_run n _ mode acc target addend carry work read h
    · intro h
      exact toggleEqualityProgram_run n _ leftRoot leftRegister value acc flag scratch read h

theorem topFirstProgram_tCount (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot) read history =
      (topSpecialFirstLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).tCount := by
  unfold topFirstProgram topSpecialFirstLeafAdaptive
  dsimp only
  apply appendCompiled_tCount_eq
  · exact toggleEqualityProgram_tCount n start rightRoot rightRegister value acc flag scratch read history
  · intro h
    apply appendCompiled_tCount_eq
    · exact rippleFirstProgram_tCount n _ mode acc target addend carry work read h
    · intro h
      exact toggleEqualityProgram_tCount n _ leftRoot leftRegister value acc flag scratch read h

def topSecondProgram (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) : (count : Nat) × Straight n start (start+count) :=
  let first := toggleEqualityProgram n start leftRoot leftRegister value acc flag scratch
  let cell := rippleSecondProgram n (start+first.1) mode acc target addend carry work
  appendCompiled first (appendCompiled cell
    (toggleEqualityProgram n (start+first.1+cell.1) rightRoot rightRegister value acc flag scratch))
theorem topSecondProgram_run (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot) read history =
      (topSpecialSecondLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).run := by
  unfold topSecondProgram topSpecialSecondLeafAdaptive
  dsimp only
  apply appendCompiled_run_eq
  · exact toggleEqualityProgram_run n start leftRoot leftRegister value acc flag scratch read history
  · intro h
    apply appendCompiled_run_eq
    · exact rippleSecondProgram_run n _ mode acc target addend carry work read h
    · intro h
      exact toggleEqualityProgram_run n _ rightRoot rightRegister value acc flag scratch read h

theorem topSecondProgram_tCount (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot) read history =
      (topSpecialSecondLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).tCount := by
  unfold topSecondProgram topSpecialSecondLeafAdaptive
  dsimp only
  apply appendCompiled_tCount_eq
  · exact toggleEqualityProgram_tCount n start leftRoot leftRegister value acc flag scratch read history
  · intro h
    apply appendCompiled_tCount_eq
    · exact rippleSecondProgram_tCount n _ mode acc target addend carry work read h
    · intro h
      exact toggleEqualityProgram_tCount n _ rightRoot rightRegister value acc flag scratch read h

def traversalFirstProgram (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    (count : Nat) × Straight n start (start+count) :=
  dualProgram n .dec (fun label right left cursor =>
    intervalFirstProgram n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label)
      carry scratch label right left) tree rightRoot leftRoot rightPaths leftPaths start
theorem traversalFirstProgram_run (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) read history =
      (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).run := by
  unfold traversalFirstProgram intervalFirstTraversalAdaptive
  apply dualProgram_run
  intro label right left cursor h
  exact intervalFirstProgram_run n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left read h

theorem traversalFirstProgram_tCount (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) read history =
      (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).tCount := by
  unfold traversalFirstProgram intervalFirstTraversalAdaptive
  apply dualProgram_tCount
  intro label right left cursor h
  exact intervalFirstProgram_tCount n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left read h

def traversalSecondProgram (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    (count : Nat) × Straight n start (start+count) :=
  dualProgram n .inc (fun label right left cursor =>
    intervalSecondProgram n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label)
      carry scratch label right left) tree rightRoot leftRoot rightPaths leftPaths start
theorem traversalSecondProgram_run (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) read history =
      (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).run := by
  unfold traversalSecondProgram intervalSecondTraversalAdaptive
  apply dualProgram_run
  intro label right left cursor h
  exact intervalSecondProgram_run n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left read h

theorem traversalSecondProgram_tCount (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) read history =
      (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).tCount := by
  unfold traversalSecondProgram intervalSecondTraversalAdaptive
  apply dualProgram_tCount
  intro label right left cursor h
  exact intervalSecondProgram_tCount n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
