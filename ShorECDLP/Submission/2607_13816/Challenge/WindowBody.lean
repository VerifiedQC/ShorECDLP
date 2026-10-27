import ShorECDLP.Submission.«2607_13816».Challenge.BatchPlacement
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] sharedCoordinateProgram yNegateProgram placedBatchProgram

def sharedYNegateProgram (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  reindexCompiled (windowIndex w) (yNegateProgram start)

noncomputable def windowYNegate : AdaptiveCircuit :=
  negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558

theorem sharedYNegateProgram_run (w : OddWindow) (start : Nat) (read : ConstantBit 983040 → Bool)
    (history : Fin start → Bool) :
    compiledRun (sharedYNegateProgram w start) read history = windowYNegate.run := by
  simp only [sharedYNegateProgram,reindexCompiled,compiledRun,reindexStraight_instantiate]
  exact yNegateProgram_run start _ history

/-- Internal additions only; address preparation and Fourier are outside this list. -/
def batchedWindowSegments (w : OddWindow) : List (FixedSegment 983040) :=
  [sharedCoordinateProgram w, sharedYNegateProgram w, placedBatchProgram w, sharedYNegateProgram w]

noncomputable def batchedWindowSources (Q : Point) (w : OddWindow) : List AdaptiveCircuit :=
  [signedLookupCoordinateProgram (fun l => fieldValue (windowPoint Q w l) .x)
    (fun l => fieldValue (windowPoint Q w l) .y),windowYNegate,placedBatchSource Q w,windowYNegate]

def batchedWindowCore (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  sequenceProgram 983040 (batchedWindowSegments w) start

theorem batchedWindowCore_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledRun (batchedWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (batchedWindowSources Q w)).run := by
  apply sequenceProgram_run
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact sharedCoordinateProgram_run w cursor Q hQ h
  · intro cursor h; exact sharedYNegateProgram_run w cursor _ h
  · intro cursor h; exact placedBatchProgram_run w cursor Q h
  · intro cursor h; exact sharedYNegateProgram_run w cursor _ h

attribute [local irreducible] batchedWindowCore

def batchedWindowPrepared (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  surroundCompiled (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (batchedWindowCore w start)

noncomputable def batchedWindowPreparedSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
    ((sequenceCircuit (batchedWindowSources Q w)).seq
      (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))

theorem batchedWindowPrepared_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledRun (batchedWindowPrepared w start) (readConstant coefficientAt Q) history =
      (batchedWindowPreparedSource Q w).run := by
  exact surroundCompiled_run _ _ _ _ _ _ (batchedWindowCore_run w start Q hQ history)

/-- Address bank is relabeled to the reused 855–870 bank; endpoint storage is disjoint. -/
def actualBatchedWindow (w : OddWindow) : OuterWindow 983040 :=
  closedWindow (relabelStraight (windowAddressPerm 855 (by decide)) (batchedWindowPrepared w 0).2)

theorem actualBatchedWindow_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    (((actualBatchedWindow w).program start).instantiate (readConstant coefficientAt Q) history).run =
      ((batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide))).run := by
  simp only [actualBatchedWindow,closedWindow_run,relabelStraight_instantiate,AdaptiveCircuit.run_relabel]
  exact congrArg (List.map (InstrumentBranch.relabel (windowAddressPerm 855 (by decide))))
    (batchedWindowPrepared_run w 0 Q hQ Fin.elim0)

def actualFirstWindow : OuterWindow 983040 :=
  ⟨65535,fun start => reindexStraight firstIndex (firstLookupProgram start)⟩

theorem actualFirstWindow_run (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    (((actualFirstWindow).program start).instantiate (readConstant coefficientAt Q) history).run =
      (physicalPointLookup (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
        ((2^(16*15)) • G))).run := by
  simp only [actualFirstWindow,reindexStraight_instantiate,
    readConstant_reindex firstIndex _ _ Q coefficientAt_first]
  exact firstLookupProgram_run start Q hQ history

def actualLeftWindows : List (OuterWindow 983040) :=
  actualFirstWindow :: List.ofFn (fun k : Fin 15 => actualBatchedWindow (.left ⟨14-k.val,by omega⟩))
def actualRightWindows : List (OuterWindow 983040) :=
  List.ofFn (fun k : Fin 13 => actualBatchedWindow (.right ⟨12-k.val,by omega⟩))

theorem actualLeftWindows_length : actualLeftWindows.length = 16 := by simp [actualLeftWindows]
theorem actualRightWindows_length : actualRightWindows.length = 13 := by simp [actualRightWindows]
/-- Reset every added endpoint, flag and comparator auxiliary wire as well as the
original round-reset list. Cleanliness before reset remains a semantic obligation. -/
def batchedResetWires : List Wire := resetWires ++ List.range' 1024 2565 ++ List.range' 4102 512

theorem batchedResetWires_length : batchedResetWires.length = 3931 := by
  simp [batchedResetWires,resetWires_length]

def batchedOuterPlan : OuterPlan 983040 :=
  standardOuterPlan ⟨actualLeftWindows.toArray,by simp [actualLeftWindows_length]⟩
    ⟨actualRightWindows.toArray,by simp [actualRightWindows_length]⟩ batchedResetWires

end ShorECDLP.Paper2607_13816.ChallengeMigration
