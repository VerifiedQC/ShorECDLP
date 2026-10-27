import ShorECDLP.Submission.«2607_13816».Challenge.InPlaceSlots
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] divisionProgram multiplicationProgram
attribute [local irreducible] zeroDivisionProgram zeroMultiplicationProgram modularNegateProgram squareSubtractProgram coordinateProgram

theorem fig15ZeroPrepare_length : fig15ZeroPrepare.length=1022 := by
  rw [circuit_length_primitive,fig15ZeroPrepare_primitive]; rfl

theorem fig15ZeroRestore_length : fig15ZeroRestore.length=1022 := by
  rw [circuit_length_primitive,fig15ZeroRestore_primitive]; rfl

theorem zeroDivisionProgram_slots (n start : Nat) :
    (zeroDivisionProgram n start).2.gateSlots≤676000000 := by
  have h := divisionProgram_slots n start
  simp only [zeroDivisionProgram,surroundCompiled_slots,fig15ZeroPrepare_length,fig15ZeroRestore_length]
  omega

theorem zeroMultiplicationProgram_slots (n start : Nat) :
    (zeroMultiplicationProgram n start).2.gateSlots≤676000000 := by
  have h := multiplicationProgram_slots n start
  simp only [zeroMultiplicationProgram,surroundCompiled_slots,fig15ZeroPrepare_length,fig15ZeroRestore_length]
  omega

theorem xNegateProgram_slots (n start : Nat) :
    (xNegateProgram n start).2.gateSlots≤26370 := by
  have h := modularNegateProgram_slots_le n start (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558 (by simp) (by simp) (by simp)
  simpa only [List.length_range'] using h

theorem pointSquareProgram_slots (n start : Nat) :
    (pointSquareProgram n start).2.gateSlots≤15750663 := by
  exact squareSubtractProgram_slots256 n start _ _ _ _ _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp)

theorem coordinateProgram_slots (start : Nat) :
    (coordinateProgram start).2.gateSlots≤1500000000 := by
  have h := sequenceProgram_slots_le 32768 coordinateSegments
    ([17449459,17502203,676000000,15750663,17449459,676000000,26370,17449459,17502203] : List Nat) (by
      unfold coordinateSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))))
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s
      · intro s; exact zeroDivisionProgram_slots _ s
      · intro s; exact pointSquareProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact zeroMultiplicationProgram_slots _ s
      · intro s; exact xNegateProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold coordinateProgram
  omega


theorem reindexCompiled_slots {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    (reindexCompiled f p).2.gateSlots=p.2.gateSlots := by
  exact reindexStraight_gateSlots f p.2

attribute [local irreducible] reindexCompiled sharedCoordinateProgram sharedYNegateProgram
  placedBatchProgram batchedWindowCore batchedWindowPrepared actualBatchedWindow actualFirstWindow
  actualLeftWindows actualRightWindows batchedOuterPlan

theorem sharedCoordinateProgram_slots (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).2.gateSlots≤1500000000 := by
  simp only [sharedCoordinateProgram,reindexCompiled_slots]
  exact coordinateProgram_slots start

theorem sharedYNegateProgram_slots (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).2.gateSlots≤26372 := by
  simp only [sharedYNegateProgram,reindexCompiled_slots]
  exact yNegateProgram_slots_le start

theorem batchedWindowCore_slots (w : OddWindow) (start : Nat) :
    (batchedWindowCore w start).2.gateSlots≤2683845980 := by
  have h := sequenceProgram_slots_le 983040 (batchedWindowSegments w)
    ([1500000000,26372,1183793236,26372] : List Nat) (by
      unfold batchedWindowSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
      · intro s; exact sharedCoordinateProgram_slots w s
      · intro s; exact sharedYNegateProgram_slots w s
      · intro s; exact placedBatchProgram_slots w s
      · intro s; exact sharedYNegateProgram_slots w s) start
  simpa only [batchedWindowCore,List.sum_cons,List.sum_nil] using h

theorem batchedWindowPrepared_slots (w : OddWindow) (start : Nat) :
    (batchedWindowPrepared w start).2.gateSlots≤3000000000 := by
  have h := batchedWindowCore_slots w start
  simp only [batchedWindowPrepared,surroundCompiled_slots,signedAddressCircuit_length,
    pointLookupAddress,List.length_range']
  omega

theorem actualBatchedWindow_slots (w : OddWindow) (start : Nat) :
    ((actualBatchedWindow w).program start).gateSlots≤3000000000 := by
  simp only [actualBatchedWindow,closedWindow,shiftStraight_gateSlots,relabelStraight_slots]
  exact batchedWindowPrepared_slots w 0

theorem batchedOuterPlan_windowSlots :
    ∀ w ∈ batchedOuterPlan.left.toList ++ batchedOuterPlan.right.toList,
      ∀ start, (w.program start).gateSlots≤3000000000 := by
  intro w hw start
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray,
    actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨i,rfl⟩) | ⟨i,rfl⟩
  · exact (actualFirstWindow_slots start).trans (by decide)
  · exact actualBatchedWindow_slots _ start
  · exact actualBatchedWindow_slots _ start

/-- Syntactic slots of the actual 56-round program. This counts every fixed
correction slot; it does not assert physical validity, success, or wire support. -/
theorem batchedOuterPlan_slots (start : Nat) :
    (batchedOuterPlan.repeat 56 start).gateSlots≤5000000000000 := by
  exact (batchedOuterPlan.repeat_slots_le 3000000000 batchedOuterPlan_windowSlots 56 start).trans (by decide)


end ShorECDLP.Paper2607_13816.ChallengeMigration
