import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredLengthUpdates
/-!
# Measured end-of-iteration refresh

Both source orders reuse the same physical scratch. Each measured length update
coherently refines the literal strict block, and that block restores all scratch.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem refresh_restrict {a : AdaptiveCircuit} {u : State →ₗ[ℂ] State}
    {P Q : BasisState → Prop} (h : CoherentlyImplementsOn a u P)
    (hp : ∀ s, Q s → P s) : CoherentlyImplementsOn a u Q := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

private theorem refresh_seq
    {a b : AdaptiveCircuit} {u v : Circuit} {P : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) P)
    (hu : HPFree u) (hp : ∀ s, P s → P (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket P _ (hp s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append u v (ket s)).symm

/-- The upper measured update on the shared physical allocation. -/
def measuredEndUpper (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : AdaptiveCircuit :=
  measuredLenUpdateLtUnary n w.k4 w.K4 (r.upperTree w) r.control
    (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry
    (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants

/-- The corresponding literal strict source block. -/
def strictEndUpper (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : Circuit :=
  lenUpdateLtUnary n w.k4 w.K4 (r.upperTree w) r.control
    (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry
    (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants

/-- Shared scratch readiness suffices, for both control values and arbitrary live registers. -/
theorem measuredEndUpper_coherent (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    CoherentlyImplementsOn (measuredEndUpper r n w) (Quantum.run (strictEndUpper r n w))
      (EndIterationReady r) := by
  have hm := measuredLenUpdateLtUnary_coherent n w.k4 w.K4 h.k4_le_K4 (r.upperTree w) r.control
    (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry
    (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants
    (by rw [h.lengthRP_length]; exact h.width_positive)
    (h.constants_length.trans h.lengthRP_length.symm) h.upper
  exact refresh_restrict hm (fun s hs => by
    obtain ⟨hc,hp,_,ht⟩ := h.clean_components4 hs
    exact ⟨hc,hp,ht⟩)

/-- The literal block preserves readiness for the next allocation of shared scratch. -/
theorem strictEndUpper_ready (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w)
    (s : BasisState) (hs : EndIterationReady r s) :
    EndIterationReady r (Classical.run (strictEndUpper r n w) s) :=
  lenUpdateLtUnary_ready r n w h s hs

/-- Every physical branch of the allocated measured update is well formed. -/
theorem measuredEndUpper_wellFormed (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    (measuredEndUpper r n w).WellFormed :=
  measuredLenUpdateLtUnary_wellFormed n w.k4 w.K4 h.k4_le_K4 (r.upperTree w) r.control
    (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry
    (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants
    (h.constants_length.trans h.lengthRP_length.symm) h.upper

/-- The lower measured update on the shared physical allocation. -/
def measuredEndLower (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : AdaptiveCircuit :=
  measuredLenUpdateLrpUnary n w.k5 (w.K5Decode n) (r.lowerTree n w) r.control
    (r.rangeAccumulator w.k5 (w.K5Decode n)) (r.temporary w.k5 (w.K5Decode n)) r.carry
    (r.path w.k5 (w.K5Decode n)) r.work1At r.work2At r.lengthT r.lengthRP r.constants

/-- The corresponding literal strict source block. -/
def strictEndLower (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : Circuit :=
  lenUpdateLrpUnary n w.k5 (w.K5Decode n) (r.lowerTree n w) r.control
    (r.rangeAccumulator w.k5 (w.K5Decode n)) (r.temporary w.k5 (w.K5Decode n)) r.carry
    (r.path w.k5 (w.K5Decode n)) r.work1At r.work2At r.lengthT r.lengthRP r.constants

/-- Shared scratch readiness suffices, for both control values and arbitrary live registers. -/
theorem measuredEndLower_coherent (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    CoherentlyImplementsOn (measuredEndLower r n w) (Quantum.run (strictEndLower r n w))
      (EndIterationReady r) := by
  have hm := measuredLenUpdateLrpUnary_coherent n w.k5 (w.K5Decode n) h.k5_le_decode (r.lowerTree n w) r.control
    (r.rangeAccumulator w.k5 (w.K5Decode n)) (r.temporary w.k5 (w.K5Decode n)) r.carry
    (r.path w.k5 (w.K5Decode n)) r.work1At r.work2At r.lengthT r.lengthRP r.constants
    h.constants_length h.lower
  exact refresh_restrict hm (fun s hs => by
    obtain ⟨hc,hp,_,ht⟩ := h.clean_components5 hs
    exact ⟨hc,hp,ht⟩)

/-- The literal block preserves readiness for the next allocation of shared scratch. -/
theorem strictEndLower_ready (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w)
    (s : BasisState) (hs : EndIterationReady r s) :
    EndIterationReady r (Classical.run (strictEndLower r n w) s) :=
  lenUpdateLrpUnary_ready r n w h s hs

/-- Every physical branch of the allocated measured update is well formed. -/
theorem measuredEndLower_wellFormed (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    (measuredEndLower r n w).WellFormed :=
  measuredLenUpdateLrpUnary_wellFormed n w.k5 (w.K5Decode n) h.k5_le_decode (r.lowerTree n w) r.control
    (r.rangeAccumulator w.k5 (w.K5Decode n)) (r.temporary w.k5 (w.K5Decode n)) r.carry
    (r.path w.k5 (w.K5Decode n)) r.work1At r.work2At r.lengthT r.lengthRP r.constants
    h.constants_length h.lower

/-- Source forward bank swap followed by the two measured length updates. -/
def measuredEndIteration (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : AdaptiveCircuit :=
  .unitary (controlledWorkSwap r.control r.work1 r.work2)
    ((measuredEndUpper r n w).seq (measuredEndLower r n w))

/-- Source inverse order; measurement histories are not reversed. -/
def measuredEndIterationInverse (r : EndIterationRegisters) (n : Nat) (w : EndIterationWindows) : AdaptiveCircuit :=
  (measuredEndLower r n w).seq ((measuredEndUpper r n w).seq
    (.unitary (controlledWorkSwapInverse r.control r.work1 r.work2) .done))

/-- Coherent refinement of the full forward refresh using the original shared allocation. -/
theorem measuredEndIteration_coherent (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    CoherentlyImplementsOn (measuredEndIteration r n w)
      (Quantum.run (swapWorkAndLengthUnaryShared r n w)) (EndIterationReady r) := by
  have hb := refresh_seq (measuredEndUpper_coherent r n w h) (measuredEndLower_coherent r n w h)
    (by simp [strictEndUpper]) (strictEndUpper_ready r n w h)
  have ha := refresh_seq (CoherentlyImplementsOn.unitary
    (controlledWorkSwap r.control r.work1 r.work2) (EndIterationReady r)) hb
    (by simp) (controlledWorkSwap_ready r n w h)
  convert ha using 1
  simp [swapWorkAndLengthUnaryShared,strictEndUpper,strictEndLower,List.append_assoc]

/-- Coherent refinement of the source inverse with fresh measured erasures in its emitted order. -/
theorem measuredEndIterationInverse_coherent (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    CoherentlyImplementsOn (measuredEndIterationInverse r n w)
      (Quantum.run (swapWorkAndLengthUnarySharedInverse r n w)) (EndIterationReady r) := by
  have hb := refresh_seq (measuredEndUpper_coherent r n w h)
    (CoherentlyImplementsOn.unitary (controlledWorkSwapInverse r.control r.work1 r.work2) (EndIterationReady r))
    (by simp [strictEndUpper]) (strictEndUpper_ready r n w h)
  have ha := refresh_seq (measuredEndLower_coherent r n w h) hb
    (by simp [strictEndLower]) (strictEndLower_ready r n w h)
  convert ha using 1
  simp [swapWorkAndLengthUnarySharedInverse,strictEndUpper,strictEndLower,List.append_assoc]
/-- Well-formedness of every forward branch on the shared allocation. -/
theorem measuredEndIteration_wellFormed (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    (measuredEndIteration r n w).WellFormed := by
  have hs := swapWorkAndLengthUnaryShared_wellFormed r n w h
  simp only [swapWorkAndLengthUnaryShared,circuitWellFormed_append] at hs
  exact ⟨hs.1.1,(measuredEndUpper_wellFormed r n w h).seq (measuredEndLower_wellFormed r n w h)⟩

/-- Well-formedness of every inverse branch, without reversing measurements. -/
theorem measuredEndIterationInverse_wellFormed (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    (measuredEndIterationInverse r n w).WellFormed := by
  have hs := swapWorkAndLengthUnarySharedInverse_wellFormed r n w h
  simp only [swapWorkAndLengthUnarySharedInverse,circuitWellFormed_append] at hs
  exact (measuredEndLower_wellFormed r n w h).seq
    ((measuredEndUpper_wellFormed r n w h).seq ⟨hs.2,trivial⟩)

/-- Actual Toffoli cost of the measured upper update with constant reflection retained. -/
theorem measuredEndUpper_toffoli (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    (primitiveResources (measuredEndUpper r n w)).toffoli =
      2*(2*(r.width-2)+2*r.width)+(24*(w.K4+1-w.k4)-16) := by
  have hlabels := r.upperTree_visitLabels w h.k4_le_K4
  rw [UnaryActionTree.visitLabels_inc] at hlabels
  rw [measuredEndUpper, measuredLenUpdateLtUnary_toffoli _ _ _ h.k4_le_K4 _ _ _ _ _ _ _ _ _ _ _
    h.upper.work1Bits.decoder hlabels]
  rw [constMinus_toffoliCount _ _ _ _ (by rw [h.lengthRP_length]; exact h.width_positive)
    (h.constants_length.trans h.lengthRP_length.symm), h.lengthRP_length]
  omega

/-- Actual Toffoli cost of the measured lower update with constant shift retained. -/
theorem measuredEndLower_toffoli (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    (primitiveResources (measuredEndLower r n w)).toffoli =
      4*r.width+(24*(w.K5Decode n+1-w.k5)-16) := by
  have hlabels := r.lowerTree_visitLabels n w h.k5_le_decode
  rw [UnaryActionTree.visitLabels_inc] at hlabels
  rw [measuredEndLower, measuredLenUpdateLrpUnary_toffoli _ _ _ h.k5_le_decode _ _ _ _ _ _ _ _ _ _ _
    h.lower.work1Bits.decoder hlabels]
  rw [addConstant_toffoliCount _ _ _ _ h.constants_length,
    subConstant_toffoliCount _ _ _ _ h.constants_length]
  dsimp [EndIterationRegisters.width]
  omega

/-- Closed cost of the emitted measured refresh, including the full bank swap. -/
def measuredEndIterationToffoliFormula (workWidth lengthWidth n : Nat) (w : EndIterationWindows) : Nat :=
  workWidth + 2*(2*(lengthWidth-2)+2*lengthWidth) + (24*(w.K4+1-w.k4)-16) +
    4*lengthWidth + (24*(w.K5Decode n+1-w.k5)-16)

/-- Forward cost comes from the emitted adaptive constructors. -/
theorem measuredEndIteration_toffoli (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    (primitiveResources (measuredEndIteration r n w)).toffoli =
      measuredEndIterationToffoliFormula r.work1.length r.width n w := by
  rw [measuredEndIteration,primitiveResources_unitary_HPFree _ _ (by simp),primitiveResources_seq]
  simp only [PrimitiveResources.add]
  rw [controlledWorkSwap_toffoliCount _ _ _ (h.work1_length.trans h.work2_length.symm),
    measuredEndUpper_toffoli _ _ _ h,measuredEndLower_toffoli _ _ _ h]
  simp [measuredEndIterationToffoliFormula,Nat.add_assoc]

/-- The inverse's separately emitted order has the same actual Toffoli cost. -/
theorem measuredEndIterationInverse_toffoli (r : EndIterationRegisters) (n : Nat)
    (w : EndIterationWindows) (h : EndIterationLayout r n w) :
    (primitiveResources (measuredEndIterationInverse r n w)).toffoli =
      measuredEndIterationToffoliFormula r.work1.length r.width n w := by
  rw [measuredEndIterationInverse,primitiveResources_seq,primitiveResources_seq,
    primitiveResources_unitary_HPFree _ _ (by simp)]
  simp only [PrimitiveResources.add]
  rw [controlledWorkSwapInverse_toffoliCount _ _ _ (h.work1_length.trans h.work2_length.symm),
    measuredEndUpper_toffoli _ _ _ h,measuredEndLower_toffoli _ _ _ h]
  simp only [primitiveResources,gidneyToffoliCount,gidneyGateCount]
  simp [measuredEndIterationToffoliFormula]
  omega

/-- Exact savings against the strict source formula, for both nonempty source windows. -/
theorem measuredEndIteration_savings (workWidth lengthWidth n : Nat) (w : EndIterationWindows)
    (h4 : w.k4 ≤ w.K4) (h5 : w.k5 ≤ w.K5Decode n) :
    measuredEndIterationToffoliFormula workWidth lengthWidth n w +
      (16*(w.K4+1-w.k4)-12) + (16*(w.K5Decode n+1-w.k5)-12) =
        endIterationToffoliFormula workWidth lengthWidth n w := by
  unfold measuredEndIterationToffoliFormula endIterationToffoliFormula
  omega
end
end ShorECDLP.Paper2607_13816
