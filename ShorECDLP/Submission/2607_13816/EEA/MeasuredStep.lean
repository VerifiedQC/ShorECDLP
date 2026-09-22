import ShorECDLP.Submission.«2607_13816».EEA.MeasuredBlockH
import ShorECDLP.Framework.Quantum.CoherentReplacement
import ShorECDLP.Framework.Quantum.AdaptiveComposition

namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private def adaptiveUnitary (c : Circuit) : AdaptiveCircuit := .unitary c .done
/-- Literal A--G adaptive prefix, excluding the endpoint H block. -/
def measuredStepPrefix (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  let w := certifiedActiveWindows n T
  (adaptiveUnitary (blockAForward r)).seq
    ((blockBAdaptive r n w.remainder).seq
      ((adaptiveUnitary (blockCForward r ++ blockDForward r w.quotientSwap)).seq
        ((blockEAdaptive r n w.coefficient).seq
          ((adaptiveUnitary (blockFForward r)).seq
            (phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch)))))
/-- Actual full forward step with measured endpoint refresh. -/
def measuredIndexedStep (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  (measuredStepPrefix r n T).seq (measuredBlockHForward r n T)
/-- Split the original adaptive step at its final strict H block. -/
theorem measuredStepPrefix_factor (r : IndexedStepRegisters) (n T : Nat) :
    indexedStepAdaptive r n T = (measuredStepPrefix r n T).seq (adaptiveUnitary (blockHForward r n T)) := by
  simp only [indexedStepAdaptive,measuredStepPrefix,circuit_seq_assoc]
  rfl
/-- Split the strict source circuit at the same boundary. -/
theorem measuredStepPrefix_unitary_factor (r : IndexedStepRegisters) (n T : Nat) :
    indexedStepUnitary r n T = (indexedStepShiftPrefix r n T ++ blockGForward r) ++ blockHForward r n T := by
  simp only [indexedStepUnitary,indexedStepShiftPrefix,indexedStepRemainderPrefix,List.append_assoc]
/-- The unchanged measured prefix implements its strict source prefix. -/
theorem measuredStepPrefix_coherent (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (measuredStepPrefix r n T)
      (Quantum.run (indexedStepShiftPrefix r n T ++ blockGForward r))
      (fun s => IndexedStepReady r s ∧ IndexedStepEpochEncoded r s) := by
  apply cancelUnitaryRight (blockHForward_wellFormed r n T h)
  have hc := indexedStepAdaptive_coherent r n T h
  rw [measuredStepPrefix_factor,measuredStepPrefix_unitary_factor] at hc
  exact hc
/-- Full coherent refinement on the existing ready and epoch-encoded input contract. -/
 theorem measuredIndexedStep_coherent (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (measuredIndexedStep r n T)
      (Quantum.run (indexedStepUnitary r n T))
      (fun s => IndexedStepReady r s ∧ IndexedStepEpochEncoded r s) := by
  have hp := indexedStepUnitary_HPFree r n T
  rw [measuredStepPrefix_unitary_factor] at hp
  have hpre : HPFree (indexedStepShiftPrefix r n T ++ blockGForward r) := by
    exact fun g hg => hp g (List.mem_append_left _ hg)
  have hall := (measuredStepPrefix_coherent r n T h).seq
    (measuredBlockHForward_coherent r n T h) (by
      intro s hs
      rw [run_ket_agrees_classical _ s hpre]
      exact supportedOn_ket _ _ (indexedStepBeforeEnd_ready r n T h s hs.1 hs.2))
  apply hall.congrIdeal
  intro s _
  rw [measuredStepPrefix_unitary_factor,Quantum.run_append]
  rfl
private theorem wf_left (a b : AdaptiveCircuit) (h : (a.seq b).WellFormed) : a.WellFormed := by
  induction a with
  | done => trivial
  | unitary c a ih => exact ⟨h.1,ih h.2⟩
  | xMeasureReset q a b ia ib => exact ⟨ia h.1,ib h.2⟩
/-- Every branch of the new full forward step is well formed. -/
theorem measuredIndexedStep_wellFormed (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) : (measuredIndexedStep r n T).WellFormed := by
  have ho := indexedStepAdaptive_wellFormed r n T h
  rw [measuredStepPrefix_factor] at ho
  exact (wf_left _ _ ho).seq (measuredBlockHForward_wellFormed r n T h)
/-- Exact savings in the emitted full forward step, including unchanged A--G costs. -/
theorem measuredIndexedStep_toffoli (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) (hw : 2 ≤ r.lengthT.length) :
    (primitiveResources (measuredIndexedStep r n T)).toffoli + measuredBlockHSavings n T =
      (primitiveResources (indexedStepAdaptive r n T)).toffoli := by
  have hp := indexedStepUnitary_HPFree r n T
  rw [measuredStepPrefix_unitary_factor] at hp
  have hh : HPFree (blockHForward r n T) := fun g hg => hp g (List.mem_append_right _ hg)
  have hc := measuredBlockHForward_toffoli r n T h hw
  have hu : (primitiveResources (adaptiveUnitary (blockHForward r n T))).toffoli =
      eeaToffoliCount (blockHForward r n T) := by
    rw [adaptiveUnitary,primitiveResources_unitary_HPFree _ _ hh]
    simp only [primitiveResources,gidneyToffoliCount,gidneyGateCount,PrimitiveResources.add,Nat.add_zero]
  rw [measuredIndexedStep,measuredStepPrefix_factor,primitiveResources_seq,primitiveResources_seq]
  change (primitiveResources (measuredStepPrefix r n T)).toffoli +
    (primitiveResources (measuredBlockHForward r n T)).toffoli + measuredBlockHSavings n T =
    (primitiveResources (measuredStepPrefix r n T)).toffoli +
      (primitiveResources (adaptiveUnitary (blockHForward r n T))).toffoli
  rw [hu,Nat.add_assoc,hc]


private theorem step_restrict {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P Q : BasisState → Prop} (h : CoherentlyImplementsOn a v P)
    (hp : ∀ s, Q s → P s) : CoherentlyImplementsOn a v Q := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

/-- Actual inverse step: measured H followed by the unchanged G-through-A tail. -/
def measuredIndexedStepInverse (r : IndexedStepRegisters) (n T : Nat) : AdaptiveCircuit :=
  (measuredBlockHInverse r n T).seq (indexedStepInverseTailAdaptive r n T)

/-- The inverse additionally needs clean H-entry control/scratch; its five tail conditions
are exactly the original inverse-adaptive conditions. -/
theorem measuredIndexedStepInverse_coherent (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) :
    CoherentlyImplementsOn (measuredIndexedStepInverse r n T)
      (Quantum.run (indexedStepInverseUnitary r n T))
      (fun s => IndexedStepReady r s ∧ IndexedStepInverseAdaptiveInput r n T s) := by
  have ho := step_restrict (indexedStepInverseAdaptive_coherent r n T h)
    (fun _ hs => hs.2 : ∀ s, IndexedStepReady r s ∧ IndexedStepInverseAdaptiveInput r n T s → _)
  rw [indexedStepInverseAdaptive_factor] at ho
  exact replaceInitialUnitary (blockHInverse_wellFormed r n T h) (blockHInverse_HPFree r n T)
    (step_restrict (measuredBlockHInverse_coherent r n T h) (fun _ hs => hs.1)) ho

/-- The inverse replacement preserves well-formedness of every emitted branch. -/
theorem measuredIndexedStepInverse_wellFormed (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) : (measuredIndexedStepInverse r n T).WellFormed := by
  have ho := indexedStepInverseAdaptive_wellFormed r n T h
  rw [indexedStepInverseAdaptive_factor] at ho
  exact (measuredBlockHInverse_wellFormed r n T h).seq ho.2

/-- Exact savings in the emitted inverse step, with all tail subroutines retained. -/
theorem measuredIndexedStepInverse_toffoli (r : IndexedStepRegisters) (n T : Nat)
    (h : IndexedStepLayout r n T) (hw : 2 ≤ r.lengthT.length) :
    (primitiveResources (measuredIndexedStepInverse r n T)).toffoli + measuredBlockHSavings n T =
      (primitiveResources (indexedStepInverseAdaptive r n T)).toffoli := by
  have hc := measuredBlockHInverse_toffoli r n T h hw
  have hu : (primitiveResources (AdaptiveCircuit.unitary (blockHInverse r n T) .done)).toffoli =
      eeaToffoliCount (blockHInverse r n T) := by
    rw [primitiveResources_unitary_HPFree _ _ (blockHInverse_HPFree r n T)]
    simp only [primitiveResources,gidneyToffoliCount,gidneyGateCount,PrimitiveResources.add,Nat.add_zero]
  rw [measuredIndexedStepInverse,indexedStepInverseAdaptive_factor,
    primitiveResources_seq,primitiveResources_seq]
  change (primitiveResources (measuredBlockHInverse r n T)).toffoli +
    (primitiveResources (indexedStepInverseTailAdaptive r n T)).toffoli + measuredBlockHSavings n T =
    (primitiveResources (AdaptiveCircuit.unitary (blockHInverse r n T) .done)).toffoli +
      (primitiveResources (indexedStepInverseTailAdaptive r n T)).toffoli
  rw [hu]
  omega

end
end ShorECDLP.Paper2607_13816
