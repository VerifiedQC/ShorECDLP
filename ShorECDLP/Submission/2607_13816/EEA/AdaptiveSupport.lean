import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularAdd
/-! Physical-support refinement from measurement-uncomputed primitives to their coherent references. -/
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem erase_zero_wires (a b c : Wire) :
    (eraseZeroAnd a b c).wires ⊆ circuitWires (computeZeroAnd a b c) := by
  intro w hw
  simp only [eraseZeroAnd,modularWires_seq] at hw
  simp [AdaptiveCircuit.wires,measuredAndErase,measureResetWithCorrection,measuredAndCorrection,controlledZ,computeZeroAnd,circuitWires,gateWires] at hw ⊢
  aesop

/-- Measurement erasure uses only wires already present in the coherent decoder. -/
theorem unaryAction_wires_subset (order : UnaryOrder) (leaf : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire) :
    (unaryAction order leaf tree control ancillas).wires ⊆
      circuitWires (unaryActionUnitary order leaf tree control ancillas) := by
  induction tree generalizing control ancillas with
  | leaf label => simp [unaryAction,unaryActionUnitary,AdaptiveCircuit.wires]
  | node index zero one hz ho =>
    cases ancillas with
    | nil => simp [unaryAction,unaryActionUnitary,AdaptiveCircuit.wires]
    | cons path rest =>
      intro w hw
      have he := erase_zero_wires control index path
      have hzero := hz path rest
      have hone := ho path rest
      simp only [List.subset_def,circuitWires,List.mem_flatMap] at hzero hone he
      cases order <;>
        simp only [unaryAction,unaryActionUnitary,modularWires_seq,AdaptiveCircuit.wires,
          circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
      all_goals aesop

/-- Measurement erasure uses only wires already present in the coherent decoder. -/
theorem unaryAdaptiveAction_wires_subset (order : UnaryOrder) (leaf : Nat → Wire → AdaptiveCircuit) (reference : Nat → Wire → Circuit)
    (hleaf : ∀ label control, (leaf label control).wires ⊆ circuitWires (reference label control))
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire) :
    (unaryAdaptiveAction order leaf tree control ancillas).wires ⊆
      circuitWires (unaryActionUnitary order reference tree control ancillas) := by
  induction tree generalizing control ancillas with
  | leaf label => exact hleaf label control
  | node index zero one hz ho =>
    cases ancillas with
    | nil => simp [unaryAdaptiveAction,unaryActionUnitary,AdaptiveCircuit.wires]
    | cons path rest =>
      intro w hw
      have he := erase_zero_wires control index path
      have hzero := hz path rest
      have hone := ho path rest
      simp only [List.subset_def,circuitWires,List.mem_flatMap] at hzero hone he
      cases order <;>
        simp only [unaryAdaptiveAction,unaryActionUnitary,modularWires_seq,AdaptiveCircuit.wires,
          circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
      all_goals aesop


/-- The paired adaptive decoder also introduces no wires beyond its coherent reference. -/
theorem dualUnaryAdaptiveAction_wires_subset (order : UnaryOrder)
    (leaf : Nat → Wire → Wire → AdaptiveCircuit) (reference : Nat → Wire → Wire → Circuit)
    (hleaf : ∀ label a b, (leaf label a b).wires ⊆ circuitWires (reference label a b))
    (tree : DualUnaryActionTree) (a b : Wire) (pa pb : List Wire) :
    (dualUnaryAdaptiveAction order leaf tree a b pa pb).wires ⊆
      circuitWires (dualUnaryActionUnitary order reference tree a b pa pb) := by
  induction tree generalizing a b pa pb with
  | leaf label => exact hleaf label a b
  | node ia ib zero one hz ho =>
    cases pa with
    | nil => simp [dualUnaryAdaptiveAction,dualUnaryActionUnitary,AdaptiveCircuit.wires]
    | cons p ra =>
      cases pb with
      | nil => simp [dualUnaryAdaptiveAction,dualUnaryActionUnitary,AdaptiveCircuit.wires]
      | cons q rb =>
        intro w hw
        have hea := erase_zero_wires a ia p
        have heb := erase_zero_wires b ib q
        have hzero := hz p q ra rb
        have hone := ho p q ra rb
        simp only [List.subset_def,circuitWires,List.mem_flatMap] at hea heb hzero hone
        cases order <;>
          simp only [dualUnaryAdaptiveAction,dualUnaryActionUnitary,eraseDualZeroAnd,modularWires_seq,
            AdaptiveCircuit.wires,circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
        all_goals aesop


private theorem measured_and_wires (a b c : Wire) :
    (measuredAndErase a b c).wires ⊆ circuitWires [.CCX a b c] := by
  intro w hw
  simp [measuredAndErase,measureResetWithCorrection,measuredAndCorrection,controlledZ,
    AdaptiveCircuit.wires,circuitWires,gateWires] at hw ⊢
  aesop
private theorem mcx_tail_wires (acc : Wire) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChainTailAdaptive acc controls target scratch).wires ⊆ circuitWires (mcxVChainTail acc controls target scratch) := by
  induction controls generalizing acc scratch with
  | nil => simp [mcxVChainTailAdaptive,mcxVChainTail,AdaptiveCircuit.wires]
  | cons first rest ih =>
    cases rest with
    | nil => simp [mcxVChainTailAdaptive,mcxVChainTail,AdaptiveCircuit.wires]
    | cons second rest =>
      cases scratch with
      | nil => simp [mcxVChainTailAdaptive,mcxVChainTail,AdaptiveCircuit.wires]
      | cons s ss =>
        intro w hw
        have he := measured_and_wires first acc s
        have ht := ih s ss
        simp only [List.subset_def,circuitWires,List.mem_flatMap] at he ht
        simp only [mcxVChainTailAdaptive,mcxVChainTail,modularWires_seq,AdaptiveCircuit.wires,
          circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
        aesop
/-- The adaptive v-chain uses only wires already present in the coherent v-chain. -/
theorem mcxVChainAdaptive_wires_subset (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChainAdaptive controls target scratch).wires ⊆ circuitWires (mcxVChain controls target scratch) := by
  cases controls with
  | nil => simp [mcxVChainAdaptive,mcxVChain,AdaptiveCircuit.wires]
  | cons a controls =>
    cases controls with
    | nil => simp [mcxVChainAdaptive,mcxVChain,AdaptiveCircuit.wires]
    | cons b controls => exact mcx_tail_wires b (a::controls) target scratch


private theorem unitary_prefix_wires (c : Circuit) (a : AdaptiveCircuit) (ref : Circuit)
    (h : a.wires ⊆ circuitWires ref) :
    (AdaptiveCircuit.unitary c a).wires ⊆ circuitWires (c++ref) := by
  intro w hw
  simp only [AdaptiveCircuit.wires,circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
  exact hw.elim Or.inl (fun hw => Or.inr (h hw))
private theorem seq_wires (a b : AdaptiveCircuit) (ca cb : Circuit)
    (ha : a.wires ⊆ circuitWires ca) (hb : b.wires ⊆ circuitWires cb) :
    (a.seq b).wires ⊆ circuitWires (ca++cb) := by
  intro w hw
  rw [modularWires_seq] at hw
  simp only [circuitWires,List.flatMap_append,List.mem_append]
  exact hw.elim (fun hw => Or.inl (ha hw)) (fun hw => Or.inr (hb hw))
private theorem unitary_only_wires (c : Circuit) :
    (AdaptiveCircuit.unitary c .done).wires ⊆ circuitWires c := by simp [AdaptiveCircuit.wires]
/-- Equality masks and adaptive v-chains stay inside the coherent equality support. -/
theorem computeEqConstAdaptive_wires_subset (register : List Wire) (value : Nat)
    (flag : Wire) (scratch : List Wire) :
    (computeEqConstAdaptive register value flag scratch).wires ⊆
      circuitWires (computeEqConst register value flag scratch) := by
  simpa only [computeEqConstAdaptive,computeEqConst,List.append_assoc] using
    unitary_prefix_wires (zeroMask register value) _ _
      (seq_wires _ _ _ _ (mcxVChainAdaptive_wires_subset register flag scratch)
        (unitary_only_wires (zeroMask register value)))
/-- Both adaptive equality evaluations retain the same selector support. -/
theorem toggleEqConstUnderControlAdaptive_wires_subset (root : Wire) (register : List Wire)
    (value : Nat) (acc flag : Wire) (scratch : List Wire) :
    (toggleEqConstUnderControlAdaptive root register value acc flag scratch).wires ⊆
      circuitWires (toggleEqConstUnderControl root register value acc flag scratch) := by
  have h := computeEqConstAdaptive_wires_subset register value flag scratch
  simpa only [toggleEqConstUnderControlAdaptive,toggleEqConstUnderControl,List.append_assoc] using
    seq_wires _ _ _ _ h (unitary_prefix_wires [.CCX root flag acc] _ _ h)
/-- A measured ripple cell stays on the five wires of its coherent counterpart. -/
theorem rippleFirstCellAdaptive_wires_subset (mode : RippleMode) (q t a c s : Wire) :
    (rippleFirstCellAdaptive mode q t a c s).wires ⊆ circuitWires (rippleFirstCell mode q t a c s) := by
  intro w hw
  cases mode <;>
    simp [rippleFirstCellAdaptive,rippleFirstCell,controlledMajAdaptive,controlledUmaInvAdaptive,
      controlledMaj,controlledUmaInv,cleanC3XAdaptive,mcxVChainAdaptive,mcxVChainTailAdaptive,
      modularWires_seq,measuredAndErase,measureResetWithCorrection,measuredAndCorrection,controlledZ,
      cleanC3X,AdaptiveCircuit.wires,circuitWires,gateWires] at hw ⊢
  all_goals aesop
/-- The second measured ripple cell likewise adds no physical labels. -/
theorem rippleSecondCellAdaptive_wires_subset (mode : RippleMode) (q t a c s : Wire) :
    (rippleSecondCellAdaptive mode q t a c s).wires ⊆ circuitWires (rippleSecondCell mode q t a c s) := by
  intro w hw
  cases mode <;>
    simp [rippleSecondCellAdaptive,rippleSecondCell,controlledUmaAdaptive,controlledMajInvAdaptive,
      controlledUma,controlledMajInv,cleanC3XAdaptive,mcxVChainAdaptive,mcxVChainTailAdaptive,
      modularWires_seq,measuredAndErase,measureResetWithCorrection,measuredAndCorrection,controlledZ,
      cleanC3X,AdaptiveCircuit.wires,circuitWires,gateWires] at hw ⊢
  all_goals aesop


/-- The first interval leaf keeps the physical support of its coherent counterpart. -/
theorem intervalFirstLeafAdaptive_wires_subset (mode : RippleMode) (special : Bool)
    (rt lt acc target addend carry scratch : Wire) (label : Nat) (rc lc : Wire) :
    (intervalFirstLeafAdaptive mode special rt lt acc target addend carry scratch label rc lc).wires ⊆
      circuitWires (intervalFirstLeaf mode special rt lt acc target addend carry scratch label rc lc) := by
  simpa only [intervalFirstLeafAdaptive,intervalFirstLeaf,List.append_assoc] using
    unitary_prefix_wires (endpointLeafToggle special label rt rc acc) _ _
      (seq_wires _ _ _ _ (rippleFirstCellAdaptive_wires_subset mode acc target addend carry scratch)
        (unitary_only_wires (endpointLeafToggle special label lt lc acc)))
/-- Adaptive handling of the special top lane introduces no extra physical labels. -/
theorem topSpecialFirstLeafAdaptive_wires_subset (mode : RippleMode) (value : Nat)
    (rr lr : List Wire) (acc target addend carry scratch flag : Wire) (eq : List Wire) (rc lc : Wire) :
    (topSpecialFirstLeafAdaptive mode value rr lr acc target addend carry scratch flag eq rc lc).wires ⊆
      circuitWires (topSpecialFirstLeaf mode value rr lr acc target addend carry scratch flag eq rc lc) := by
  simpa only [topSpecialFirstLeafAdaptive,topSpecialFirstLeaf,List.append_assoc] using
    seq_wires _ _ _ _
      (toggleEqConstUnderControlAdaptive_wires_subset rc rr value acc flag eq)
      (seq_wires _ _ _ _ (rippleFirstCellAdaptive_wires_subset mode acc target addend carry scratch)
        (toggleEqConstUnderControlAdaptive_wires_subset lc lr value acc flag eq))
/-- Whole adaptive first traversal stays on its coherent tree's physical labels. -/
theorem intervalFirstTraversalAdaptive_wires_subset (mode : RippleMode) (special : Bool)
    (rt lt acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rc lc : Wire) (rp lp : List Wire) :
    (intervalFirstTraversalAdaptive mode special rt lt acc carry scratch targetAt addendAt tree rc lc rp lp).wires ⊆
      circuitWires (intervalFirstTraversal mode special rt lt acc carry scratch targetAt addendAt tree rc lc rp lp) :=
  dualUnaryAdaptiveAction_wires_subset .dec _ _
    (fun label a b => intervalFirstLeafAdaptive_wires_subset mode special rt lt acc
      (targetAt label) (addendAt label) carry scratch label a b) tree rc lc rp lp

/-- The second interval leaf keeps the physical support of its coherent counterpart. -/
theorem intervalSecondLeafAdaptive_wires_subset (mode : RippleMode) (special : Bool)
    (rt lt acc target addend carry scratch : Wire) (label : Nat) (rc lc : Wire) :
    (intervalSecondLeafAdaptive mode special rt lt acc target addend carry scratch label rc lc).wires ⊆
      circuitWires (intervalSecondLeaf mode special rt lt acc target addend carry scratch label rc lc) := by
  simpa only [intervalSecondLeafAdaptive,intervalSecondLeaf,List.append_assoc] using
    unitary_prefix_wires (endpointLeafToggle special label lt lc acc) _ _
      (seq_wires _ _ _ _ (rippleSecondCellAdaptive_wires_subset mode acc target addend carry scratch)
        (unitary_only_wires (endpointLeafToggle special label rt rc acc)))
/-- Adaptive handling of the special top lane introduces no extra physical labels. -/
theorem topSpecialSecondLeafAdaptive_wires_subset (mode : RippleMode) (value : Nat)
    (rr lr : List Wire) (acc target addend carry scratch flag : Wire) (eq : List Wire) (rc lc : Wire) :
    (topSpecialSecondLeafAdaptive mode value rr lr acc target addend carry scratch flag eq rc lc).wires ⊆
      circuitWires (topSpecialSecondLeaf mode value rr lr acc target addend carry scratch flag eq rc lc) := by
  simpa only [topSpecialSecondLeafAdaptive,topSpecialSecondLeaf,List.append_assoc] using
    seq_wires _ _ _ _
      (toggleEqConstUnderControlAdaptive_wires_subset lc lr value acc flag eq)
      (seq_wires _ _ _ _ (rippleSecondCellAdaptive_wires_subset mode acc target addend carry scratch)
        (toggleEqConstUnderControlAdaptive_wires_subset rc rr value acc flag eq))
/-- Whole adaptive second traversal stays on its coherent tree's physical labels. -/
theorem intervalSecondTraversalAdaptive_wires_subset (mode : RippleMode) (special : Bool)
    (rt lt acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rc lc : Wire) (rp lp : List Wire) :
    (intervalSecondTraversalAdaptive mode special rt lt acc carry scratch targetAt addendAt tree rc lc rp lp).wires ⊆
      circuitWires (intervalSecondTraversal mode special rt lt acc carry scratch targetAt addendAt tree rc lc rp lp) :=
  dualUnaryAdaptiveAction_wires_subset .inc _ _
    (fun label a b => intervalSecondLeafAdaptive_wires_subset mode special rt lt acc
      (targetAt label) (addendAt label) carry scratch label a b) tree rc lc rp lp
end ShorECDLP.Paper2607_13816
