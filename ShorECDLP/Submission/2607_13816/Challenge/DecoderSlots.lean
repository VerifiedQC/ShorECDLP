import ShorECDLP.Submission.«2607_13816».Challenge.ArithmeticSlots
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem andEraseProgram_slots (n s : Nat) (a b w : Wire) :
    (andEraseProgram n s a b w).gateSlots=3 := by
  simp only [andEraseProgram,Straight.gateSlots,recordGates_slots,controlledZ,List.length_cons,List.length_nil]

theorem vchainTailProgram_slots (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) :
    (vchainTailProgram n controls acc target scratch start).2.gateSlots ≤ 4*controls.length := by
  induction controls generalizing acc scratch start with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    cases cs with
    | nil => simp only [vchainTailProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
    | cons c' cs =>
      cases scratch with
      | nil => exact Nat.zero_le _
      | cons work scratch =>
        have h := ih work scratch start
        simp only [vchainTailProgram,prependCompiled_slots,appendCompiled_slots,andEraseProgram_slots,
          List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem vchainProgram_slots (n start : Nat) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (vchainProgram n start controls target scratch).2.gateSlots ≤ 4*controls.length+1 := by
  cases controls with
  | nil => simp only [vchainProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
  | cons a rest =>
    cases rest with
    | nil => simp only [vchainProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
    | cons b bs =>
      have h := vchainTailProgram_slots n (a::bs) b target scratch start
      change (vchainTailProgram n (a::bs) b target scratch start).2.gateSlots ≤ _
      simp only [List.length_cons] at h ⊢
      omega

theorem zeroEraseProgram_slots (n s : Nat) (a b w : Wire) :
    (zeroEraseProgram n s a b w).2.gateSlots=5 := by
  simp only [zeroEraseProgram,prependCompiled_slots,appendCompiled_slots,andEraseProgram_slots,
    literalProgram_slots,List.length_cons,List.length_nil]

theorem unaryProgram_slots_le (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (bound : Nat) (hl : ∀ l q s, (leaf l q s).2.gateSlots ≤ bound)
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire) (start : Nat) :
    (unaryProgram n order leaf tree q paths start).2.gateSlots ≤
      bound*(tree.internalNodes+1)+10*tree.internalNodes := by
  induction tree generalizing q paths start with
  | leaf l =>
    rw [unaryProgram]
    simpa only [UnaryActionTree.internalNodes,Nat.zero_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero] using hl l q start
  | node bit zero one ihz iho =>
    cases paths with
    | nil => rw [unaryProgram]; exact Nat.zero_le _
    | cons path rest =>
      have hz (s : Nat) := ihz path rest s
      have ho (s : Nat) := iho path rest s
      rw [unaryProgram]
      cases order <;>
        simp only [compiledIf_slots,ite_true,reduceCtorEq,ite_false,
          prependCompiled_slots,appendCompiled_slots,zeroEraseProgram_slots,computeZeroAnd,
          List.length_cons,List.length_nil,UnaryActionTree.internalNodes]
      all_goals grind only

theorem zeroMaskFrom_length_le (register : List Wire) (v k : Nat) :
    (zeroMaskFrom register v k).length ≤ register.length := by
  induction register generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [zeroMaskFrom,List.length_append,List.length_cons]
    have h := ih (k+1)
    split <;> simp only [List.length_cons,List.length_nil] <;> omega

theorem equalityProgram_slots (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) :
    (equalityProgram n start register value flag scratch).2.gateSlots ≤ 6*register.length+1 := by
  have hb := vchainProgram_slots n start register flag scratch
  have hm := zeroMaskFrom_length_le register value 0
  simp only [equalityProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,zeroMask]
  omega

theorem toggleEqualityProgram_slots (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) :
    (toggleEqualityProgram n start root register value acc flag scratch).2.gateSlots ≤ 12*register.length+3 := by
  have he (s : Nat) := equalityProgram_slots n s register value flag scratch
  simp only [toggleEqualityProgram,appendCompiled_slots,prependCompiled_slots,List.length_cons,List.length_nil]
  grind only

theorem rippleMajProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleMajProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleMajProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem rippleUmaProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleUmaProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleUmaProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem rippleMajInvProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleMajInvProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleMajInvProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem rippleUmaInvProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleUmaInvProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleUmaInvProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem dualEraseProgram_slots (n s : Nat) (a i x b j y : Wire) :
    (dualEraseProgram n s a i x b j y).2.gateSlots=10 := by
  simp only [dualEraseProgram,appendCompiled_slots,zeroEraseProgram_slots]

theorem dualProgram_slots_le (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (bound : Nat) (hl : ∀ l a b s, (leaf l a b s).2.gateSlots ≤ bound)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) :
    (dualProgram n order leaf tree a b xs ys start).2.gateSlots ≤
      bound*(tree.internalNodes+1)+20*tree.internalNodes := by
  induction tree generalizing a b xs ys start with
  | leaf l =>
    rw [dualProgram]
    simpa only [DualUnaryActionTree.internalNodes,Nat.zero_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero] using hl l a b start
  | node i j zero one ihz iho =>
    cases xs with
    | nil =>
      rw [dualProgram]
      · exact Nat.zero_le _
      · simp
    | cons x xs =>
      cases ys with
      | nil =>
        rw [dualProgram]
        · exact Nat.zero_le _
        · simp
      | cons y ys =>
        have hz (s : Nat) := ihz x y xs ys s
        have ho (s : Nat) := iho x y xs ys s
        rw [dualProgram]
        cases order <;>
          simp only [compiledIf_slots,ite_true,reduceCtorEq,ite_false,
            prependCompiled_slots,appendCompiled_slots,dualEraseProgram_slots,computeZeroAnd,
            List.length_cons,List.length_nil,DualUnaryActionTree.internalNodes]
        all_goals grind only

theorem rippleFirstProgram_slots (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleFirstProgram n start mode control target addend carry scratch).2.gateSlots ≤ 16 := by
  cases mode
  · exact rippleMajProgram_slots n start control target addend carry scratch
  · exact rippleUmaInvProgram_slots n start control target addend carry scratch

theorem rippleSecondProgram_slots (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleSecondProgram n start mode control target addend carry scratch).2.gateSlots ≤ 16 := by
  cases mode
  · exact rippleUmaProgram_slots n start control target addend carry scratch
  · exact rippleMajInvProgram_slots n start control target addend carry scratch

theorem endpointLeafToggle_length_le (topSpecial : Bool) (label : Nat) (endpoint control acc : Wire) :
    (endpointLeafToggle topSpecial label endpoint control acc).length ≤ 3 := by
  unfold endpointLeafToggle
  split <;> simp only [List.length_cons,List.length_nil] <;> decide

theorem intervalFirstProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.gateSlots ≤ 22 := by
  have hr := endpointLeafToggle_length_le topSpecial label rightTop rightControl acc
  have hl := endpointLeafToggle_length_le topSpecial label leftTop leftControl acc
  have hc (s : Nat) := rippleFirstProgram_slots n s mode acc target addend carry scratch
  simp only [intervalFirstProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

theorem intervalSecondProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.gateSlots ≤ 22 := by
  have hr := endpointLeafToggle_length_le topSpecial label rightTop rightControl acc
  have hl := endpointLeafToggle_length_le topSpecial label leftTop leftControl acc
  have hc (s : Nat) := rippleSecondProgram_slots n s mode acc target addend carry scratch
  simp only [intervalSecondProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

theorem topFirstProgram_slots (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.gateSlots ≤
      12*rightRegister.length+12*leftRegister.length+22 := by
  have hr (s : Nat) := toggleEqualityProgram_slots n s rightRoot rightRegister value acc flag scratch
  have hl (s : Nat) := toggleEqualityProgram_slots n s leftRoot leftRegister value acc flag scratch
  have hc (s : Nat) := rippleFirstProgram_slots n s mode acc target addend carry work
  simp only [topFirstProgram,appendCompiled_slots]
  grind only

theorem topSecondProgram_slots (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.gateSlots ≤
      12*rightRegister.length+12*leftRegister.length+22 := by
  have hr (s : Nat) := toggleEqualityProgram_slots n s rightRoot rightRegister value acc flag scratch
  have hl (s : Nat) := toggleEqualityProgram_slots n s leftRoot leftRegister value acc flag scratch
  have hc (s : Nat) := rippleSecondProgram_slots n s mode acc target addend carry work
  simp only [topSecondProgram,appendCompiled_slots]
  grind only

theorem traversalFirstProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.gateSlots ≤
      22*(tree.internalNodes+1)+20*tree.internalNodes := by
  unfold traversalFirstProgram
  apply dualProgram_slots_le
  intro label right left cursor
  exact intervalFirstProgram_slots n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left

theorem traversalSecondProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.gateSlots ≤
      22*(tree.internalNodes+1)+20*tree.internalNodes := by
  unfold traversalSecondProgram
  apply dualProgram_slots_le
  intro label right left cursor
  exact intervalSecondProgram_slots n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left

theorem intervalTopFirstProgram_slots (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    (intervalTopFirstProgram n start r k K mode target).2.gateSlots ≤ 12*r.lengthS.length+12*r.lengthQ.length+22 := by
  simp only [intervalTopFirstProgram,compiledIf_slots]
  split
  · exact topFirstProgram_slots n start mode (intervalTopRelative k K) r.lengthS r.lengthQ
      (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K))
      (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control
  · exact Nat.zero_le _

theorem intervalTopSecondProgram_slots (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    (intervalTopSecondProgram n start r k K mode target).2.gateSlots ≤ 12*r.lengthS.length+12*r.lengthQ.length+22 := by
  simp only [intervalTopSecondProgram,compiledIf_slots]
  split
  · exact topSecondProgram_slots n start mode (intervalTopRelative k K) r.lengthS r.lengthQ
      (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K))
      (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control
  · exact Nat.zero_le _

theorem prepareIntervalEndpoints_length9 (t q s scratch : List Wire) (carry : Wire) (width k : Nat)
    (ht : t.length=9) (hq : q.length=9) (hs : s.length=9) (hw : 9≤scratch.length) :
    (prepareIntervalEndpoints t q s scratch carry width k).length ≤ 376 := by
  have hb (v : Nat) : (constantBits 9 v).count true ≤ 9 := by
    have h := List.count_le_length (l := constantBits 9 v) (a := true)
    simpa only [constantBits_length] using h
  rw [circuit_length_primitive,prepareIntervalEndpoints9_primitive _ _ _ _ _ _ _ ht hq hs hw]
  dsimp only [PrimitiveResources.x,PrimitiveResources.h,PrimitiveResources.cnot,PrimitiveResources.toffoli,PrimitiveResources.phase]
  have h4 := hb 4
  have hn := hb (width+2)
  have hk := hb k
  omega

theorem restoreIntervalEndpoints_length9 (t q s scratch : List Wire) (carry : Wire) (width k : Nat)
    (ht : t.length=9) (hq : q.length=9) (hs : s.length=9) (hw : 9≤scratch.length) :
    (restoreIntervalEndpoints t q s scratch carry width k).length ≤ 376 := by
  have hb (v : Nat) : (constantBits 9 v).count true ≤ 9 := by
    have h := List.count_le_length (l := constantBits 9 v) (a := true)
    simpa only [constantBits_length] using h
  rw [circuit_length_primitive,restoreIntervalEndpoints9_primitive _ _ _ _ _ _ _ ht hq hs hw]
  dsimp only [PrimitiveResources.x,PrimitiveResources.h,PrimitiveResources.cnot,PrimitiveResources.toffoli,PrimitiveResources.phase]
  have h4 := hb 4
  have hn := hb (width+2)
  have hk := hb k
  omega

theorem intervalSignUpdate_length_le (r : IntervalRegisters) (k K : Nat) (signUpdate : Bool) :
    (intervalSignUpdate r k K signUpdate).length ≤ 1 := by
  cases signUpdate <;> simp only [intervalSignUpdate,Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil] <;> decide

theorem intervalProgram_slots9 (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9)
    (hw : 9≤r.endpointScratch.length) :
    (intervalProgram n start r width k K mode signUpdate target).2.gateSlots ≤
      84*(intervalTree r k K).internalNodes+1273 := by
  have hp := prepareIntervalEndpoints_length9 r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k ht hq hs hw
  have hr := restoreIntervalEndpoints_length9 r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k ht hq hs hw
  have hsg := intervalSignUpdate_length_le r k K signUpdate
  have ht1 (s : Nat) := intervalTopFirstProgram_slots n s r k K mode target
  have ht2 (s : Nat) := intervalTopSecondProgram_slots n s r k K mode target
  have hf (s : Nat) := traversalFirstProgram_slots n s mode (intervalHasTopSpecial k K)
    (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  have hb (s : Nat) := traversalSecondProgram_slots n s mode (intervalHasTopSpecial k K)
    (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  simp only [hs,hq] at ht1 ht2
  simp only [intervalProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration
