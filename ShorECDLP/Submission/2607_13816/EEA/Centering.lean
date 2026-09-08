import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstMinus

/-! # Input centering in the EEA wrapper

Compare the little-endian input to `p / 2 + 1`, retain the comparison in `Iter`,
then conditionally replace the input by `p - x`. The full borrowed word is used
by comparison; constant subtraction borrows only its first `n - 1` wires.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

/-- The exact preprocessing pair in the source EEA wrapper. -/
def eeaCenter (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) : AdaptiveCircuit :=
  (gidneyCompareGE input dirty (p / 2 + 1) c r t iter).seq
    (controlledConstMinus input (dirty.take (input.length - 1)) modulus iter c r t)

/-- Literal reverse of the preprocessing pair. -/
def eeaUncenter (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) : AdaptiveCircuit :=
  (controlledConstMinus input (dirty.take (input.length - 1)) modulus iter c r t).seq
    (gidneyCompareGE input dirty (p / 2 + 1) c r t iter)

private def centerFlagState (input : List Wire) (p : Nat) (iter : Wire) (s : BasisState) : BasisState :=
  upd s iter (s iter ^^ decide (p / 2 + 1 ≤ boolWordToNat (wireValues input s)))

def eeaCenterIdealState (input : List Wire) (modulus : List Bool) (p : Nat)
    (iter : Wire) (s : BasisState) : BasisState :=
  constMinusIdealState input modulus iter (centerFlagState input p iter s)

def eeaUncenterIdealState (input : List Wire) (modulus : List Bool) (p : Nat)
    (iter : Wire) (s : BasisState) : BasisState :=
  centerFlagState input p iter (constMinusIdealState input modulus iter s)

private theorem center_layout (input dirty : List Wire) (c r t iter : Wire)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup) :
    ([iter,c,r,t] ++ input ++ dirty.take (input.length - 1)).Nodup := by
  have hp : ([c,r,t,iter] ++ input ++ dirty).Perm ([iter,c,r,t] ++ input ++ dirty) :=
    ((show ([c,r,t] ++ [iter]).Perm ([iter] ++ [c,r,t]) from
      List.perm_append_comm).append_right input).append_right dirty
  exact (hp.nodup_iff.mp hnd).sublist
    ((List.Sublist.refl _).append (List.take_sublist _ _))

private theorem center_geometry (input dirty : List Wire) (c r t iter : Wire)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup) :
    input.Nodup ∧ (∀ w ∈ [c,r,t,iter], w ∉ input) ∧
      c ≠ iter ∧ r ≠ iter ∧ t ≠ iter := by
  have hl := List.nodup_append.mp (List.nodup_append.mp hnd).1
  refine ⟨hl.2.1,?_,?_,?_,?_⟩
  · intro w hw hi; exact hl.2.2 w hw w hi rfl
  all_goals
    have h := hl.1
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at h
    tauto

private theorem centerFlagState_word (input : List Wire) (p : Nat) (iter : Wire)
    (s : BasisState) (hi : iter ∉ input) :
    wireValues input (centerFlagState input p iter s) = wireValues input s := by
  apply List.map_congr_left
  intro w hw
  have hne : w ≠ iter := by intro he; subst w; exact hi hw
  simp [centerFlagState,upd,hne]

/-- Centering writes the smaller positive representative and remembers the sign
in the iteration flag. All other wires retain their complete initial state. -/
theorem eeaCenterIdealState_correct (input dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t iter : Wire) (s : BasisState)
    (hn : 0 < input.length) (hk : input.length = modulus.length)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup)
    (hp : p < 2 ^ input.length) (hm : boolWordToNat modulus = p)
    (hx : 0 < boolWordToNat (wireValues input s))
    (hxp : boolWordToNat (wireValues input s) < p) (hi : s iter = false) :
    let after := eeaCenterIdealState input modulus p iter s
    boolWordToNat (wireValues input after) =
      min (boolWordToNat (wireValues input s)) (p - boolWordToNat (wireValues input s)) ∧
    0 < boolWordToNat (wireValues input after) ∧
    boolWordToNat (wireValues input after) ≤ p / 2 ∧
    after iter = decide (p / 2 + 1 ≤ boolWordToNat (wireValues input s)) ∧
    (∀ w, w ∉ input → w ≠ iter → after w = s w) := by
  have hg := center_geometry input dirty c r t iter hnd
  have hiw := hg.2.1 iter (by simp)
  have hw := centerFlagState_word input p iter s hiw
  have hminus := constMinusIdealState_correct input modulus iter p
    (centerFlagState input p iter s) hn hk hg.1 hiw hp hm (by rw [hw]; omega)
  have hv : boolWordToNat (wireValues input (eeaCenterIdealState input modulus p iter s)) =
      min (boolWordToNat (wireValues input s)) (p - boolWordToNat (wireValues input s)) := by
    change boolWordToNat (wireValues input (constMinusIdealState input modulus iter _)) = _
    rw [hminus.1,hw]
    simp only [centerFlagState,upd,↓reduceIte,hi,Bool.false_xor,decide_eq_true_eq]
    split <;> omega
  refine ⟨hv,?_,?_,?_,?_⟩
  · rw [hv]; omega
  · rw [hv]; omega
  · change constMinusIdealState input modulus iter _ iter = _
    rw [hminus.2 iter hiw]
    simp [centerFlagState,upd,hi]
  · intro w hw hwi
    exact (hminus.2 w hw).trans (by simp [centerFlagState,upd,hwi])

private theorem center_take_length (input dirty : List Wire)
    (hn : 0 < input.length) (hd : input.length = dirty.length) :
    input.length = (dirty.take (input.length - 1)).length + 1 := by
  simp only [List.length_take]
  omega

/-- Every forward preprocessing branch preserves coherent relative phases. -/
theorem eeaCenter_branch_correct (input dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t iter : Wire) (s : BasisState)
    (hn : 0 < input.length) (hk : input.length = modulus.length)
    (hd : input.length = dirty.length) (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : InstrumentBranch) (hb : branch ∈ (eeaCenter input dirty modulus p c r t iter).run) :
    branch.kraus (ket s) = registerXResetMagnitude branch.history.length •
      ket (eeaCenterIdealState input modulus p iter s) := by
  have hg := center_geometry input dirty c r t iter hnd
  apply horner_seq_branch _ _ s (centerFlagState input p iter s) _ _ _ branch hb
  · intro b hb
    have hb' := gidneyCompareGE_branch_correct input dirty (p / 2 + 1) c r t iter s
      hd hnd hc hr ht b hb
    rw [hb'.1,hb'.2]
    rfl
  · intro b hb
    have hb' := controlledConstMinus_branch_correct input (dirty.take (input.length - 1))
      modulus iter c r t (centerFlagState input p iter s) hk (center_take_length input dirty hn hd)
      (center_layout input dirty c r t iter hnd)
      (by simp [centerFlagState,upd,hg.2.2.1,hc])
      (by simp [centerFlagState,upd,hg.2.2.2.1,hr])
      (by simp [centerFlagState,upd,hg.2.2.2.2,ht]) b hb
    exact hb'

/-- The source reverse preprocessing order also has a positive branch coefficient. -/
theorem eeaUncenter_branch_correct (input dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t iter : Wire) (s : BasisState)
    (hn : 0 < input.length) (hk : input.length = modulus.length)
    (hd : input.length = dirty.length) (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (hp : p < 2 ^ input.length) (hm : boolWordToNat modulus = p)
    (hx : boolWordToNat (wireValues input s) ≤ p)
    (branch : InstrumentBranch) (hb : branch ∈ (eeaUncenter input dirty modulus p c r t iter).run) :
    branch.kraus (ket s) = registerXResetMagnitude branch.history.length •
      ket (eeaUncenterIdealState input modulus p iter s) := by
  have hg := center_geometry input dirty c r t iter hnd
  have hi := constMinusIdealState_correct input modulus iter p s hn hk hg.1
    (hg.2.1 iter (by simp)) hp hm hx
  apply horner_seq_branch _ _ s (constMinusIdealState input modulus iter s) _ _ _ branch hb
  · intro b hb
    exact controlledConstMinus_branch_correct input (dirty.take (input.length - 1)) modulus iter c r t s
      hk (center_take_length input dirty hn hd) (center_layout input dirty c r t iter hnd) hc hr ht b hb
  · intro b hb
    have hb' := gidneyCompareGE_branch_correct input dirty (p / 2 + 1) c r t iter _
      hd hnd ((hi.2 c (hg.2.1 c (by simp))).trans hc)
      ((hi.2 r (hg.2.1 r (by simp))).trans hr)
      ((hi.2 t (hg.2.1 t (by simp))).trans ht) b hb
    rw [hb'.1,hb'.2]
    rfl

/-- Reversing preprocessing restores the entire initial state, including `Iter`. -/
theorem eeaUncenterIdealState_after_center (input dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t iter : Wire) (s : BasisState)
    (hn : 0 < input.length) (hk : input.length = modulus.length)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup)
    (hp : p < 2 ^ input.length) (hm : boolWordToNat modulus = p)
    (hx : boolWordToNat (wireValues input s) ≤ p) :
    eeaUncenterIdealState input modulus p iter (eeaCenterIdealState input modulus p iter s) = s := by
  have hg := center_geometry input dirty c r t iter hnd
  have hi := hg.2.1 iter (by simp)
  have hw := centerFlagState_word input p iter s hi
  unfold eeaUncenterIdealState eeaCenterIdealState
  rw [constMinusIdealState_involutive input modulus iter p _ hn hk hg.1 hi hp hm (by rw [hw]; exact hx)]
  have hw' := centerFlagState_word input p iter s hi
  unfold centerFlagState at hw' ⊢
  rw [hw']
  funext w
  by_cases he : w = iter
  · subst w; simp [upd]
  · simp [upd,he]

/-- Both directions are well formed on the same physical register contract. -/
theorem eeaCenter_wellFormed (input dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t iter : Wire) (hn : 0 < input.length)
    (hk : input.length = modulus.length) (hd : input.length = dirty.length)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup) :
    (eeaCenter input dirty modulus p c r t iter).WellFormed ∧
    (eeaUncenter input dirty modulus p c r t iter).WellFormed := by
  have hc := gidneyCompareGE_wellFormed input dirty (p / 2 + 1) c r t iter hd hnd
  have hn := controlledConstMinus_wellFormed input (dirty.take (input.length - 1)) modulus iter c r t hk
    (center_take_length input dirty hn hd) (center_layout input dirty c r t iter hnd)
  exact ⟨hc.seq hn,hn.seq hc⟩

/-- Forward and reverse branches may have independent histories; every pair
restores the complete canonical input state with its positive total amplitude. -/
theorem eeaUncenter_after_center (input dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t iter : Wire) (s : BasisState)
    (hn : 0 < input.length) (hk : input.length = modulus.length)
    (hd : input.length = dirty.length) (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hi : s iter = false)
    (hp : p < 2 ^ input.length) (hm : boolWordToNat modulus = p)
    (hx : 0 < boolWordToNat (wireValues input s))
    (hxp : boolWordToNat (wireValues input s) < p)
    (forward reverse : InstrumentBranch)
    (hf : forward ∈ (eeaCenter input dirty modulus p c r t iter).run)
    (hrv : reverse ∈ (eeaUncenter input dirty modulus p c r t iter).run) :
    reverse.kraus (forward.kraus (ket s)) =
      registerXResetMagnitude (forward.history.length + reverse.history.length) • ket s := by
  have hg := center_geometry input dirty c r t iter hnd
  have hs := eeaCenterIdealState_correct input dirty modulus p c r t iter s hn hk hnd hp hm hx hxp hi
  have hforward := eeaCenter_branch_correct input dirty modulus p c r t iter s hn hk hd hnd hc hr ht forward hf
  have hreverse := eeaUncenter_branch_correct input dirty modulus p c r t iter _ hn hk hd hnd
    ((hs.2.2.2.2 c (hg.2.1 c (by simp)) hg.2.2.1).trans hc)
    ((hs.2.2.2.2 r (hg.2.1 r (by simp)) hg.2.2.2.1).trans hr)
    ((hs.2.2.2.2 t (hg.2.1 t (by simp)) hg.2.2.2.2).trans ht)
    hp hm (by have hbound := hs.2.2.1; omega) reverse hrv
  rw [hforward,map_smul,hreverse,eeaUncenterIdealState_after_center input dirty modulus p c r t iter s
    hn hk hnd hp hm (by omega),smul_smul]
  simp [registerXResetMagnitude,pow_add]

/-- The centered divisor fits in one fewer bit than the modulus register. -/
theorem eeaCenterIdealState_half_width (input dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t iter : Wire) (s : BasisState)
    (hn : 0 < input.length) (hk : input.length = modulus.length)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup)
    (hp : p < 2 ^ input.length) (hm : boolWordToNat modulus = p)
    (hx : 0 < boolWordToNat (wireValues input s))
    (hxp : boolWordToNat (wireValues input s) < p) (hi : s iter = false) :
    boolWordToNat (wireValues input (eeaCenterIdealState input modulus p iter s)) <
      2 ^ (input.length - 1) := by
  have h := (eeaCenterIdealState_correct input dirty modulus p c r t iter s hn hk hnd hp hm hx hxp hi).2.2.1
  have he : input.length = (input.length - 1) + 1 := by omega
  rw [he,Nat.pow_succ] at hp
  omega

/-- Production preprocessing on a 256-bit word and the EEA shared borrowed bank. -/
def secp256k1EEACenter : AdaptiveCircuit :=
  eeaCenter (List.range' 4 256) (List.range' 260 256) secp256k1ModulusBits
    (2 ^ 256 - 2 ^ 32 - 977) 1 2 3 0

/-- The literal reverse preprocessing on the same physical roles. -/
def secp256k1EEAUncenter : AdaptiveCircuit :=
  eeaUncenter (List.range' 4 256) (List.range' 260 256) secp256k1ModulusBits
    (2 ^ 256 - 2 ^ 32 - 977) 1 2 3 0

private def centerProductionCompare : AdaptiveCircuit :=
  gidneyCompareGE (List.range' 4 256) (List.range' 260 256)
    ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1) 1 2 3 0

set_option maxRecDepth 10000

private theorem centerProduction_programs :
    secp256k1EEACenter = centerProductionCompare.seq secp256k1ConstMinus ∧
    secp256k1EEAUncenter = secp256k1ConstMinus.seq centerProductionCompare := by
  have ht : (List.range' 260 256).take 255 = List.range' 260 255 := by decide
  simp only [secp256k1EEACenter,secp256k1EEAUncenter,eeaCenter,eeaUncenter,
    List.length_range',show 256 - 1 = 255 from rfl,ht]
  exact ⟨rfl,rfl⟩

private theorem centerProduction_layout :
    ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

set_option maxRecDepth 10000 in
private theorem centerProduction_compare_metrics :
    gidneyToffoliCount centerProductionCompare = 767 ∧
    gidneyCnotCount centerProductionCompare = 1537 ∧
    centerProductionCompare.tCount = 5369 ∧
    centerProductionCompare.measurementCount = 256 ∧
    (∀ w, w ∈ centerProductionCompare.wires ↔
      w ∈ [1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256) := by
  exact gidneyCompareGE_metrics 4 (List.range' 5 255) (List.range' 260 256)
    ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1) 1 2 3 0 (by simp) (by decide) (by decide)

private theorem centerProduction_counts (program : AdaptiveCircuit)
    (hprogram : program ∈ [secp256k1EEACenter,secp256k1EEAUncenter]) :
    gidneyToffoliCount program = 2295 ∧ gidneyCnotCount program = 6842 ∧
    program.tCount = 16065 ∧ program.measurementCount = 766 := by
  have hseqT (a b : AdaptiveCircuit) : (a.seq b).tCount = a.tCount + b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  have hseqCCX (a b : AdaptiveCircuit) : gidneyToffoliCount (a.seq b) =
      gidneyToffoliCount a + gidneyToffoliCount b := modularGateCount_seq _ a b
  have hseqCX (a b : AdaptiveCircuit) : gidneyCnotCount (a.seq b) =
      gidneyCnotCount a + gidneyCnotCount b := modularGateCount_seq _ a b
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hprogram
  rcases hprogram with rfl | rfl <;>
    simp only [centerProduction_programs.1,centerProduction_programs.2,hseqCCX,hseqCX,hseqT,
      modularMeasurements_seq,centerProduction_compare_metrics.1,centerProduction_compare_metrics.2.1,
      centerProduction_compare_metrics.2.2.1,centerProduction_compare_metrics.2.2.2.1,
      secp256k1ConstMinus_counts.1,secp256k1ConstMinus_counts.2.1,secp256k1ConstMinus_counts.2.2.1,
      secp256k1ConstMinus_counts.2.2.2] <;> decide

private theorem centerProduction_wires (program : AdaptiveCircuit)
    (hprogram : program ∈ [secp256k1EEACenter,secp256k1EEAUncenter]) (w : Wire) :
    w ∈ program.wires ↔ w ∈ List.range' 0 516 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hprogram
  rcases hprogram with rfl | rfl <;>
    simp only [centerProduction_programs.1,centerProduction_programs.2,modularWires_seq,
      centerProduction_compare_metrics.2.2.2.2 w,secp256k1ConstMinus_wires w]
  all_goals
    simp
    dsimp only [Wire] at *
    omega

private theorem centerProduction_qubits (program : AdaptiveCircuit)
    (hprogram : program ∈ [secp256k1EEACenter,secp256k1EEAUncenter]) : program.qubitCount = 516 := by
  have heq : program.wires.dedup.toFinset = (List.range' 0 516).toFinset := by
    ext w
    simpa only [List.mem_toFinset,List.mem_dedup] using centerProduction_wires program hprogram w
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

attribute [local irreducible] eeaCenter eeaUncenter eeaCenterIdealState eeaUncenterIdealState

/-- Same-program certificate for the source input-centering pair: the positive
centered divisor fits in 255 bits, `Iter` retains the sign, and every branch pair
cancels. Both literal directions use the listed exact resources. -/
theorem secp256k1EEACenter_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hi : s 0 = false)
    (hx : 0 < boolWordToNat (wireValues (List.range' 4 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 4 256) s) < 2 ^ 256 - 2 ^ 32 - 977) :
    let after := eeaCenterIdealState (List.range' 4 256) secp256k1ModulusBits
      (2 ^ 256 - 2 ^ 32 - 977) 0 s
    boolWordToNat (wireValues (List.range' 4 256) after) =
      min (boolWordToNat (wireValues (List.range' 4 256) s))
        (2 ^ 256 - 2 ^ 32 - 977 - boolWordToNat (wireValues (List.range' 4 256) s)) ∧
    0 < boolWordToNat (wireValues (List.range' 4 256) after) ∧
    boolWordToNat (wireValues (List.range' 4 256) after) < 2 ^ 255 ∧
    after 0 = decide ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1 ≤
      boolWordToNat (wireValues (List.range' 4 256) s)) ∧
    (∀ w, w ∉ List.range' 4 256 → w ≠ 0 → after w = s w) ∧
    (∀ b ∈ secp256k1EEACenter.run, b.kraus (ket s) =
      registerXResetMagnitude b.history.length • ket after) ∧
    (∀ f ∈ secp256k1EEACenter.run, ∀ r ∈ secp256k1EEAUncenter.run,
      r.kraus (f.kraus (ket s)) = registerXResetMagnitude (f.history.length + r.history.length) • ket s) ∧
    (∀ program ∈ [secp256k1EEACenter,secp256k1EEAUncenter],
      program.WellFormed ∧ (∀ ψ, Instrument.bornMass program.run ψ = normSq ψ) ∧
      gidneyToffoliCount program = 2295 ∧ gidneyCnotCount program = 6842 ∧
      program.tCount = 16065 ∧ program.measurementCount = 766 ∧ program.qubitCount = 516) := by
  have hn : 0 < (List.range' 4 256).length := by simp
  have hk : (List.range' 4 256).length = secp256k1ModulusBits.length := by simp [secp256k1ModulusBits]
  have hd : (List.range' 4 256).length = (List.range' 260 256).length := by simp
  have hp : 2 ^ 256 - 2 ^ 32 - 977 < 2 ^ (List.range' 4 256).length := by decide
  have hm : boolWordToNat secp256k1ModulusBits = 2 ^ 256 - 2 ^ 32 - 977 :=
    gidneyCompareBits_value 256 _ (by decide)
  have hstate := eeaCenterIdealState_correct (List.range' 4 256) (List.range' 260 256)
    secp256k1ModulusBits _ 1 2 3 0 s hn hk centerProduction_layout hp hm hx hxp hi
  have hwidth := eeaCenterIdealState_half_width (List.range' 4 256) (List.range' 260 256)
    secp256k1ModulusBits _ 1 2 3 0 s hn hk centerProduction_layout hp hm hx hxp hi
  refine ⟨hstate.1,hstate.2.1,hwidth,hstate.2.2.2.1,hstate.2.2.2.2,?_,?_,?_⟩
  · intro b hb
    exact eeaCenter_branch_correct _ _ _ _ _ _ _ _ s hn hk hd centerProduction_layout hc hr ht b hb
  · intro f hf r hrv
    exact eeaUncenter_after_center _ _ _ _ _ _ _ _ s hn hk hd centerProduction_layout
      hc hr ht hi hp hm hx hxp f r hf hrv
  · intro program hprogram
    have hw := eeaCenter_wellFormed (List.range' 4 256) (List.range' 260 256)
      secp256k1ModulusBits (2 ^ 256 - 2 ^ 32 - 977) 1 2 3 0 hn hk hd centerProduction_layout
    have hwell : program.WellFormed := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hprogram
      rcases hprogram with rfl | rfl
      · exact hw.1
      · exact hw.2
    have hcounts := centerProduction_counts program hprogram
    exact ⟨hwell,fun ψ => AdaptiveCircuit.run_preservesBornMass _ hwell ψ,hcounts.1,hcounts.2.1,
      hcounts.2.2.1,hcounts.2.2.2,centerProduction_qubits program hprogram⟩

end
end ShorECDLP.Paper2607_13816
