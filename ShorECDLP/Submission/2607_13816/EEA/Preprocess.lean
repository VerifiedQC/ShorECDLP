import ShorECDLP.Submission.«2607_13816».EEA.WorkPreparation
import ShorECDLP.Submission.«2607_13816».EEA.Centering

/-! # Algorithm 1 preprocessing in the fixed EEA allocation

Arrange the work banks, center the input, and initialize the four length words.
The known modulus word supplies the reversible lowering's borrowed MCX scratch.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
set_option maxRecDepth 10000
attribute [local irreducible] lengthInitialize xorConstant workRegistersPrepare

/-- The source's length-word initialization following input centering. -/
def eeaLengthSetup : Circuit :=
  xorConstant (List.range' 531 9) 511 ++
  xorConstant (List.range' 540 9) 511 ++
  lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
    ((List.range' 7 256).reverse.take 254) (2 ^ 256 - 2 ^ 32 - 977)

/-- Concrete Algorithm 1 prefix, before the first Algorithm 3 iteration. -/
def eeaPreprocess : AdaptiveCircuit :=
  .unitary workRegistersPrepare
    ((eeaCenter (List.range' 266 256).reverse (List.range' 4 256)
      (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977)
      560 561 562 2).seq (.unitary eeaLengthSetup .done))

private theorem constantBits_take (width count value : Nat) :
    (constantBits width value).take count = constantBits (min count width) value := by
  induction width generalizing count value with
  | zero => simp [constantBits, xorConstantBits]
  | succ width ih =>
    cases count with
    | zero => simp [constantBits, xorConstantBits]
    | succ count =>
      have h := ih count (value / 2)
      simp only [constantBits] at h ⊢
      rw [Nat.succ_min_succ]
      simp only [List.replicate_succ, xorConstantBits]
      split <;> simp only [List.take_succ_cons, h]

/-- Bank preparation exposes the original little-endian input unchanged as a word. -/
theorem workRegistersPrepare_input_word (state : BasisState)
    (hwork1 : Clean (List.range' 4 259) state)
    (htail : Clean (List.range' 519 3) state) :
    wireValues (List.range' 266 256).reverse (run workRegistersPrepare state) =
      wireValues (List.range' 263 256) state := by
  have h := (workRegistersPrepare_correct state hwork1 htail).2.2.2.2.2.1
  apply List.ext_getElem
  · simp [wireValues]
  · intro i hi hj
    simp only [wireValues, List.length_map, List.length_reverse, List.length_range'] at hi hj
    simp only [wireValues, List.getElem_map, List.getElem_reverse,
      List.length_range', List.getElem_range', Nat.one_mul]
    have hx := h ⟨255-i, by omega⟩
    simpa only [show 256-1-i = 255-i by omega,
      show 518-(255-i) = 263+i by omega] using hx

/-- The lower 254 modulus bits are available for the length initializer's MCX lowering. -/
theorem workRegistersPrepare_known_scratch (state : BasisState)
    (hwork1 : Clean (List.range' 4 259) state)
    (htail : Clean (List.range' 519 3) state) :
    wireValues ((List.range' 7 256).reverse.take 254) (run workRegistersPrepare state) =
      constantBits 254 (2 ^ 256 - 2 ^ 32 - 977) := by
  have h := (workRegistersPrepare_correct state hwork1 htail).2.2.2.1
  rw [wireValues, List.map_take, ← wireValues, h, constantBits_take]
  rfl

private theorem preprocessCenter_layout :
    ([560,561,562,2] ++ (List.range' 266 256).reverse ++ List.range' 4 256).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨by decide,
    by simpa using (List.nodup_range' (s := 266) (n := 256)), ?_⟩,
    List.nodup_range', ?_⟩
  · intro a ha b hb he
    simp at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  · intro a ha b hb he
    simp at ha hb
    rcases ha with ha | ha
    · rcases ha with rfl | rfl | rfl | rfl; omega
    · omega

/-- The deterministic state described by the complete preprocessing prefix. -/
def eeaPreprocessIdealState (state : BasisState) : BasisState :=
  run eeaLengthSetup (eeaCenterIdealState (List.range' 266 256).reverse
    (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977) 2
      (run workRegistersPrepare state))

private theorem preprocessCenter_clean (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (wire : Wire) (hw : wire ∈ [560,561,562,2,558]) :
    run workRegistersPrepare state wire = false := by
  have hwork1 : Clean (List.range' 4 259) state := by
    intro w hw; exact hclean w (by simp at hw ⊢; omega)
  have htail : Clean (List.range' 519 3) state := by
    intro w hw; exact hclean w (by simp at hw ⊢; omega)
  rw [(workRegistersPrepare_correct state hwork1 htail).2.2.2.2.2.2 wire (by
    simp at hw ⊢; rcases hw with rfl | rfl | rfl | rfl | rfl <;> omega)]
  apply hclean
  simp at hw ⊢
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem preprocessScratch_bounds (wire : Wire)
    (hw : wire ∈ (List.range' 7 256).reverse.take 254) : (7 : Nat) ≤ wire ∧ wire < (263 : Nat) := by
  have h := List.mem_of_mem_take hw
  simpa using h

private theorem preprocessLength_layout :
    ComputeControlLayout (List.range' 266 256) 558
      ((List.range' 7 256).reverse.take 254) := by
  constructor
  · simp
  · apply List.nodup_append.mpr
    refine ⟨List.nodup_range', List.nodup_cons.mpr ⟨?_, ?_⟩, ?_⟩
    · intro hw; have h := preprocessScratch_bounds 558 hw; norm_num at h
    · exact (show (List.range' 7 256).reverse.Nodup by
        simpa using (List.nodup_range' (s := 7) (n := 256))).take
    · intro a ha b hb he
      subst b
      simp at ha hb
      rcases hb with rfl | hb
      · omega
      · exact Nat.not_lt_of_ge (Nat.le_trans (by decide : 263 ≤ 266) ha.1) (preprocessScratch_bounds a hb).2

private theorem preprocessLength_targets :
    ∀ wire ∈ List.range' 549 9, wire ∉ List.range' 266 256 ∧ wire ≠ 558 ∧
      wire ∉ (List.range' 7 256).reverse.take 254 := by
  intro wire hw
  have hs : wire ∉ (List.range' 7 256).reverse.take 254 := by
    intro hm; simp at hw
    exact Nat.not_lt_of_ge (Nat.le_trans (by decide : 263 ≤ 549) hw.1) (preprocessScratch_bounds wire hm).2
  refine ⟨?_, ?_, hs⟩ <;> simp at hw ⊢ <;> omega

private theorem preprocessWord_congr (wires : List Wire) (left right : BasisState)
    (h : ∀ w ∈ wires, left w = right w) : wireValues wires left = wireValues wires right :=
  List.map_congr_left h

private theorem preprocess_findIdx_congr (wires : List Wire) (left right : BasisState)
    (h : ∀ w ∈ wires, left w = right w) : wires.findIdx left = wires.findIdx right := by
  have hm := preprocessWord_congr wires left right h
  simpa only [wireValues, List.findIdx_map, Function.comp_def] using congrArg (List.findIdx id) hm

private theorem preprocessWord_clean (wires : List Wire) (state : BasisState)
    (h : Clean wires state) : wireValues wires state = List.replicate wires.length false := by
  induction wires with
  | nil => rfl
  | cons w ws ih =>
    simp only [wireValues, List.map_cons, List.length_cons, List.replicate_succ]
    exact congrArg₂ List.cons (h w (by simp)) (ih (fun v hv => h v (by simp [hv])))

/-- Length initialization sets both zero-length sentinels and the divisor length,
restoring its flag and known modulus scratch, with a complete frame. -/
theorem eeaLengthSetup_correct (state : BasisState)
    (hknown : wireValues ((List.range' 7 256).reverse.take 254) state =
      constantBits 254 (2 ^ 256 - 2 ^ 32 - 977))
    (hflag : state 558 = false)
    (hq : Clean (List.range' 531 9) state) (hs : Clean (List.range' 540 9) state)
    (hrp : Clean (List.range' 549 9) state) :
    wireValues (List.range' 531 9) (run eeaLengthSetup state) = constantBits 9 511 ∧
    wireValues (List.range' 540 9) (run eeaLengthSetup state) = constantBits 9 511 ∧
    wireValues (List.range' 549 9) (run eeaLengthSetup state) = constantBits 9
      (if (List.range' 266 256).findIdx state < 256
       then 255 - (List.range' 266 256).findIdx state else 511) ∧
    ∀ wire, wire ∉ List.range' 531 27 → run eeaLengthSetup state wire = state wire := by
  let first := run (xorConstant (List.range' 531 9) 511) state
  let second := run (xorConstant (List.range' 540 9) 511) first
  have hfirst := xorConstant_correct (List.range' 531 9) 511 state List.nodup_range'
  have hsecond := xorConstant_correct (List.range' 540 9) 511 first List.nodup_range'
  have hframe : ∀ w, w ∉ List.range' 531 18 → second w = state w := by
    intro w hw
    exact (hsecond.2 w (by simp at hw ⊢; omega)).trans
      (hfirst.2 w (by simp at hw ⊢; omega))
  have hk : wireValues ((List.range' 7 256).reverse.take 254) second =
      constantBits ((List.range' 7 256).reverse.take 254).length (2 ^ 256 - 2 ^ 32 - 977) := by
    rw [preprocessWord_congr _ second state (by
      intro w hw; exact hframe w (by
        simp only [List.mem_range', Nat.one_mul]
        intro hm
        obtain ⟨i, hi, he⟩ := hm
        exact Nat.not_lt_of_ge (Nat.le_trans (by decide : 263 ≤ 531) (by omega))
          (preprocessScratch_bounds w hw).2))]
    simpa using hknown
  have hf : second 558 = false := (hframe 558 (by decide)).trans hflag
  have hi : (List.range' 266 256).findIdx second = (List.range' 266 256).findIdx state := by
    have hword := preprocessWord_congr (List.range' 266 256) second state (by
      intro w hw; exact hframe w (by simp at hw ⊢; omega))
    have h := congrArg (List.findIdx id) hword
    simpa only [wireValues, List.findIdx_map, Function.comp_def] using h
  have hlast := lengthInitialize_correct (List.range' 266 256) (List.range' 549 9) 558
    ((List.range' 7 256).reverse.take 254) (2 ^ 256 - 2 ^ 32 - 977) second
    List.nodup_range' preprocessLength_layout preprocessLength_targets hk hf
  simp only [eeaLengthSetup, Classical.run_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [preprocessWord_congr _ _ second (by
      intro w hw; exact hlast.2 w (by simp at hw ⊢; omega))]
    rw [preprocessWord_congr _ second first (by
      intro w hw; exact hsecond.2 w (by simp at hw ⊢; omega))]
    rw [hfirst.1, preprocessWord_clean _ state hq]
    rfl
  · rw [preprocessWord_congr _ _ second (by
      intro w hw; exact hlast.2 w (by simp at hw ⊢; omega))]
    rw [hsecond.1, preprocessWord_congr _ first state (by
      intro w hw; exact hfirst.2 w (by simp at hw ⊢; omega)), preprocessWord_clean _ state hs]
    rfl
  · rw [hlast.1, preprocessWord_congr _ second state (by
      intro w hw; exact hframe w (by simp at hw ⊢; omega)), preprocessWord_clean _ state hrp, hi]
    simp only [List.length_range']
    congr 2
    omega
  · intro w hw
    exact (hlast.2 w (by simp at hw ⊢; omega)).trans (hframe w (by simp at hw ⊢; omega))

private theorem eeaLengthSetup_HPFree : HPFree eeaLengthSetup := by
  simp only [eeaLengthSetup, hpFree_append]
  exact ⟨⟨xorConstant_HPFree _ _, xorConstant_HPFree _ _⟩, lengthInitialize_HPFree _ _ _ _ _⟩

attribute [local irreducible] eeaCenter eeaLengthSetup eeaCenterIdealState

/-- Every actual preprocessing branch realizes the same complete state with
positive amplitude, including all measurement corrections inside centering. -/
theorem eeaPreprocess_branch_correct (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (branch : InstrumentBranch) (hb : branch ∈ eeaPreprocess.run) :
    branch.kraus (ket state) = registerXResetMagnitude branch.history.length •
      ket (eeaPreprocessIdealState state) := by
  obtain ⟨rest, hr, hh, hk⟩ := gidneyUnitaryBranch _ _ branch hb
  rw [hk, Quantum.run_ket_agrees_classical _ _ workRegistersPrepare_resources.2.1, hh]
  apply horner_seq_branch _ _ (run workRegistersPrepare state)
    (eeaCenterIdealState (List.range' 266 256).reverse
      (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977) 2
      (run workRegistersPrepare state)) (eeaPreprocessIdealState state) _ _ rest hr
  · intro b hb
    exact eeaCenter_branch_correct _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp)
      preprocessCenter_layout
      (preprocessCenter_clean state hclean 560 (by simp))
      (preprocessCenter_clean state hclean 561 (by simp))
      (preprocessCenter_clean state hclean 562 (by simp)) b hb
  · intro b hb
    obtain ⟨last, hl, hhistory, hrun⟩ := gidneyUnitaryBranch _ _ b hb
    have hd := gidneyDoneBranch last hl
    rw [hrun, hd.2, Quantum.run_ket_agrees_classical _ _ eeaLengthSetup_HPFree,
      hhistory, hd.1]
    simp only [List.length_nil, registerXResetMagnitude, pow_zero, one_smul]
    rfl

attribute [local irreducible] eeaPreprocessIdealState

/-- Complete arithmetic and register postconditions of the concrete preprocessing
prefix. This initializes the EEA state; it does not assume or establish iteration readiness. -/
theorem eeaPreprocessIdealState_correct (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977) :
    let after := eeaPreprocessIdealState state
    let x := boolWordToNat (wireValues (List.range' 263 256) state)
    boolWordToNat (wireValues (List.range' 266 256).reverse after) =
      min x (2 ^ 256 - 2 ^ 32 - 977 - x) ∧
    0 < boolWordToNat (wireValues (List.range' 266 256).reverse after) ∧
    boolWordToNat (wireValues (List.range' 266 256).reverse after) ≤
      (2 ^ 256 - 2 ^ 32 - 977) / 2 ∧
    after 2 = decide ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1 ≤ x) ∧
    after 4 = true ∧ after 5 = false ∧ after 6 = false ∧
    wireValues (List.range' 7 256).reverse after = constantBits 256 (2 ^ 256 - 2 ^ 32 - 977) ∧
    (∀ i : Fin 3, after (263+i.val) = false) ∧
    wireValues (List.range' 531 9) after = constantBits 9 511 ∧
    wireValues (List.range' 540 9) after = constantBits 9 511 ∧
    wireValues (List.range' 549 9) after = constantBits 9
      (if (List.range' 266 256).findIdx after < 256
       then 255 - (List.range' 266 256).findIdx after else 511) ∧
    Clean (List.range' 522 9 ++ [0,1,3] ++ List.range' 558 22) after ∧
    (∀ w, w ∉ 2 :: List.range' 4 554 → after w = state w) := by
  let prepared := run workRegistersPrepare state
  let centered := eeaCenterIdealState (List.range' 266 256).reverse
    (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977) 2 prepared
  have hw1 : Clean (List.range' 4 259) state := by
    intro w hw; exact hclean w (by simp at hw ⊢; omega)
  have htail : Clean (List.range' 519 3) state := by
    intro w hw; exact hclean w (by simp at hw ⊢; omega)
  have hp := workRegistersPrepare_correct state hw1 htail
  have hw := workRegistersPrepare_input_word state hw1 htail
  have hc := eeaCenterIdealState_correct (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977) 560 561 562 2
    prepared (by simp) (by simp) preprocessCenter_layout (by simp)
    (by rw [boolWordToNat_constantBits]; exact Nat.mod_eq_of_lt (by decide))
    (by change 0 < boolWordToNat (wireValues _ (run workRegistersPrepare state)); rw [hw]; exact hx)
    (by change boolWordToNat (wireValues _ (run workRegistersPrepare state)) < _; rw [hw]; exact hxp)
    (preprocessCenter_clean state hclean 2 (by simp))
  have hcf : ∀ w, w ∉ List.range' 266 256 → w ≠ 2 → centered w = prepared w := by
    intro w hw hn; exact hc.2.2.2.2 w (by simpa using hw) hn
  have hknown : wireValues ((List.range' 7 256).reverse.take 254) centered =
      constantBits 254 (2 ^ 256 - 2 ^ 32 - 977) := by
    rw [preprocessWord_congr _ centered prepared (by
      intro w hw
      have hb := preprocessScratch_bounds w hw
      apply hcf w
      · intro hm; simp at hm
        exact Nat.not_lt_of_ge (Nat.le_trans (by decide : 263 ≤ 266) hm.1) hb.2
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 7) hb.1))]
    exact workRegistersPrepare_known_scratch state hw1 htail
  have hcleanLengths : Clean (List.range' 522 36) centered := by
    intro w hw
    rw [hcf w (by simp at hw ⊢; omega) (by simp at hw; omega)]
    change run workRegistersPrepare state w = false
    rw [hp.2.2.2.2.2.2 w (by simp at hw ⊢; omega)]
    exact hclean w (by simp at hw ⊢; omega)
  have hflag : centered 558 = false := (hcf 558 (by decide) (by decide)).trans
    (preprocessCenter_clean state hclean 558 (by simp))
  have hl := eeaLengthSetup_correct centered hknown hflag
    (fun w hw => hcleanLengths w (by simp at hw ⊢; omega))
    (fun w hw => hcleanLengths w (by simp at hw ⊢; omega))
    (fun w hw => hcleanLengths w (by simp at hw ⊢; omega))
  have hlf : ∀ w, w ∉ List.range' 531 27 → eeaPreprocessIdealState state w = centered w := by
    simpa only [eeaPreprocessIdealState] using hl.2.2.2
  have hword : wireValues (List.range' 266 256).reverse (eeaPreprocessIdealState state) =
      wireValues (List.range' 266 256).reverse centered := by
    apply preprocessWord_congr
    intro w hw; exact hlf w (by simp at hw ⊢; omega)
  have hsmall : ∀ w, w ∈ List.range' 4 262 → eeaPreprocessIdealState state w = prepared w := by
    intro w hw
    exact (hlf w (by simp at hw ⊢; omega)).trans
      (hcf w (by simp at hw ⊢; omega) (by simp at hw; omega))
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hword]; exact hc.1.trans (by rw [show wireValues _ prepared = _ from hw])
  · rw [hword]; exact hc.2.1
  · rw [hword]; exact hc.2.2.1
  · rw [hlf 2 (by decide)]
    change eeaCenterIdealState _ _ _ _ _ 2 = _
    rw [hc.2.2.2.1]
    exact congrArg (fun v => decide ((2 ^ 256 - 2 ^ 32 - 977) / 2 + 1 ≤ boolWordToNat v)) hw
  · exact (hsmall 4 (by decide)).trans hp.1
  · exact (hsmall 5 (by decide)).trans hp.2.1
  · exact (hsmall 6 (by decide)).trans hp.2.2.1
  · rw [preprocessWord_congr _ _ prepared (by
      intro w hw; exact hsmall w (by simp at hw ⊢; omega))]
    exact hp.2.2.2.1
  · intro i
    exact (hsmall (263+i.val) (by simp; omega)).trans (hp.2.2.2.2.1 i)
  · simpa only [eeaPreprocessIdealState] using hl.1
  · simpa only [eeaPreprocessIdealState] using hl.2.1
  · have hidx : (List.range' 266 256).findIdx (eeaPreprocessIdealState state) =
        (List.range' 266 256).findIdx centered := by
      exact preprocess_findIdx_congr _ _ _ (fun w hw => hlf w (by simp at hw ⊢; omega))
    rw [hidx]; simpa only [eeaPreprocessIdealState] using hl.2.2.1
  · intro w hw
    have hf : w ∉ List.range' 531 27 ∧ w ∉ List.range' 266 256 ∧ w ≠ 2 ∧
        w ∉ List.range' 4 518 ∧ w ∈ List.range' 0 263 ++ List.range' 519 61 := by
      simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · simp at hw
        have hn : w ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hw.1)
        simp [hn]
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> decide
      · simp at hw
        have hn : w ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hw.1)
        simp [hn]
        omega
    rw [hlf w hf.1, hcf w hf.2.1 hf.2.2.1]
    exact (hp.2.2.2.2.2.2 w hf.2.2.2.1).trans (hclean w hf.2.2.2.2)
  · intro w hw
    have hw' : w ≠ 2 ∧ w ∉ List.range' 4 554 := by simpa using hw
    rw [hlf w (by simp at hw' ⊢; omega), hcf w (by simp at hw' ⊢; omega) hw'.1]
    exact hp.2.2.2.2.2.2 w (by simp at hw' ⊢; omega)

/-- All gates in the actual preprocessing prefix have distinct operands. -/
theorem eeaPreprocess_wellFormed : eeaPreprocess.WellFormed := by
  have hl : CircuitWellFormed eeaLengthSetup := by
    simp only [eeaLengthSetup, circuitWellFormed_append]
    refine ⟨⟨xorConstant_wellFormed _ _, xorConstant_wellFormed _ _⟩, ?_⟩
    exact lengthInitialize_wellFormed _ _ _ _ _ preprocessLength_layout
      (fun w hw => Ne.symm (preprocessLength_targets w hw).2.1)
  have hc := (eeaCenter_wellFormed (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977)
    560 561 562 2 (by simp) (by simp) (by simp) preprocessCenter_layout).1
  exact ⟨workRegistersPrepare_resources.1, hc.seq ⟨hl, trivial⟩⟩

/-- Length setup reuses only the existing 580-role allocation. -/
theorem eeaLengthSetup_usesOnly : PaperCircuitUsesOnly (List.range 580) eeaLengthSetup := by
  have hq : PaperCircuitUsesOnly (List.range 580) (xorConstant (List.range' 531 9) 511) :=
    (xorConstant_usesOnly (List.range' 531 9) 511).mono (by
    intro w hw; simp at hw ⊢; omega)
  have hs : PaperCircuitUsesOnly (List.range 580) (xorConstant (List.range' 540 9) 511) :=
    (xorConstant_usesOnly (List.range' 540 9) 511).mono (by
    intro w hw; simp at hw ⊢; omega)
  have hl : PaperCircuitUsesOnly (List.range 580)
      (lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
        ((List.range' 7 256).reverse.take 254) (2 ^ 256 - 2 ^ 32 - 977)) :=
    (lengthInitialize_usesOnly _ _ _ _ _ preprocessLength_layout).mono (by
      intro w hw
      simp only [List.mem_append, List.mem_cons] at hw
      rcases hw with (hw | hw) | hw | hw
      · simp at hw ⊢; omega
      · simp at hw ⊢; omega
      · subst w; decide
      · have h := (preprocessScratch_bounds w hw).2
        exact List.mem_range.mpr (Nat.lt_trans h (by decide)))
  simpa only [eeaLengthSetup] using (hq.append hs).append hl

end
end ShorECDLP.Paper2607_13816
