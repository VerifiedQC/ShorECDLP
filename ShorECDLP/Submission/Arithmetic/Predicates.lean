import ShorECDLP.Submission.Arithmetic.Primitives

/-!
# Clean reversible register predicates

This module supplies the clean zero and equality flags needed by affine point-addition branch
selection. Both programs use only `X`, `CX`, and `CCX`, preserve their public inputs, and restore
all scratch wires.

## Programs (syntax-sugared)

For a nonempty `input = [x₀, ..., xₙ₋₁]`, `zeroCompute` fills an equally long clean history
register from the tail toward the head:

```text
history[n - 1] ^= NOT input[n - 1]
for i = n - 2 downto 0:
  history[i] ^= history[i + 1] AND NOT input[i]
```

Thus `history[0]` says that every input bit is zero. `zeroFlag` CNOT-copies that bit to a clean
flag and reverses `zeroCompute`. For the empty input, it flips the flag directly. `equalFlag`
first CNOT-computes `lhs XOR rhs` in a clean difference register, runs the same zero test, and
then reverses the XOR computation.

## Specifications

On duplicate-free layouts with equally long aligned registers and clean flag/work wires:

```text
zeroFlag:  flag = (value(input) = 0), input preserved, history restored clean
equalFlag: flag = (value(lhs) = value(rhs)), lhs/rhs preserved, difference/history clean
```

Both programs have exact T-count `14 * (width - 1)`: the only non-Clifford gates are the
`width - 1` Toffolis in `zeroCompute`, executed once forward and once backward.
-/

namespace ShorECDLP
namespace Arithmetic

/-- Boolean recurrence for the zero predicate on an LSB-first register. -/
theorem decide_regValue_cons_zero (x : Wire) (xs : List Wire) (st : BasisState) :
    decide (regValue (x :: xs) st = 0) =
      (!st x && decide (regValue xs st = 0)) := by
  rw [regValue_cons]
  by_cases hx : st x <;> simp [hx] <;> omega

/-- A natural-valued register is zero exactly when every one of its wires is clean. -/
theorem regValue_eq_zero_iff_clean (ws : List Wire) (st : BasisState) :
    regValue ws st = 0 ↔ Clean ws st := by
  induction ws with
  | nil => simp [Clean]
  | cons w ws ih =>
      rw [regValue_cons]
      constructor
      · intro hzero a ha
        simp only [List.mem_cons] at ha
        rcases ha with ha | ha
        · subst a
          by_cases hw : st w
          · simp [hw] at hzero
          · exact Bool.eq_false_iff.mpr hw
        · have htail : regValue ws st = 0 := by
            by_cases hw : st w <;> simp [hw] at hzero ⊢ <;> omega
          exact ih.mp htail a ha
      · intro hclean
        have hw := hclean w (List.mem_cons_self ..)
        have htail : Clean ws st := fun a ha => hclean a (List.mem_cons_of_mem w ha)
        rw [hw, ih.mpr htail]
        simp

/-- Equal-width registers have equal values exactly when their aligned bit lists agree. -/
theorem regValue_eq_iff_map_eq (lhs rhs : List Wire) (st : BasisState)
    (hlen : rhs.length = lhs.length) :
    regValue lhs st = regValue rhs st ↔ lhs.map st = rhs.map st := by
  induction lhs generalizing rhs with
  | nil =>
      have : rhs = [] := List.length_eq_zero_iff.mp hlen
      subst rhs
      simp
  | cons a lhs ih =>
      cases rhs with
      | nil => simp at hlen
      | cons b rhs =>
          have htail : rhs.length = lhs.length := by simpa using hlen
          simp only [List.map_cons, List.cons.injEq]
          constructor
          · intro heq
            have hab : st a = st b := by
              rw [regValue_cons, regValue_cons] at heq
              cases ha : st a <;> cases hb : st b <;>
                simp [ha, hb] at heq ⊢ <;> omega
            refine ⟨hab, (ih rhs htail).mp ?_⟩
            rw [regValue_cons, regValue_cons, hab] at heq
            omega
          · rintro ⟨hab, htailEq⟩
            rw [regValue_cons, regValue_cons, hab, (ih rhs htail).mpr htailEq]

private theorem clean_iff_map_false (ws : List Wire) (st : BasisState) :
    Clean ws st ↔ ws.map st = List.replicate ws.length false := by
  induction ws with
  | nil => simp [Clean]
  | cons w ws ih =>
      simp only [Clean, List.mem_cons, forall_eq_or_imp, List.map_cons,
        List.length_cons, List.replicate_succ, List.cons.injEq]
      exact and_congr Iff.rfl ih

private theorem zipWith_xor_eq_false_iff (as bs : List Bool)
    (hlen : bs.length = as.length) :
    List.zipWith Bool.xor as bs = List.replicate as.length false ↔ as = bs := by
  induction as generalizing bs with
  | nil =>
      have : bs = [] := List.length_eq_zero_iff.mp hlen
      subst bs
      simp
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have htail : bs.length = as.length := by simpa using hlen
          simp only [List.zipWith_cons_cons, List.length_cons, List.replicate_succ,
            List.cons.injEq]
          rw [ih bs htail]
          cases a <;> cases b <;> simp

private theorem zipWith_xor_false_left (bits : List Bool) :
    List.zipWith Bool.xor (List.replicate bits.length false) bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons,
        Bool.false_xor, List.cons.injEq, true_and]
      exact ih

/-- Pointwise semantics of CNOT-copying an aligned register into an arbitrary destination. -/
theorem copyReg_target_map :
    ∀ (src dst : List Wire) (st : BasisState),
      dst.length = src.length → (src ++ dst).Nodup →
      dst.map (Classical.run (copyReg src dst) st) =
        List.zipWith Bool.xor (dst.map st) (src.map st) := by
  intro src
  induction src with
  | nil =>
      intro dst st hlen _
      have : dst = [] := List.length_eq_zero_iff.mp hlen
      subst dst
      rfl
  | cons s src ih =>
      intro dst st hlen hnd
      cases dst with
      | nil => simp at hlen
      | cons d dst =>
          have hlenTail : dst.length = src.length := by simpa using hlen
          obtain ⟨hsrcNd, hdstNd, hcross⟩ := List.nodup_append.mp hnd
          have hsrcTailNd : src.Nodup := (List.nodup_cons.mp hsrcNd).2
          have hdDst : d ∉ dst := (List.nodup_cons.mp hdstNd).1
          have hdstTailNd : dst.Nodup := (List.nodup_cons.mp hdstNd).2
          have htailNd : (src ++ dst).Nodup := List.nodup_append.mpr
            ⟨hsrcTailNd, hdstTailNd,
              fun a ha b hb => hcross a (List.mem_cons_of_mem s ha)
                b (List.mem_cons_of_mem d hb)⟩
          have hdSrc : d ∉ src := by
            intro hd
            exact hcross d (List.mem_cons_of_mem s hd) d (List.mem_cons_self ..) rfl
          let st₁ := Classical.applyGate (Gate.CX s d) st
          have hsrcMap : src.map st₁ = src.map st := by
            apply List.map_congr_left
            intro w hw
            exact upd_other st d (Bool.xor (st d) (st s)) (fun e => hdSrc (e ▸ hw))
          have hdstMap : dst.map st₁ = dst.map st := by
            apply List.map_congr_left
            intro w hw
            exact upd_other st d (Bool.xor (st d) (st s)) (fun e => hdDst (e ▸ hw))
          have htail := ih dst st₁ hlenTail htailNd
          have hdFinal :
              Classical.run (copyReg src dst) st₁ d = Bool.xor (st d) (st s) := by
            rw [copyReg_other d src dst st₁ hdDst]
            simp [st₁, Classical.applyGate]
          rw [copyReg, Classical.run_cons]
          simp only [List.map_cons, List.zipWith_cons_cons]
          rw [hdFinal, htail, hsrcMap, hdstMap]

/-- XORing two equal-width registers into clean scratch is zero exactly when their values agree. -/
theorem xorCopies_zero_iff (lhs rhs difference : List Wire) (st : BasisState)
    (hrlen : rhs.length = lhs.length)
    (hdlen : difference.length = lhs.length)
    (hnd : ((lhs ++ rhs) ++ difference).Nodup)
    (hclean : Clean difference st) :
    let st₁ := Classical.run (copyReg lhs difference) st
    let st₂ := Classical.run (copyReg rhs difference) st₁
    regValue difference st₂ = 0 ↔ regValue lhs st = regValue rhs st := by
  obtain ⟨hlrNd, hdNd, hlrDiff⟩ := List.nodup_append.mp hnd
  obtain ⟨hlNd, hrNd, _⟩ := List.nodup_append.mp hlrNd
  have hld : (lhs ++ difference).Nodup := List.nodup_append.mpr
    ⟨hlNd, hdNd, fun a ha b hb => hlrDiff a (List.mem_append_left rhs ha) b hb⟩
  have hrd : (rhs ++ difference).Nodup := List.nodup_append.mpr
    ⟨hrNd, hdNd, fun a ha b hb => hlrDiff a (List.mem_append_right lhs ha) b hb⟩
  let st₁ := Classical.run (copyReg lhs difference) st
  let st₂ := Classical.run (copyReg rhs difference) st₁
  have hcopyL := copyReg_target_map lhs difference st hdlen hld
  have hdiffCleanMap := (clean_iff_map_false difference st).mp hclean
  have hdiffSt₁ : difference.map st₁ = lhs.map st := by
    change difference.map (Classical.run (copyReg lhs difference) st) = lhs.map st
    rw [hcopyL, hdiffCleanMap, hdlen]
    simpa using zipWith_xor_false_left (lhs.map st)
  have hrhsSt₁ : rhs.map st₁ = rhs.map st := by
    apply List.map_congr_left
    intro w hw
    change Classical.run (copyReg lhs difference) st w = st w
    apply copyReg_other
    intro hd
    exact hlrDiff w (List.mem_append_right lhs hw) w hd rfl
  have hdrlen : difference.length = rhs.length := hdlen.trans hrlen.symm
  have hcopyR := copyReg_target_map rhs difference st₁ hdrlen hrd
  have hdiffSt₂ :
      difference.map st₂ = List.zipWith Bool.xor (lhs.map st) (rhs.map st) := by
    change difference.map (Classical.run (copyReg rhs difference) st₁) = _
    rw [hcopyR, hdiffSt₁, hrhsSt₁]
  have hxor :
      List.zipWith Bool.xor (lhs.map st) (rhs.map st) =
          List.replicate lhs.length false ↔ lhs.map st = rhs.map st := by
    simpa using zipWith_xor_eq_false_iff (lhs.map st) (rhs.map st) (by
      simpa using hrlen)
  change regValue difference st₂ = 0 ↔ regValue lhs st = regValue rhs st
  rw [regValue_eq_zero_iff_clean, clean_iff_map_false, hdiffSt₂, hdlen,
    hxor, regValue_eq_iff_map_eq lhs rhs st hrlen]

/-- Tail-first conjunction history. Its first history bit is the zero predicate. -/
def zeroCompute : List Wire → List Wire → Circuit
  | [x], h :: _ => [Gate.X h, Gate.CX x h]
  | x :: x' :: xs, h :: h' :: hs =>
      zeroCompute (x' :: xs) (h' :: hs) ++
        [Gate.X x, Gate.CCX h' x h, Gate.X x]
  | _, _ => []

@[simp]
theorem zeroCompute_HPFree (input history : List Wire) :
    Classical.HPFree (zeroCompute input history) := by
  fun_induction zeroCompute input history with
  | case1 => simp
  | case2 x x' xs h h' hs ih =>
      exact (Classical.hpFree_append _ _).mpr ⟨ih, by simp⟩
  | case3 => simp

theorem zeroCompute_tCount (input history : List Wire)
    (hlen : history.length = input.length) :
    tCount (zeroCompute input history) = 7 * (input.length - 1) := by
  induction input generalizing history with
  | nil =>
      have : history = [] := List.length_eq_zero_iff.mp hlen
      subst history
      rfl
  | cons x input ih =>
      cases input with
      | nil =>
          have hhist : history.length = 1 := by simpa using hlen
          obtain ⟨h, rfl⟩ := List.length_eq_one_iff.mp hhist
          rfl
      | cons x' xs =>
          cases history with
          | nil => simp at hlen
          | cons h history =>
              cases history with
              | nil => simp at hlen
              | cons h' hs =>
                  have htail : hs.length = xs.length := by simpa using hlen
                  rw [zeroCompute, tCount_append, ih (h' :: hs) (by simp [htail])]
                  simp [tCount, tCost]
                  omega

/-- `zeroCompute` reads and writes only its input and history registers. -/
theorem zeroCompute_usesOnly (input history : List Wire) :
    CircuitUsesOnly (input ++ history) (zeroCompute input history) := by
  fun_induction zeroCompute input history with
  | case1 x h hs =>
      simp [CircuitUsesOnly, Gate.UsesOnly]
  | case2 x x' xs h h' hs ih =>
      apply usesOnly_append
      · apply usesOnly_mono ih
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem x hw))
        · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem h hw))
      · simpa using (show CircuitUsesOnly ((x :: x' :: xs) ++ (h :: h' :: hs))
          ([Gate.X x, Gate.CCX h' x h, Gate.X x] : Circuit) by
            simp [CircuitUsesOnly, Gate.UsesOnly])
  | case3 => simp [CircuitUsesOnly]

/-- Duplicate-free input/history wires make every Toffoli role physically distinct. -/
theorem zeroCompute_wellFormed (input history : List Wire)
    (hnd : (input ++ history).Nodup) :
    CircuitWellFormed (zeroCompute input history) := by
  fun_induction zeroCompute input history with
  | case1 x h hs =>
      obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hnd
      have hxh : x ≠ h := hcross x (by simp) h (by simp)
      simpa [CircuitWellFormed, Gate.WellFormed] using hxh
  | case2 x x' xs h h' hs ih =>
      obtain ⟨hin, hhist, hcross⟩ := List.nodup_append.mp hnd
      have hinTail : (x' :: xs).Nodup := (List.nodup_cons.mp hin).2
      have hhistTail : (h' :: hs).Nodup := (List.nodup_cons.mp hhist).2
      have htail : ((x' :: xs) ++ (h' :: hs)).Nodup :=
        List.nodup_append.mpr ⟨hinTail, hhistTail, fun a ha b hb => hcross a
          (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem h hb)⟩
      have hx_h' : x ≠ h' := hcross x (by simp) h' (by simp)
      have hx_h : x ≠ h := hcross x (by simp) h (by simp)
      have hh_h' : h ≠ h' := fun e => (List.nodup_cons.mp hhist).1 (e ▸ by simp)
      rw [circuitWellFormed_append]
      exact ⟨ih htail, by
        simp [CircuitWellFormed, Gate.WellFormed, hx_h'.symm, hx_h, hh_h'.symm]⟩
  | case3 => simp [CircuitWellFormed]

/-- Forward semantic invariant: the first history bit is true exactly for the zero input. -/
theorem zeroCompute_head_correct (x : Wire) (xs : List Wire) (h : Wire)
    (hs : List Wire) (st : BasisState)
    (hlen : hs.length = xs.length)
    (hnd : ((x :: xs) ++ (h :: hs)).Nodup)
    (hclean : Clean (h :: hs) st) :
    let after := Classical.run (zeroCompute (x :: xs) (h :: hs)) st
    AgreesOn (x :: xs) st after ∧
      after h = decide (regValue (x :: xs) st = 0) := by
  induction xs generalizing x h hs st with
  | nil =>
      have : hs = [] := List.length_eq_zero_iff.mp hlen
      subst hs
      obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hnd
      have hxh : x ≠ h := hcross x (by simp) h (by simp)
      have hh : st h = false := hclean h (by simp)
      dsimp only
      constructor
      · intro w hw
        simp only [List.mem_singleton] at hw
        subst w
        simp [zeroCompute, Classical.run, Classical.applyGate, upd, hxh]
      · by_cases hx : st x <;>
          simp [zeroCompute, Classical.run, Classical.applyGate, upd, hxh, hh, hx,
            regValue_cons]
  | cons y ys ih =>
      cases hs with
      | nil => simp at hlen
      | cons k ks =>
          have hlenTail : ks.length = ys.length := by simpa using hlen
          obtain ⟨hin, hhist, hcross⟩ := List.nodup_append.mp hnd
          have hinTail : (y :: ys).Nodup := (List.nodup_cons.mp hin).2
          have hhistTail : (k :: ks).Nodup := (List.nodup_cons.mp hhist).2
          have htailNodup : ((y :: ys) ++ (k :: ks)).Nodup :=
            List.nodup_append.mpr ⟨hinTail, hhistTail, fun a ha b hb => hcross a
              (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem h hb)⟩
          have htailClean : Clean (k :: ks) st := fun w hw =>
            hclean w (List.mem_cons_of_mem h hw)
          have hih := ih y k ks st hlenTail htailNodup htailClean
          let tailInput : List Wire := y :: ys
          let tailHistory : List Wire := k :: ks
          let mid := Classical.run (zeroCompute tailInput tailHistory) st
          have hih' : AgreesOn tailInput st mid ∧
              mid k = decide (regValue tailInput st = 0) := by
            simpa [tailInput, tailHistory, mid] using hih
          have hxInput : x ∉ tailInput := by
            simpa [tailInput] using (List.nodup_cons.mp hin).1
          have hxHistory : x ∉ tailHistory := by
            intro hx
            exact hcross x (by simp) x (List.mem_cons_of_mem h hx) rfl
          have hxActive : x ∉ tailInput ++ tailHistory := by
            simpa [List.mem_append] using And.intro hxInput hxHistory
          have hhHistory : h ∉ tailHistory := by
            simpa [tailHistory] using (List.nodup_cons.mp hhist).1
          have hhInput : h ∉ tailInput := by
            intro hhmem
            exact hcross h (List.mem_cons_of_mem x hhmem) h (by simp) rfl
          have hhActive : h ∉ tailInput ++ tailHistory := by
            simpa [List.mem_append] using And.intro hhInput hhHistory
          have huses := zeroCompute_usesOnly tailInput tailHistory
          have hmidX : mid x = st x := huses.preservesOutside st x hxActive
          have hmidH : mid h = st h := huses.preservesOutside st h hhActive
          have hcleanH : st h = false := hclean h (by simp)
          have hxH : x ≠ h := hcross x (by simp) h (by simp)
          have hxK : x ≠ k := hcross x (by simp) k (by simp)
          rw [zeroCompute, Classical.run_append]
          change AgreesOn (x :: y :: ys) st
              (Classical.run ([Gate.X x, Gate.CCX k x h, Gate.X x] : Circuit) mid) ∧
            Classical.run ([Gate.X x, Gate.CCX k x h, Gate.X x] : Circuit) mid h =
              decide (regValue (x :: y :: ys) st = 0)
          constructor
          · intro w hw
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · simp [Classical.run, Classical.applyGate, upd, hxH, hmidX]
            · have hwTail : w ∈ tailInput := by simpa [tailInput] using hw
              have hwX : w ≠ x := fun e => hxInput (e ▸ hwTail)
              have hwH : w ≠ h := fun e => hhInput (e ▸ hwTail)
              calc
                Classical.run ([Gate.X x, Gate.CCX k x h, Gate.X x] : Circuit) mid w =
                    mid w := by
                      simp [Classical.run, Classical.applyGate, upd, hwX, hwH]
                _ = st w := hih'.1 w hwTail
          · calc
              Classical.run ([Gate.X x, Gate.CCX k x h, Gate.X x] : Circuit) mid h =
                  (!st x && decide (regValue tailInput st = 0)) := by
                    simp [Classical.run, Classical.applyGate, upd, hxH.symm, hxK.symm,
                      hmidX, hmidH, hcleanH, hih'.2, Bool.and_comm]
              _ = decide (regValue (x :: tailInput) st = 0) :=
                    (decide_regValue_cons_zero x tailInput st).symm
              _ = decide (regValue (x :: y :: ys) st = 0) := by
                    simp [tailInput]

/-- One-bit Bennett copy-out restores every active wire while retaining the copied result. -/
theorem bennett_cleanup_copyBit
    (compute : Circuit) (active : List Wire) (source flag : Wire) (st : BasisState)
    (huses : CircuitUsesOnly active compute)
    (hfree : Classical.HPFree compute)
    (hwf : CircuitWellFormed compute)
    (hflag : flag ∉ active)
    (hcleanFlag : st flag = false) :
    let after := Classical.run
      (compute ++ [Gate.CX source flag] ++ compute.reverse) st
    AgreesOn active st after ∧
      after flag = Classical.run compute st source := by
  let mid := Classical.run compute st
  let copied := Classical.applyGate (Gate.CX source flag) mid
  let after := Classical.run compute.reverse copied
  have hmidFlag : mid flag = false := by
    change Classical.run compute st flag = false
    rw [huses.preservesOutside st flag hflag]
    exact hcleanFlag
  have hcopyActive : ∀ w ∈ active, copied w = mid w := by
    intro w hw
    have hwFlag : w ≠ flag := fun e => hflag (e ▸ hw)
    simp [copied, Classical.applyGate, upd, hwFlag]
  have hreverseUses : CircuitUsesOnly active compute.reverse := usesOnly_reverse huses
  have hcancel : Classical.run compute.reverse mid = st := by
    simpa [mid] using run_reverse_cancel compute st hfree hwf
  have hafterActive : AgreesOn active st after := by
    intro w hw
    calc
      after w = Classical.run compute.reverse mid w := by
        change Classical.run compute.reverse copied w = Classical.run compute.reverse mid w
        exact CircuitUsesOnly.run_congr hreverseUses hcopyActive w hw
      _ = st w := by rw [hcancel]
  have hafterFlag : after flag = mid source := by
    calc
      after flag = copied flag := by
        change Classical.run compute.reverse copied flag = copied flag
        exact hreverseUses.preservesOutside copied flag hflag
      _ = mid source := by
        simp [copied, Classical.applyGate, hmidFlag]
  have hprogramRun :
      Classical.run (compute ++ [Gate.CX source flag] ++ compute.reverse) st = after := by
    simp [after, copied, mid, Classical.run_append]
  simp only [hprogramRun]
  exact ⟨hafterActive, hafterFlag⟩

/-- Full syntactic support of a clean zero flag. -/
def zeroFlagWires (input : List Wire) (flag : Wire) (history : List Wire) : List Wire :=
  input ++ flag :: history

/-- Clean reversible zero flag with a Bennett-restored conjunction history. -/
def zeroFlag : List Wire → Wire → List Wire → Circuit
  | [], flag, _ => [Gate.X flag]
  | x :: xs, flag, h :: hs =>
      let compute := zeroCompute (x :: xs) (h :: hs)
      compute ++ [Gate.CX h flag] ++ compute.reverse
  | _, _, _ => []

@[simp]
theorem zeroFlag_HPFree (input : List Wire) (flag : Wire) (history : List Wire) :
    Classical.HPFree (zeroFlag input flag history) := by
  cases input with
  | nil => simp [zeroFlag]
  | cons x xs =>
      cases history with
      | nil => simp [zeroFlag]
      | cons h hs =>
          rw [zeroFlag, Classical.hpFree_append, Classical.hpFree_append]
          exact ⟨⟨zeroCompute_HPFree _ _, by simp⟩,
            hpFree_reverse (zeroCompute_HPFree _ _)⟩

/-- A zero flag uses only its input, output flag, and conjunction history. -/
theorem zeroFlag_usesOnly (input : List Wire) (flag : Wire) (history : List Wire) :
    CircuitUsesOnly (zeroFlagWires input flag history) (zeroFlag input flag history) := by
  cases input with
  | nil => simp [zeroFlag, zeroFlagWires, CircuitUsesOnly, Gate.UsesOnly]
  | cons x xs =>
      cases history with
      | nil => simp [zeroFlag, CircuitUsesOnly]
      | cons h hs =>
          let compute := zeroCompute (x :: xs) (h :: hs)
          have hcompute :
              CircuitUsesOnly (zeroFlagWires (x :: xs) flag (h :: hs)) compute := by
            apply usesOnly_mono (zeroCompute_usesOnly (x :: xs) (h :: hs))
            intro w hw
            rcases List.mem_append.mp hw with hw | hw
            · exact List.mem_append.mpr (Or.inl hw)
            · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem flag hw))
          rw [zeroFlag]
          exact usesOnly_append (usesOnly_append hcompute (by
            simp [CircuitUsesOnly, Gate.UsesOnly, zeroFlagWires]))
            (usesOnly_reverse hcompute)

/-- Exact T-count of the clean zero flag. -/
theorem zeroFlag_tCount (input : List Wire) (flag : Wire) (history : List Wire)
    (hlen : history.length = input.length) :
    tCount (zeroFlag input flag history) = 14 * (input.length - 1) := by
  cases input with
  | nil => simp [zeroFlag, tCount, tCost]
  | cons x xs =>
      cases history with
      | nil => simp at hlen
      | cons h hs =>
          have htail : hs.length = xs.length := by simpa using hlen
          rw [zeroFlag, tCount_append, tCount_append, tCount_reverse,
            zeroCompute_tCount _ _ (by simp [htail])]
          simp [tCount, tCost]
          omega

/-- A duplicate-free zero-flag layout makes the complete compute/copy/uncompute circuit valid. -/
theorem zeroFlag_wellFormed (input : List Wire) (flag : Wire) (history : List Wire)
    (hnd : (zeroFlagWires input flag history).Nodup) :
    CircuitWellFormed (zeroFlag input flag history) := by
  cases input with
  | nil => simp [zeroFlag, CircuitWellFormed, Gate.WellFormed]
  | cons x xs =>
      cases history with
      | nil => simp [zeroFlag, CircuitWellFormed]
      | cons h hs =>
          obtain ⟨hin, hrest, hcross⟩ := List.nodup_append.mp hnd
          have hhist : (h :: hs).Nodup := (List.nodup_cons.mp hrest).2
          have hactive : ((x :: xs) ++ (h :: hs)).Nodup :=
            List.nodup_append.mpr ⟨hin, hhist, fun a ha b hb => hcross a ha b
              (List.mem_cons_of_mem flag hb)⟩
          have hflagH : flag ≠ h := fun e => (List.nodup_cons.mp hrest).1 (e ▸ by simp)
          rw [zeroFlag, circuitWellFormed_append, circuitWellFormed_append]
          exact ⟨⟨zeroCompute_wellFormed _ _ hactive, by
            simpa [CircuitWellFormed, Gate.WellFormed] using hflagH.symm⟩,
            wellFormed_reverse (zeroCompute_wellFormed _ _ hactive)⟩

/-- Clean zero-flag correctness, including public-input preservation and complete scratch cleanup. -/
theorem zeroFlag_correct (input : List Wire) (flag : Wire) (history : List Wire)
    (st : BasisState)
    (hlen : history.length = input.length)
    (hnd : (zeroFlagWires input flag history).Nodup)
    (hclean : Clean (flag :: history) st) :
    let after := Classical.run (zeroFlag input flag history) st
    AgreesOn input st after ∧
      after flag = decide (regValue input st = 0) ∧
      Clean history after := by
  cases input with
  | nil =>
      have : history = [] := List.length_eq_zero_iff.mp hlen
      subst history
      have hflag : st flag = false := hclean flag (by simp)
      simp [zeroFlag, AgreesOn, Clean, Classical.run, Classical.applyGate, hflag]
  | cons x xs =>
      cases history with
      | nil => simp at hlen
      | cons h hs =>
          have htail : hs.length = xs.length := by simpa using hlen
          obtain ⟨hin, hrest, hcross⟩ := List.nodup_append.mp hnd
          have hhist : (h :: hs).Nodup := (List.nodup_cons.mp hrest).2
          have hactive : ((x :: xs) ++ (h :: hs)).Nodup :=
            List.nodup_append.mpr ⟨hin, hhist, fun a ha b hb => hcross a ha b
              (List.mem_cons_of_mem flag hb)⟩
          have hflagOutside : flag ∉ (x :: xs) ++ (h :: hs) := by
            intro hw
            rcases List.mem_append.mp hw with hw | hw
            · exact hcross flag hw flag (by simp) rfl
            · exact (List.nodup_cons.mp hrest).1 hw
          have hhistoryClean : Clean (h :: hs) st := fun w hw =>
            hclean w (List.mem_cons_of_mem flag hw)
          have hflagClean : st flag = false := hclean flag (by simp)
          let compute := zeroCompute (x :: xs) (h :: hs)
          let active := (x :: xs) ++ (h :: hs)
          let after := Classical.run (zeroFlag (x :: xs) flag (h :: hs)) st
          have hforward := zeroCompute_head_correct x xs h hs st htail hactive hhistoryClean
          have hforward' :
              Classical.run compute st h = decide (regValue (x :: xs) st = 0) := by
            simpa [compute] using hforward.2
          have hcleanup : AgreesOn active st after ∧
              after flag = Classical.run compute st h := by
            simpa [active, after, compute, zeroFlag] using
              (bennett_cleanup_copyBit compute active h flag st
                (by simpa [compute, active] using zeroCompute_usesOnly (x :: xs) (h :: hs))
                (by simp [compute])
                (by simpa [compute] using
                  zeroCompute_wellFormed (x :: xs) (h :: hs) hactive)
                (by simpa [active] using hflagOutside) hflagClean)
          dsimp only
          change AgreesOn (x :: xs) st after ∧
            after flag = decide (regValue (x :: xs) st = 0) ∧
            Clean (h :: hs) after
          refine ⟨?_, hcleanup.2.trans hforward', ?_⟩
          · intro w hw
            exact hcleanup.1 w (List.mem_append.mpr (Or.inl hw))
          · intro w hw
            rw [hcleanup.1 w (List.mem_append.mpr (Or.inr hw))]
            exact hhistoryClean w hw

/-! ## Equality flag -/

/-- Forward equality computation: XOR both inputs into `difference`, then zero-test it. -/
def equalCompute (lhs rhs difference history : List Wire) : Circuit :=
  copyReg lhs difference ++ copyReg rhs difference ++ zeroCompute difference history

@[simp]
theorem equalCompute_HPFree (lhs rhs difference history : List Wire) :
    Classical.HPFree (equalCompute lhs rhs difference history) := by
  simp [equalCompute]

theorem equalCompute_tCount (lhs rhs difference history : List Wire)
    (hlen : history.length = difference.length) :
    tCount (equalCompute lhs rhs difference history) = 7 * (difference.length - 1) := by
  rw [equalCompute, tCount_append, tCount_append, copyReg_tCount, copyReg_tCount,
    zeroCompute_tCount _ _ hlen]
  omega

/-- Active compute/uncompute wires of an equality flag, excluding its copied-out result bit. -/
def equalComputeWires (lhs rhs difference history : List Wire) : List Wire :=
  ((lhs ++ rhs) ++ difference) ++ history

/-- The equality computation is confined to both inputs and its two scratch registers. -/
theorem equalCompute_usesOnly (lhs rhs difference history : List Wire) :
    CircuitUsesOnly (equalComputeWires lhs rhs difference history)
      (equalCompute lhs rhs difference history) := by
  apply usesOnly_append
  · apply usesOnly_append
    · apply copyReg_usesOnly
      · intro w hw
        simp [equalComputeWires, hw]
      · intro w hw
        simp [equalComputeWires, hw]
    · apply copyReg_usesOnly
      · intro w hw
        simp [equalComputeWires, hw]
      · intro w hw
        simp [equalComputeWires, hw]
  · apply usesOnly_mono (zeroCompute_usesOnly difference history)
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · simp [equalComputeWires, hw]
    · simp [equalComputeWires, hw]

theorem equalCompute_wellFormed (lhs rhs difference history : List Wire)
    (hnd : (equalComputeWires lhs rhs difference history).Nodup) :
    CircuitWellFormed (equalCompute lhs rhs difference history) := by
  obtain ⟨hlrdNd, hhistNd, hlrdHist⟩ := List.nodup_append.mp hnd
  obtain ⟨hlrNd, hdiffNd, hlrDiff⟩ := List.nodup_append.mp hlrdNd
  obtain ⟨hlhsNd, hrhsNd, _⟩ := List.nodup_append.mp hlrNd
  have hld : (lhs ++ difference).Nodup := List.nodup_append.mpr
    ⟨hlhsNd, hdiffNd, fun a ha b hb => hlrDiff a (List.mem_append_left rhs ha) b hb⟩
  have hrd : (rhs ++ difference).Nodup := List.nodup_append.mpr
    ⟨hrhsNd, hdiffNd, fun a ha b hb => hlrDiff a (List.mem_append_right lhs ha) b hb⟩
  have hdh : (difference ++ history).Nodup := List.nodup_append.mpr
    ⟨hdiffNd, hhistNd, fun a ha b hb => hlrdHist a
      (List.mem_append_right (lhs ++ rhs) ha) b hb⟩
  rw [equalCompute, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨copyReg_wellFormed lhs difference hld,
    copyReg_wellFormed rhs difference hrd⟩,
    zeroCompute_wellFormed difference history hdh⟩

/-- The forward equality history produces the comparison bit at its first history wire. -/
theorem equalCompute_head_correct (lhs rhs : List Wire) (d : Wire)
    (ds : List Wire) (h : Wire) (hs : List Wire) (st : BasisState)
    (hrlen : rhs.length = lhs.length)
    (hdlen : (d :: ds).length = lhs.length)
    (hhlen : (h :: hs).length = (d :: ds).length)
    (hnd : (equalComputeWires lhs rhs (d :: ds) (h :: hs)).Nodup)
    (hclean : Clean ((d :: ds) ++ (h :: hs)) st) :
    Classical.run (equalCompute lhs rhs (d :: ds) (h :: hs)) st h =
      decide (regValue lhs st = regValue rhs st) := by
  obtain ⟨hlrdNd, hhistNd, hlrdHist⟩ := List.nodup_append.mp hnd
  obtain ⟨_, hdiffNd, _⟩ := List.nodup_append.mp hlrdNd
  have hdh : ((d :: ds) ++ (h :: hs)).Nodup := List.nodup_append.mpr
    ⟨hdiffNd, hhistNd, fun a ha b hb => hlrdHist a
      (List.mem_append_right (lhs ++ rhs) ha) b hb⟩
  have hdiffClean : Clean (d :: ds) st := fun w hw =>
    hclean w (List.mem_append.mpr (Or.inl hw))
  let st₁ := Classical.run (copyReg lhs (d :: ds)) st
  let st₂ := Classical.run (copyReg rhs (d :: ds)) st₁
  have hxor := xorCopies_zero_iff lhs rhs (d :: ds) st hrlen hdlen hlrdNd hdiffClean
  have hxor' : regValue (d :: ds) st₂ = 0 ↔
      regValue lhs st = regValue rhs st := by
    simpa [st₁, st₂] using hxor
  have hhistoryCleanSt₂ : Clean (h :: hs) st₂ := by
    intro w hw
    have hwDiff : w ∉ d :: ds := by
      intro hd
      exact hlrdHist w (List.mem_append_right (lhs ++ rhs) hd) w hw rfl
    change Classical.run (copyReg rhs (d :: ds)) st₁ w = false
    rw [copyReg_other w rhs (d :: ds) st₁ hwDiff]
    change Classical.run (copyReg lhs (d :: ds)) st w = false
    rw [copyReg_other w lhs (d :: ds) st hwDiff]
    exact hclean w (List.mem_append.mpr (Or.inr hw))
  have htail : hs.length = ds.length := by simpa using hhlen
  have hzero := zeroCompute_head_correct d ds h hs st₂ htail hdh hhistoryCleanSt₂
  have hzero' :
      Classical.run (zeroCompute (d :: ds) (h :: hs)) st₂ h =
        decide (regValue (d :: ds) st₂ = 0) := hzero.2
  rw [equalCompute, Classical.run_append, Classical.run_append]
  change Classical.run (zeroCompute (d :: ds) (h :: hs)) st₂ h = _
  rw [hzero']
  exact decide_eq_decide.mpr hxor'

/-- Complete syntactic support of a clean equality flag. -/
def equalFlagWires (lhs rhs : List Wire) (flag : Wire)
    (difference history : List Wire) : List Wire :=
  ((lhs ++ rhs) ++ difference) ++ flag :: history

/-- Clean equality flag: compute XOR and zero history, copy the predicate, then uncompute. -/
def equalFlag (lhs rhs : List Wire) (flag : Wire) : List Wire → List Wire → Circuit
  | [], _ => [Gate.X flag]
  | d :: ds, h :: hs =>
      let compute := equalCompute lhs rhs (d :: ds) (h :: hs)
      compute ++ [Gate.CX h flag] ++ compute.reverse
  | _, _ => []

@[simp]
theorem equalFlag_HPFree (lhs rhs : List Wire) (flag : Wire)
    (difference history : List Wire) :
    Classical.HPFree (equalFlag lhs rhs flag difference history) := by
  cases difference with
  | nil => simp [equalFlag]
  | cons d ds =>
      cases history with
      | nil => simp [equalFlag]
      | cons h hs =>
          rw [equalFlag, Classical.hpFree_append, Classical.hpFree_append]
          exact ⟨⟨equalCompute_HPFree _ _ _ _, by simp⟩,
            hpFree_reverse (equalCompute_HPFree _ _ _ _)⟩

/-- Exact T-count of the clean equality flag; both CNOT-copy passes are Clifford-only. -/
theorem equalFlag_tCount (lhs rhs : List Wire) (flag : Wire)
    (difference history : List Wire) (hlen : history.length = difference.length) :
    tCount (equalFlag lhs rhs flag difference history) =
      14 * (difference.length - 1) := by
  cases difference with
  | nil => simp [equalFlag, tCount, tCost]
  | cons d ds =>
      cases history with
      | nil => simp at hlen
      | cons h hs =>
          have htail : hs.length = ds.length := by simpa using hlen
          rw [equalFlag, tCount_append, tCount_append, tCount_reverse,
            equalCompute_tCount _ _ _ _ (by simp [htail])]
          simp [tCount, tCost]
          omega

/-- An equality flag is confined to both inputs, its flag, and its two scratch registers. -/
theorem equalFlag_usesOnly (lhs rhs : List Wire) (flag : Wire)
    (difference history : List Wire) :
    CircuitUsesOnly (equalFlagWires lhs rhs flag difference history)
      (equalFlag lhs rhs flag difference history) := by
  cases difference with
  | nil => simp [equalFlag, equalFlagWires, CircuitUsesOnly, Gate.UsesOnly]
  | cons d ds =>
      cases history with
      | nil => simp [equalFlag, CircuitUsesOnly]
      | cons h hs =>
          let compute := equalCompute lhs rhs (d :: ds) (h :: hs)
          have hcompute :
              CircuitUsesOnly (equalFlagWires lhs rhs flag (d :: ds) (h :: hs)) compute := by
            apply usesOnly_mono (equalCompute_usesOnly lhs rhs (d :: ds) (h :: hs))
            intro w hw
            rcases List.mem_append.mp hw with hw | hw
            · exact List.mem_append.mpr (Or.inl hw)
            · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem flag hw))
          rw [equalFlag]
          exact usesOnly_append (usesOnly_append hcompute (by
            simp [CircuitUsesOnly, Gate.UsesOnly, equalFlagWires]))
            (usesOnly_reverse hcompute)

theorem equalFlag_wellFormed (lhs rhs : List Wire) (flag : Wire)
    (difference history : List Wire)
    (hnd : (equalFlagWires lhs rhs flag difference history).Nodup) :
    CircuitWellFormed (equalFlag lhs rhs flag difference history) := by
  cases difference with
  | nil => simp [equalFlag, CircuitWellFormed, Gate.WellFormed]
  | cons d ds =>
      cases history with
      | nil => simp [equalFlag, CircuitWellFormed]
      | cons h hs =>
          change ((((lhs ++ rhs) ++ (d :: ds)) ++ flag :: h :: hs).Nodup) at hnd
          obtain ⟨hprefix, hrest, hcross⟩ := List.nodup_append.mp hnd
          have hhist : (h :: hs).Nodup := (List.nodup_cons.mp hrest).2
          have hactive :
              (equalComputeWires lhs rhs (d :: ds) (h :: hs)).Nodup := by
            rw [equalComputeWires]
            exact List.nodup_append.mpr ⟨hprefix, hhist, fun a ha b hb =>
              hcross a ha b (List.mem_cons_of_mem flag hb)⟩
          have hflagH : flag ≠ h := fun e => (List.nodup_cons.mp hrest).1 (e ▸ by simp)
          rw [equalFlag, circuitWellFormed_append, circuitWellFormed_append]
          exact ⟨⟨equalCompute_wellFormed _ _ _ _ hactive, by
            simpa [CircuitWellFormed, Gate.WellFormed] using hflagH.symm⟩,
            wellFormed_reverse (equalCompute_wellFormed _ _ _ _ hactive)⟩

/-- Clean equality correctness, including preservation of both inputs and all scratch cleanup. -/
theorem equalFlag_correct (lhs rhs : List Wire) (flag : Wire)
    (difference history : List Wire) (st : BasisState)
    (hrlen : rhs.length = lhs.length)
    (hdlen : difference.length = lhs.length)
    (hhlen : history.length = lhs.length)
    (hnd : (equalFlagWires lhs rhs flag difference history).Nodup)
    (hclean : Clean (flag :: difference ++ history) st) :
    let after := Classical.run (equalFlag lhs rhs flag difference history) st
    AgreesOn lhs st after ∧
      AgreesOn rhs st after ∧
      after flag = decide (regValue lhs st = regValue rhs st) ∧
      Clean (difference ++ history) after := by
  cases difference with
  | nil =>
      have hlhs : lhs = [] := List.length_eq_zero_iff.mp hdlen.symm
      subst lhs
      have hrhs : rhs = [] := List.length_eq_zero_iff.mp hrlen
      subst rhs
      have hhistory : history = [] := List.length_eq_zero_iff.mp hhlen
      subst history
      have hflag : st flag = false := hclean flag (by simp)
      simp [equalFlag, AgreesOn, Clean, Classical.run, Classical.applyGate, hflag]
  | cons d ds =>
      cases history with
      | nil => simp at hdlen hhlen; omega
      | cons h hs =>
          have hhistoryDiff : (h :: hs).length = (d :: ds).length :=
            hhlen.trans hdlen.symm
          change ((((lhs ++ rhs) ++ (d :: ds)) ++ flag :: h :: hs).Nodup) at hnd
          obtain ⟨hprefix, hrest, hcross⟩ := List.nodup_append.mp hnd
          have hhist : (h :: hs).Nodup := (List.nodup_cons.mp hrest).2
          have hactive :
              (equalComputeWires lhs rhs (d :: ds) (h :: hs)).Nodup := by
            rw [equalComputeWires]
            exact List.nodup_append.mpr ⟨hprefix, hhist, fun a ha b hb =>
              hcross a ha b (List.mem_cons_of_mem flag hb)⟩
          have hflagOutside :
              flag ∉ equalComputeWires lhs rhs (d :: ds) (h :: hs) := by
            rw [equalComputeWires]
            intro hw
            rcases List.mem_append.mp hw with hw | hw
            · exact hcross flag hw flag (by simp) rfl
            · exact (List.nodup_cons.mp hrest).1 hw
          have hactiveClean : Clean ((d :: ds) ++ (h :: hs)) st := fun w hw =>
            hclean w (List.mem_cons_of_mem flag hw)
          have hflagClean : st flag = false := hclean flag (by simp)
          let compute := equalCompute lhs rhs (d :: ds) (h :: hs)
          let active := equalComputeWires lhs rhs (d :: ds) (h :: hs)
          let after := Classical.run (equalFlag lhs rhs flag (d :: ds) (h :: hs)) st
          have hhead := equalCompute_head_correct lhs rhs d ds h hs st hrlen hdlen
            hhistoryDiff hactive hactiveClean
          have hcleanup : AgreesOn active st after ∧
              after flag = Classical.run compute st h := by
            simpa [active, after, compute, equalFlag] using
              (bennett_cleanup_copyBit compute active h flag st
                (by simpa [compute, active] using
                  equalCompute_usesOnly lhs rhs (d :: ds) (h :: hs))
                (by simp [compute])
                (by simpa [compute] using
                  equalCompute_wellFormed lhs rhs (d :: ds) (h :: hs) hactive)
                (by simpa [active] using hflagOutside) hflagClean)
          dsimp only
          change AgreesOn lhs st after ∧
            AgreesOn rhs st after ∧
            after flag = decide (regValue lhs st = regValue rhs st) ∧
            Clean ((d :: ds) ++ (h :: hs)) after
          refine ⟨?_, ?_, hcleanup.2.trans hhead, ?_⟩
          · intro w hw
            apply hcleanup.1 w
            change w ∈ equalComputeWires lhs rhs (d :: ds) (h :: hs)
            rw [equalComputeWires]
            exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inl hw)))))
          · intro w hw
            apply hcleanup.1 w
            change w ∈ equalComputeWires lhs rhs (d :: ds) (h :: hs)
            rw [equalComputeWires]
            exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inr hw)))))
          · intro w hw
            have hwActive : w ∈ active := by
              change w ∈ equalComputeWires lhs rhs (d :: ds) (h :: hs)
              rw [equalComputeWires]
              rcases List.mem_append.mp hw with hw | hw
              · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hw)))
              · exact List.mem_append.mpr (Or.inr hw)
            rw [hcleanup.1 w hwActive]
            exact hactiveClean w hw

end Arithmetic
end ShorECDLP
