import ShorECDLP.Submission.Arithmetic.InPlaceAdder
import ShorECDLP.Submission.Arithmetic.ModSub
import ShorECDLP.Submission.Arithmetic.ModMul
import Lean.Elab.Tactic.Omega

/-!
# Low-space in-place modular arithmetic

This module builds the reversible modular operations used by the low-space multiplier.  Its
only width-sized scratch registers are a reusable masked addend and a reusable modulus
register.  The underlying addition and subtraction both use the one-ancilla Cuccaro circuit
from `InPlaceAdder`.
-/

namespace ShorECDLP

open Classical
open Arithmetic
open scoped ArithmeticNotation

/-! ## In-place two's-complement subtraction -/

/-- Subtract `source` from `target` in place.  `carryOut` is XORed with the no-borrow bit;
`source` and the incoming `carry` wire are restored. -/
def inPlaceSubCarry (source target : List Wire) (carry carryOut : Wire) : Circuit :=
  let prepare := subPrepare source carry
  circuit! {
    prepare;
    inPlaceAddCarry source target carry carryOut;
    prepare.reverse
  }

/-- Exact arithmetic and whole-state action of in-place subtraction. -/
theorem inPlaceSubCarry_correct
    (source target : List Wire) (carry carryOut : Wire) (st : BasisState)
    (hlen : target.length = source.length)
    (hnd : (source ++ (target ++ [carry, carryOut])).Nodup)
    (hcarry : st carry = false) (hcarryOut : st carryOut = false) :
    let after := run (inPlaceSubCarry source target carry carryOut) st
    AgreesOn source st after ∧
      after carry = st carry ∧
      after⟦ᵣtarget⟧ + 2 ^ source.length * bit after carryOut =
        st⟦ᵣtarget⟧ + 2 ^ source.length - st⟦ᵣsource⟧ ∧
      ∀ w, w ∉ target → w ≠ carryOut → after w = st w := by
  let prepare := subPrepare source carry
  let prepared := run prepare st
  let added := run (inPlaceAddCarry source target carry carryOut) prepared
  let after := run prepare.reverse added
  have hparts := inPlaceAddCarry_nodup_parts source target carry carryOut hnd
  have hsourceNd : source.Nodup := hparts.1
  have hcarryNeOut : carry ≠ carryOut := hparts.2.2.1
  have hsourceParts := hparts.2.2.2.1
  have htargetParts := hparts.2.2.2.2
  have hprepUses : CircuitUsesOnly (source ++ [carry]) prepare := by
    simpa [prepare] using subPrepare_usesOnly source carry
  have hreverseUses : CircuitUsesOnly (source ++ [carry]) prepare.reverse :=
    usesOnly_reverse hprepUses
  have hcancel : run prepare.reverse prepared = st := by
    simpa [prepared] using run_reverse_cancel prepare st
      (by simpa [prepare] using subPrepare_HPFree source carry)
      (by simpa [prepare] using subPrepare_wellFormed source carry)
  have htargetOutside (w : Wire) (hw : w ∈ target) : w ∉ source ++ [carry] := by
    intro hmem
    rcases List.mem_append.mp hmem with hsource | hflag
    · exact (hsourceParts w hsource).1 hw
    · simp only [List.mem_singleton] at hflag
      exact (htargetParts w hw).1 hflag
  have hcarryOutOutside : carryOut ∉ source ++ [carry] := by
    intro hmem
    rcases List.mem_append.mp hmem with hsource | hflag
    · exact (hsourceParts carryOut hsource).2.2 rfl
    · simp only [List.mem_singleton] at hflag
      exact hcarryNeOut hflag.symm
  have hpreparedSource :
      prepared⟦ᵣsource⟧ = 2 ^ source.length - 1 - st⟦ᵣsource⟧ := by
    change regValue source (run (subPrepare source carry) st) = _
    rw [subPrepare, run_append]
    calc
      regValue source (run [Gate.X carry] (run (complementReg source) st)) =
          regValue source (run (complementReg source) st) := by
        apply regValue_congr
        intro w hw
        have hwcarry : w ≠ carry := (hsourceParts w hw).2.1
        simp [run_cons, run_nil, applyGate, upd, hwcarry]
      _ = _ := regValue_complementReg source st hsourceNd
  have hpreparedTarget : prepared⟦ᵣtarget⟧ = st⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    exact hprepUses.preservesOutside st w (htargetOutside w hw)
  have hpreparedCarry : prepared carry = true := by
    change run (subPrepare source carry) st carry = true
    rw [subPrepare, run_append]
    simp only [run_cons, run_nil, applyGate, upd_same]
    rw [complementReg_other carry source st]
    · simp [hcarry]
    · intro hw
      exact (hsourceParts carry hw).2.1 rfl
  have hpreparedCarryOut : prepared carryOut = false := by
    calc
      prepared carryOut = st carryOut :=
        hprepUses.preservesOutside st carryOut hcarryOutOutside
      _ = false := hcarryOut
  have hadd := inPlaceAddCarry_correct source target carry carryOut prepared
    hlen hnd hpreparedCarryOut
  dsimp only at hadd
  obtain ⟨hsourceAdd, hcarryAdd, hsumAdd, houtsideAdd⟩ := hadd
  have hcleanupInputs : ∀ w ∈ source ++ [carry], added w = prepared w := by
    intro w hw
    rcases List.mem_append.mp hw with hsource | hflag
    · exact hsourceAdd w hsource
    · simp only [List.mem_singleton] at hflag
      subst w
      exact hcarryAdd
  have hcleanupAgree : ∀ w ∈ source ++ [carry],
      after w = run prepare.reverse prepared w := by
    intro w hw
    exact CircuitUsesOnly.run_congr hreverseUses hcleanupInputs w hw
  have hsourceFinal : AgreesOn source st after := by
    intro w hw
    calc
      after w = run prepare.reverse prepared w :=
        hcleanupAgree w (List.mem_append_left _ hw)
      _ = st w := congrFun hcancel w
  have hcarryFinal : after carry = st carry := by
    calc
      after carry = run prepare.reverse prepared carry :=
        hcleanupAgree carry (by simp)
      _ = st carry := congrFun hcancel carry
  have htargetFinal : after⟦ᵣtarget⟧ = added⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    exact hreverseUses.preservesOutside added w (htargetOutside w hw)
  have hcarryOutFinal : after carryOut = added carryOut :=
    hreverseUses.preservesOutside added carryOut hcarryOutOutside
  have hsourceBound : st⟦ᵣsource⟧ < 2 ^ source.length :=
    regValue_lt_two_pow source st
  have hnumeric :
      after⟦ᵣtarget⟧ + 2 ^ source.length * bit after carryOut =
        st⟦ᵣtarget⟧ + 2 ^ source.length - st⟦ᵣsource⟧ := by
    rw [htargetFinal, show bit after carryOut = bit added carryOut by
      simp [bit, hcarryOutFinal]]
    change added⟦ᵣtarget⟧ + 2 ^ source.length * bit added carryOut = _ at hsumAdd
    rw [hpreparedSource, hpreparedTarget] at hsumAdd
    have hcarryBit : bit prepared carry = 1 := by simp [bit, hpreparedCarry]
    rw [hcarryBit] at hsumAdd
    omega
  have houtside : ∀ w, w ∉ target → w ≠ carryOut → after w = st w := by
    intro w hwTarget hwOut
    by_cases hwPrep : w ∈ source ++ [carry]
    · calc
        after w = run prepare.reverse prepared w := hcleanupAgree w hwPrep
        _ = st w := congrFun hcancel w
    · calc
        after w = added w := hreverseUses.preservesOutside added w hwPrep
        _ = prepared w := houtsideAdd w hwTarget hwOut
        _ = st w := hprepUses.preservesOutside st w hwPrep
  change let result := run (inPlaceSubCarry source target carry carryOut) st
    AgreesOn source st result ∧ result carry = st carry ∧
      result⟦ᵣtarget⟧ + 2 ^ source.length * bit result carryOut =
        st⟦ᵣtarget⟧ + 2 ^ source.length - st⟦ᵣsource⟧ ∧
      ∀ w, w ∉ target → w ≠ carryOut → result w = st w
  simp only [inPlaceSubCarry, run_append]
  exact ⟨hsourceFinal, hcarryFinal, hnumeric, houtside⟩

/-- The subtraction carry is exactly the no-borrow predicate. -/
theorem inPlaceSubCarry_noBorrow
    (source target : List Wire) (carry carryOut : Wire) (st : BasisState)
    (hlen : target.length = source.length)
    (hnd : (source ++ (target ++ [carry, carryOut])).Nodup)
    (hcarry : st carry = false) (hcarryOut : st carryOut = false) :
    let after := run (inPlaceSubCarry source target carry carryOut) st
    (after carryOut = true ↔ st⟦ᵣsource⟧ ≤ st⟦ᵣtarget⟧) := by
  let after := run (inPlaceSubCarry source target carry carryOut) st
  have hcorrect := inPlaceSubCarry_correct source target carry carryOut st
    hlen hnd hcarry hcarryOut
  dsimp only at hcorrect
  have hnumeric := hcorrect.2.2.1
  change after⟦ᵣtarget⟧ + 2 ^ source.length * bit after carryOut =
    st⟦ᵣtarget⟧ + 2 ^ source.length - st⟦ᵣsource⟧ at hnumeric
  change after carryOut = true ↔ st⟦ᵣsource⟧ ≤ st⟦ᵣtarget⟧
  have htargetBound : after⟦ᵣtarget⟧ < 2 ^ source.length := by
    rw [← hlen]
    exact regValue_lt_two_pow target after
  constructor
  · intro hbit
    simp [bit, hbit] at hnumeric
    omega
  · intro hle
    cases hout : after carryOut with
    | false =>
        simp [bit, hout] at hnumeric
        omega
    | true => rfl

/-- In-place subtraction has the same `14 * width` T-count as its adder core. -/
theorem inPlaceSubCarry_tCount
    (source target : List Wire) (carry carryOut : Wire)
    (hlen : target.length = source.length) :
    tCount (inPlaceSubCarry source target carry carryOut) = 14 * source.length := by
  rw [inPlaceSubCarry, tCount_append, tCount_append, Arithmetic.tCount_reverse,
    inPlaceAddCarry_tCount source target carry carryOut hlen]
  simp [subPrepare, tCount_append, tCost]

/-- In-place subtraction contains no Hadamard or phase gates. -/
theorem inPlaceSubCarry_HPFree
    (source target : List Wire) (carry carryOut : Wire) :
    HPFree (inPlaceSubCarry source target carry carryOut) := by
  rw [inPlaceSubCarry, hpFree_append, hpFree_append]
  exact ⟨⟨subPrepare_HPFree source carry,
    inPlaceAddCarry_HPFree source target carry carryOut⟩,
    Arithmetic.hpFree_reverse (subPrepare_HPFree source carry)⟩

/-- In-place subtraction is physically well-formed on a duplicate-free layout. -/
theorem inPlaceSubCarry_wellFormed
    (source target : List Wire) (carry carryOut : Wire)
    (hlen : target.length = source.length)
    (hnd : (source ++ (target ++ [carry, carryOut])).Nodup) :
    CircuitWellFormed (inPlaceSubCarry source target carry carryOut) := by
  rw [inPlaceSubCarry, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨subPrepare_wellFormed source carry,
    inPlaceAddCarry_wellFormed source target carry carryOut hlen hnd⟩,
    Arithmetic.wellFormed_reverse (subPrepare_wellFormed source carry)⟩

/-- In-place subtraction stays inside the adder's named footprint. -/
theorem inPlaceSubCarry_usesOnly
    (source target : List Wire) (carry carryOut : Wire) :
    CircuitUsesOnly (inPlaceAddCarryFootprint source target carry carryOut)
      (inPlaceSubCarry source target carry carryOut) := by
  have hprep : CircuitUsesOnly (inPlaceAddCarryFootprint source target carry carryOut)
      (subPrepare source carry) := by
    apply usesOnly_mono (subPrepare_usesOnly source carry)
    intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · simp [inPlaceAddCarryFootprint, hw]
    · simp [inPlaceAddCarryFootprint]
  rw [inPlaceSubCarry]
  exact usesOnly_append
    (usesOnly_append hprep (inPlaceAddCarry_usesOnly source target carry carryOut))
    (usesOnly_reverse hprep)

/-! ## Reversible less-than flag -/

/-- XOR `flag` with `target < source`, using `workCarry` only during a subtract/unsubtract
computation.  Every wire except `flag` is restored. -/
def lessThanXor (source target : List Wire) (carry workCarry flag : Wire) : Circuit :=
  let compute := inPlaceSubCarry source target carry workCarry
  circuit! {
    compute;
    gate! Gate.X flag;
    gate! Gate.CX workCarry flag;
    compute.reverse
  }

/-- Exact whole-state action of the reversible comparator. -/
theorem lessThanXor_correct
    (source target : List Wire) (carry workCarry flag : Wire) (st : BasisState)
    (hlen : target.length = source.length)
    (hnd : (source ++ (target ++ [carry, workCarry])).Nodup)
    (hflagOutside : flag ∉ inPlaceAddCarryFootprint source target carry workCarry)
    (hcarry : st carry = false) (hworkCarry : st workCarry = false) :
    let after := run (lessThanXor source target carry workCarry flag) st
    after flag = Bool.xor (st flag) (decide (st⟦ᵣtarget⟧ < st⟦ᵣsource⟧)) ∧
      ∀ w, w ≠ flag → after w = st w := by
  let support := inPlaceAddCarryFootprint source target carry workCarry
  let compute := inPlaceSubCarry source target carry workCarry
  let mid := run compute st
  let toggled := run [Gate.X flag, Gate.CX workCarry flag] mid
  let after := run compute.reverse toggled
  have hcomputeUses : CircuitUsesOnly support compute := by
    simpa [support, compute] using
      inPlaceSubCarry_usesOnly source target carry workCarry
  have hreverseUses : CircuitUsesOnly support compute.reverse :=
    usesOnly_reverse hcomputeUses
  have hcomputeFree : HPFree compute := by
    simpa [compute] using inPlaceSubCarry_HPFree source target carry workCarry
  have hcomputeWf : CircuitWellFormed compute := by
    simpa [compute] using
      inPlaceSubCarry_wellFormed source target carry workCarry hlen hnd
  have hcancel : run compute.reverse mid = st := by
    simpa [mid] using run_reverse_cancel compute st hcomputeFree hcomputeWf
  have hworkMem : workCarry ∈ support := by
    simp [support, inPlaceAddCarryFootprint]
  have hworkNeFlag : workCarry ≠ flag := by
    intro e
    exact hflagOutside (e ▸ hworkMem)
  have hmidFlag : mid flag = st flag :=
    hcomputeUses.preservesOutside st flag hflagOutside
  have hnoBorrow : mid workCarry = true ↔ st⟦ᵣsource⟧ ≤ st⟦ᵣtarget⟧ := by
    simpa [mid, compute] using
      inPlaceSubCarry_noBorrow source target carry workCarry st
        hlen hnd hcarry hworkCarry
  have htoggledSupport : ∀ w ∈ support, toggled w = mid w := by
    intro w hw
    have hwNe : w ≠ flag := by
      intro e
      exact hflagOutside (e ▸ hw)
    simp [toggled, run_cons, run_nil, applyGate, upd, hwNe]
  have htoggledFlag :
      toggled flag = Bool.xor (st flag) (decide (st⟦ᵣtarget⟧ < st⟦ᵣsource⟧)) := by
    have hraw : toggled flag = Bool.xor (!mid flag) (mid workCarry) := by
      simp [toggled, run_cons, run_nil, applyGate, upd, hworkNeFlag]
    rw [hraw, hmidFlag]
    by_cases hlt : st⟦ᵣtarget⟧ < st⟦ᵣsource⟧
    · have hworkFalse : mid workCarry = false := by
        cases hw : mid workCarry with
        | false => rfl
        | true => exact False.elim ((Nat.not_le_of_gt hlt) (hnoBorrow.mp hw))
      simp [hlt, hworkFalse]
    · have hworkTrue : mid workCarry = true :=
        hnoBorrow.mpr (Nat.le_of_not_gt hlt)
      simp [hlt, hworkTrue]
  have hcleanupSupport : ∀ w ∈ support,
      after w = run compute.reverse mid w := by
    intro w hw
    exact CircuitUsesOnly.run_congr hreverseUses htoggledSupport w hw
  have hflagFinal :
      after flag = Bool.xor (st flag) (decide (st⟦ᵣtarget⟧ < st⟦ᵣsource⟧)) := by
    calc
      after flag = toggled flag :=
        hreverseUses.preservesOutside toggled flag hflagOutside
      _ = _ := htoggledFlag
  have hotherFinal : ∀ w, w ≠ flag → after w = st w := by
    intro w hwFlag
    by_cases hwSupport : w ∈ support
    · calc
        after w = run compute.reverse mid w := hcleanupSupport w hwSupport
        _ = st w := congrFun hcancel w
    · calc
        after w = toggled w := hreverseUses.preservesOutside toggled w hwSupport
        _ = mid w := by
          simp [toggled, run_cons, run_nil, applyGate, upd, hwFlag]
        _ = st w := hcomputeUses.preservesOutside st w hwSupport
  change let result := run (lessThanXor source target carry workCarry flag) st
    result flag = Bool.xor (st flag) (decide (st⟦ᵣtarget⟧ < st⟦ᵣsource⟧)) ∧
      ∀ w, w ≠ flag → result w = st w
  simp only [lessThanXor, run_append]
  exact ⟨hflagFinal, hotherFinal⟩

/-- Comparator cost: one subtract and its inverse. -/
theorem lessThanXor_tCount
    (source target : List Wire) (carry workCarry flag : Wire)
    (hlen : target.length = source.length) :
    tCount (lessThanXor source target carry workCarry flag) = 28 * source.length := by
  rw [lessThanXor, tCount_append, tCount_append,
    Arithmetic.tCount_reverse,
    inPlaceSubCarry_tCount source target carry workCarry hlen]
  simp [tCost]
  omega

/-- The comparator contains no Hadamard or phase gates. -/
theorem lessThanXor_HPFree
    (source target : List Wire) (carry workCarry flag : Wire) :
    HPFree (lessThanXor source target carry workCarry flag) := by
  simp [lessThanXor, hpFree_append,
    inPlaceSubCarry_HPFree source target carry workCarry,
    Arithmetic.hpFree_reverse]

/-- The comparator is physically well-formed when the flag is fresh. -/
theorem lessThanXor_wellFormed
    (source target : List Wire) (carry workCarry flag : Wire)
    (hlen : target.length = source.length)
    (hnd : (source ++ (target ++ [carry, workCarry])).Nodup)
    (hflagOutside : flag ∉ inPlaceAddCarryFootprint source target carry workCarry) :
    CircuitWellFormed (lessThanXor source target carry workCarry flag) := by
  have hworkMem : workCarry ∈
      inPlaceAddCarryFootprint source target carry workCarry := by
    simp [inPlaceAddCarryFootprint]
  have hworkNeFlag : workCarry ≠ flag := by
    intro e
    exact hflagOutside (e ▸ hworkMem)
  have hcompute := inPlaceSubCarry_wellFormed source target carry workCarry hlen hnd
  simp [lessThanXor, circuitWellFormed_append, Gate.WellFormed,
    hworkNeFlag, hcompute, Arithmetic.wellFormed_reverse]

/-- The comparator uses only the subtractor footprint and its output flag. -/
theorem lessThanXor_usesOnly
    (source target : List Wire) (carry workCarry flag : Wire) :
    CircuitUsesOnly
      (inPlaceAddCarryFootprint source target carry workCarry ++ [flag])
      (lessThanXor source target carry workCarry flag) := by
  let support := inPlaceAddCarryFootprint source target carry workCarry ++ [flag]
  have hcompute : CircuitUsesOnly support
      (inPlaceSubCarry source target carry workCarry) := by
    apply usesOnly_mono
      (inPlaceSubCarry_usesOnly source target carry workCarry)
    intro w hw
    exact List.mem_append_left _ hw
  have hgates : CircuitUsesOnly support
      ([Gate.X flag, Gate.CX workCarry flag] : Circuit) := by
    simp [support, CircuitUsesOnly, Gate.UsesOnly, inPlaceAddCarryFootprint]
  change CircuitUsesOnly support _
  rw [lessThanXor]
  exact usesOnly_append (usesOnly_append hcompute hgates) (usesOnly_reverse hcompute)

/-! ## Reversible left shift through one carry wire -/

/-- Swap two classical wires with three CNOTs. -/
def swapWire (a b : Wire) : Circuit :=
  circuit! {
    gate! Gate.CX a b;
    gate! Gate.CX b a;
    gate! Gate.CX a b
  }

/-- Exact classical action of the three-CNOT swap. -/
theorem swapWire_correct (a b : Wire) (st : BasisState) (hab : a ≠ b) :
    let after := run (swapWire a b) st
    after a = st b ∧ after b = st a ∧
      ∀ w, w ≠ a → w ≠ b → after w = st w := by
  dsimp only
  constructor
  · simp only [swapWire, run_cons, run_nil, applyGate, upd_same]
    simp [upd, hab]
    cases st a <;> cases st b <;> decide
  constructor
  · simp only [swapWire, run_cons, run_nil, applyGate, upd_same]
    simp [upd, hab, hab.symm]
  · intro w hwa hwb
    simp [swapWire, run_cons, run_nil, applyGate, upd, hwa, hwb]

/-- Move a clean low carry through an LSB-first register.  Each swap writes the old carry
into the current bit and retains the displaced bit as the next carry. -/
def shiftLeftCarry : List Wire → Wire → Circuit
  | [], _ => circuit! {}
  | w :: ws, carry => circuit! {
      swapWire carry w;
      shiftLeftCarry ws carry
    }

/-- The shift circuit implements the exact identity
`newTarget + 2^n * finalCarry = 2 * oldTarget + initialCarry`. -/
theorem shiftLeftCarry_correct :
    ∀ (target : List Wire) (carry : Wire) (st : BasisState),
      target.Nodup → carry ∉ target →
      let after := run (shiftLeftCarry target carry) st
      after⟦ᵣtarget⟧ + 2 ^ target.length * bit after carry =
          2 * st⟦ᵣtarget⟧ + bit st carry ∧
        ∀ w, w ∉ target → w ≠ carry → after w = st w := by
  intro target
  induction target with
  | nil =>
      intro carry st _ _
      simp [shiftLeftCarry, bit]
  | cons w ws ih =>
      intro carry st hnd hcarry
      obtain ⟨hwTail, htailNd⟩ := List.nodup_cons.mp hnd
      have hcarryW : carry ≠ w := by
        intro e
        exact hcarry (e ▸ List.mem_cons_self)
      have hcarryTail : carry ∉ ws := by
        intro hw
        exact hcarry (List.mem_cons_of_mem w hw)
      let mid := run (swapWire carry w) st
      let after := run (shiftLeftCarry ws carry) mid
      have hswap := swapWire_correct carry w st hcarryW
      dsimp only at hswap
      change mid carry = st w ∧ mid w = st carry ∧
        ∀ x, x ≠ carry → x ≠ w → mid x = st x at hswap
      have hih := ih carry mid htailNd hcarryTail
      dsimp only at hih
      change after⟦ᵣws⟧ + 2 ^ ws.length * bit after carry =
          2 * mid⟦ᵣws⟧ + bit mid carry ∧
        ∀ x, x ∉ ws → x ≠ carry → after x = mid x at hih
      have htailMid : mid⟦ᵣws⟧ = st⟦ᵣws⟧ := by
        apply regValue_congr
        intro x hx
        exact hswap.2.2 x
          (fun e => hcarryTail (e ▸ hx))
          (fun e => hwTail (e ▸ hx))
      have hwAfter : after w = mid w := by
        exact hih.2 w hwTail hcarryW.symm
      rw [htailMid] at hih
      simp only [bit, hswap.1] at hih
      have hnumeric :
          after⟦ᵣw :: ws⟧ + 2 ^ (w :: ws).length * bit after carry =
            2 * st⟦ᵣw :: ws⟧ + bit st carry := by
        rw [regValue_cons, regValue_cons, hwAfter, hswap.2.1, List.length_cons,
          Nat.pow_succ]
        have hmul :
            (2 ^ ws.length * 2) * bit after carry =
              2 * (2 ^ ws.length * bit after carry) := by
          simp [Nat.mul_assoc, Nat.mul_comm]
        rw [hmul]
        have htail := hih.1
        simp only [bit] at htail ⊢
        omega
      have houtside : ∀ x, x ∉ w :: ws → x ≠ carry → after x = st x := by
        intro x hxTarget hxCarry
        simp only [List.mem_cons, not_or] at hxTarget
        calc
          after x = mid x := hih.2 x hxTarget.2 hxCarry
          _ = st x := hswap.2.2 x hxCarry hxTarget.1
      change let result := run (shiftLeftCarry (w :: ws) carry) st
        result⟦ᵣw :: ws⟧ + 2 ^ (w :: ws).length * bit result carry =
            2 * st⟦ᵣw :: ws⟧ + bit st carry ∧
          ∀ x, x ∉ w :: ws → x ≠ carry → result x = st x
      simp only [shiftLeftCarry, run_append]
      exact ⟨hnumeric, houtside⟩

/-- With a clean carry and no overflow, the shift exactly doubles the target and restores
the carry to zero. -/
theorem shiftLeftCarry_noOverflow
    (target : List Wire) (carry : Wire) (st : BasisState)
    (hnd : target.Nodup) (hcarryOutside : carry ∉ target)
    (hcarry : st carry = false)
    (hfit : 2 * st⟦ᵣtarget⟧ < 2 ^ target.length) :
    let after := run (shiftLeftCarry target carry) st
    after⟦ᵣtarget⟧ = 2 * st⟦ᵣtarget⟧ ∧ after carry = false ∧
      ∀ w, w ∉ target → w ≠ carry → after w = st w := by
  let after := run (shiftLeftCarry target carry) st
  have hcorrect := shiftLeftCarry_correct target carry st hnd hcarryOutside
  dsimp only at hcorrect
  have hnumeric := hcorrect.1
  change after⟦ᵣtarget⟧ + 2 ^ target.length * bit after carry =
    2 * st⟦ᵣtarget⟧ + bit st carry at hnumeric
  have htargetBound : after⟦ᵣtarget⟧ < 2 ^ target.length :=
    regValue_lt_two_pow target after
  have hcarryBit : bit st carry = 0 := by simp [bit, hcarry]
  rw [hcarryBit] at hnumeric
  have hfinalCarry : after carry = false := by
    cases hc : after carry with
    | false => rfl
    | true =>
        simp [bit, hc] at hnumeric
        omega
  have hvalue : after⟦ᵣtarget⟧ = 2 * st⟦ᵣtarget⟧ := by
    simp [bit, hfinalCarry] at hnumeric
    exact hnumeric
  exact ⟨hvalue, hfinalCarry, hcorrect.2⟩

@[simp] theorem swapWire_tCount (a b : Wire) : tCount (swapWire a b) = 0 := rfl

@[simp] theorem shiftLeftCarry_tCount (target : List Wire) (carry : Wire) :
    tCount (shiftLeftCarry target carry) = 0 := by
  induction target with
  | nil => rfl
  | cons w ws ih => simp [shiftLeftCarry, tCount_append, ih]

theorem shiftLeftCarry_HPFree (target : List Wire) (carry : Wire) :
    HPFree (shiftLeftCarry target carry) := by
  induction target with
  | nil => simp [shiftLeftCarry]
  | cons w ws ih => simp [shiftLeftCarry, swapWire, ih]

theorem shiftLeftCarry_wellFormed (target : List Wire) (carry : Wire)
    (hnd : target.Nodup) (hcarryOutside : carry ∉ target) :
    CircuitWellFormed (shiftLeftCarry target carry) := by
  induction target with
  | nil => simp [shiftLeftCarry]
  | cons w ws ih =>
      obtain ⟨_, htailNd⟩ := List.nodup_cons.mp hnd
      have hne : carry ≠ w := by
        intro e
        exact hcarryOutside (e ▸ List.mem_cons_self)
      have htail : carry ∉ ws := by
        intro hw
        exact hcarryOutside (List.mem_cons_of_mem w hw)
      rw [shiftLeftCarry, circuitWellFormed_append]
      constructor
      · simp [swapWire, Gate.WellFormed, hne, hne.symm]
      · exact ih htailNd htail

theorem shiftLeftCarry_usesOnly (target : List Wire) (carry : Wire) :
    CircuitUsesOnly (target ++ [carry]) (shiftLeftCarry target carry) := by
  induction target with
  | nil => simp [shiftLeftCarry, CircuitUsesOnly]
  | cons w ws ih =>
      rw [shiftLeftCarry]
      apply usesOnly_append
      · simp [CircuitUsesOnly, swapWire, Gate.UsesOnly]
      · apply usesOnly_mono ih
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with hx | rfl
        · exact Or.inl (List.mem_cons_of_mem w hx)
        · simp

/-! ## Negative-controlled reusable mask -/

/-- XOR `source` into `mask` exactly when `control` is false. -/
def negativeMask (control : Wire) (source mask : List Wire) : Circuit :=
  circuit! {
    gate! Gate.X control;
    ModMul.maskReg control source mask;
    gate! Gate.X control
  }

/-- A negative-controlled mask writes the selected value into a clean mask and has no net
effect outside the mask register. -/
theorem negativeMask_correct
    (control : Wire) (source mask : List Wire) (st : BasisState)
    (hlen : mask.length = source.length)
    (hnd : (control :: source ++ mask).Nodup)
    (hclean : Clean mask st) :
    let after := run (negativeMask control source mask) st
    after⟦ᵣmask⟧ = (if st control then 0 else st⟦ᵣsource⟧) ∧
      ∀ w, w ∉ mask → after w = st w := by
  let flipped := applyGate (Gate.X control) st
  let masked := run (ModMul.maskReg control source mask) flipped
  let after := applyGate (Gate.X control) masked
  obtain ⟨hcontrolOutside, hrestNd⟩ := List.nodup_cons.mp hnd
  obtain ⟨hsourceNd, hmaskNd, hcross⟩ := List.nodup_append.mp hrestNd
  have hcontrolMask : control ∉ mask := by
    intro hw
    exact hcontrolOutside (List.mem_append.mpr (Or.inr hw))
  have hcontrolSource : control ∉ source := by
    intro hw
    exact hcontrolOutside (List.mem_append.mpr (Or.inl hw))
  have hflippedControl : flipped control = !st control := by
    simp [flipped, applyGate]
  have hflippedSource : flipped⟦ᵣsource⟧ = st⟦ᵣsource⟧ := by
    apply regValue_congr
    intro w hw
    have hwNe : w ≠ control := by
      intro e
      exact hcontrolSource (e ▸ hw)
    simp [flipped, applyGate, upd, hwNe]
  have hflippedClean : Clean mask flipped := by
    intro w hw
    have hwNe : w ≠ control := by
      intro e
      exact hcontrolMask (e ▸ hw)
    simpa [flipped, applyGate, upd, hwNe] using hclean w hw
  have hmaskValue := ModMul.maskReg_correct control source mask flipped
    hlen hnd hflippedClean
  change masked⟦ᵣmask⟧ = if flipped control then flipped⟦ᵣsource⟧ else 0 at hmaskValue
  have hafterMask : after⟦ᵣmask⟧ = masked⟦ᵣmask⟧ := by
    apply regValue_congr
    intro w hw
    have hwNe : w ≠ control := by
      intro e
      exact hcontrolMask (e ▸ hw)
    simp [after, applyGate, upd, hwNe]
  have hvalue : after⟦ᵣmask⟧ = if st control then 0 else st⟦ᵣsource⟧ := by
    rw [hafterMask, hmaskValue, hflippedControl, hflippedSource]
    cases st control <;> rfl
  have houtside : ∀ w, w ∉ mask → after w = st w := by
    intro w hwMask
    by_cases hwControl : w = control
    · subst w
      have hmaskedControl : masked control = flipped control := by
        exact ModMul.maskReg_other control control source mask flipped hcontrolMask
      simp [after, applyGate, hmaskedControl, hflippedControl]
    · have hmaskedW : masked w = flipped w :=
        ModMul.maskReg_other control w source mask flipped hwMask
      simp [after, applyGate, upd, hwControl, hmaskedW, flipped]
  have hrun : run (negativeMask control source mask) st = after := by
    simp [negativeMask, after, masked, flipped, run_append]
  dsimp only
  rw [hrun]
  exact ⟨hvalue, houtside⟩

theorem negativeMask_tCount
    (control : Wire) (source mask : List Wire)
    (hlen : mask.length = source.length) :
    tCount (negativeMask control source mask) = 7 * source.length := by
  rw [negativeMask, tCount_append, tCount_cons,
    ModMul.maskReg_tCount control source mask hlen]
  simp [tCost]

theorem negativeMask_HPFree (control : Wire) (source mask : List Wire) :
    HPFree (negativeMask control source mask) := by
  simp [negativeMask, ModMul.maskReg_HPFree]

theorem negativeMask_wellFormed
    (control : Wire) (source mask : List Wire)
    (hnd : (control :: source ++ mask).Nodup) :
    CircuitWellFormed (negativeMask control source mask) := by
  have hmask := ModMul.maskReg_wellFormed control source mask hnd
  simp [negativeMask, circuitWellFormed_append, Gate.WellFormed, hmask]

theorem negativeMask_usesOnly (control : Wire) (source mask : List Wire) :
    CircuitUsesOnly (control :: source ++ mask) (negativeMask control source mask) := by
  have hmask := ModMul.maskReg_usesOnly control source mask
    (control :: source ++ mask) (by simp)
    (by intro w hw; simp [hw]) (by intro w hw; simp [hw])
  have hx : CircuitUsesOnly (control :: source ++ mask) ([Gate.X control] : Circuit) := by
    simp [CircuitUsesOnly, Gate.UsesOnly]
  simpa [negativeMask, List.append_assoc] using
    usesOnly_append (usesOnly_append hx hmask) hx

/-! ## One-subtraction modular reduction -/

/-- Arithmetic behind subtract-and-conditionally-add-back reduction. -/
private theorem reduce_addback_arithmetic
    (modulus M x raw addend result : Nat) (reduced overflow : Bool)
    (hmod : 0 < modulus) (hfit : 2 * modulus ≤ M) (hx : x < 2 * modulus)
    (hrawBound : raw < M) (hresultBound : result < M)
    (hsub : raw + M * (if reduced then 1 else 0) = x + M - modulus)
    (haddend : addend = if reduced then 0 else modulus)
    (hadd : result + M * (if overflow then 1 else 0) = raw + addend) :
    result = x % modulus ∧ overflow = !reduced := by
  have hmodM : modulus ≤ M := by omega
  have hsub' : raw + M * (if reduced then 1 else 0) = x + (M - modulus) := by
    omega
  have hselect := reduceOnce_select_eq_mod modulus M x raw reduced
    hmod hfit hx hrawBound hsub'
  cases reduced with
  | false =>
      simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at hsub haddend hselect
      rw [haddend] at hadd
      have hxMod : x % modulus = x := hselect.symm
      cases overflow with
      | false => simp at hadd; omega
      | true =>
          simp only [if_true, Nat.mul_one] at hadd
          constructor
          · rw [hxMod]
            omega
          · rfl
  | true =>
      simp only [if_true, Nat.mul_one] at hsub haddend hselect
      rw [haddend] at hadd
      cases overflow with
      | false =>
          simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at hadd
          constructor
          · omega
          · rfl
      | true => simp at hadd; omega

/-- Complete live footprint for a reduction call, ordered to make the two masks and the
in-place add a contiguous duplicate-free suffix. -/
def reductionWires (modulusReg target mask : List Wire)
    (carry branch overflow : Wire) : List Wire :=
  branch :: modulusReg ++ mask ++ target ++ [carry, overflow]

private theorem reduction_nodup_components
    (modulusReg target mask : List Wire) (carry branch overflow : Wire)
    (hnd : (reductionWires modulusReg target mask carry branch overflow).Nodup) :
    (modulusReg ++ (target ++ [carry, branch])).Nodup ∧
      (branch :: modulusReg ++ mask).Nodup ∧
      (mask ++ (target ++ [carry, overflow])).Nodup ∧
      branch ≠ overflow ∧ target.Nodup ∧ overflow ∉ target := by
  have hmaster :
      (branch :: (modulusReg ++ (mask ++ (target ++ [carry, overflow])))).Nodup := by
    simpa [reductionWires, List.append_assoc] using hnd
  obtain ⟨hbranchRest, hrestNd⟩ := List.nodup_cons.mp hmaster
  obtain ⟨hmodNd, htail₁Nd, hmodCross⟩ := List.nodup_append.mp hrestNd
  obtain ⟨hmaskNd, htail₂Nd, hmaskCross⟩ := List.nodup_append.mp htail₁Nd
  obtain ⟨htargetNd, hflagsNd, htargetFlags⟩ := List.nodup_append.mp htail₂Nd
  have hbranchNotMod : branch ∉ modulusReg := by
    intro hw; exact hbranchRest (by simp [hw])
  have hbranchNotMask : branch ∉ mask := by
    intro hw; exact hbranchRest (by simp [hw])
  have hbranchNotTarget : branch ∉ target := by
    intro hw; exact hbranchRest (by simp [hw])
  have hbranchNeCarry : branch ≠ carry := by
    intro e; exact hbranchRest (by simp [e])
  have hbranchNeOverflow : branch ≠ overflow := by
    intro e; exact hbranchRest (by simp [e])
  have hmodMask : (modulusReg ++ mask).Nodup :=
    List.nodup_append.mpr ⟨hmodNd, hmaskNd, by
      intro x hx y hy
      exact hmodCross x hx y (by simp [hy])⟩
  have hselectNd : (branch :: modulusReg ++ mask).Nodup :=
    List.nodup_cons.mpr ⟨by
      intro hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hbranchNotMod hw
      · exact hbranchNotMask hw, hmodMask⟩
  have htargetBranchFlags : (target ++ [carry, branch]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨htargetNd, by simp [hbranchNeCarry.symm], ?_⟩
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact htargetFlags x hx carry (by simp)
    · rw [hy]
      intro e; exact hbranchNotTarget (e ▸ hx)
  have hsubNd : (modulusReg ++ (target ++ [carry, branch])).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hmodNd, htargetBranchFlags, ?_⟩
    intro x hx y hy
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy | hy
    · exact hmodCross x hx y (by simp [hy])
    · rw [hy]
      exact hmodCross x hx carry (by simp)
    · rw [hy]
      intro e; exact hbranchNotMod (e ▸ hx)
  have hoverflowOutside : overflow ∉ target := by
    intro hw
    exact htargetFlags overflow hw overflow (by simp) rfl
  exact ⟨hsubNd, hselectNd, htail₁Nd, hbranchNeOverflow,
    htargetNd, hoverflowOutside⟩

/-- Reduce a value below `2 * modulus` in place.  `branch` is left holding whether the
subtraction occurred; every other work wire is restored. -/
def reduceWithFlag (modulusReg target mask : List Wire)
    (carry branch overflow : Wire) : Circuit :=
  let select := negativeMask branch modulusReg mask
  circuit! {
    inPlaceSubCarry modulusReg target carry branch;
    select;
    inPlaceAddCarry mask target carry overflow;
    select.reverse;
    gate! Gate.X overflow;
    gate! Gate.CX branch overflow
  }

/-- Exact semantic contract for one-subtraction modular reduction. -/
theorem reduceWithFlag_correct
    (modulusReg target mask : List Wire) (carry branch overflow : Wire)
    (st : BasisState)
    (hmodLen : modulusReg.length = target.length)
    (hmaskLen : mask.length = target.length)
    (hnd : (reductionWires modulusReg target mask carry branch overflow).Nodup)
    (hmod : 0 < st⟦ᵣmodulusReg⟧)
    (hfit : 2 * st⟦ᵣmodulusReg⟧ ≤ 2 ^ target.length)
    (htarget : st⟦ᵣtarget⟧ < 2 * st⟦ᵣmodulusReg⟧)
    (hmask : Clean mask st)
    (hcarry : st carry = false) (hbranch : st branch = false)
    (hoverflow : st overflow = false) :
    let after := run (reduceWithFlag modulusReg target mask carry branch overflow) st
    after⟦ᵣtarget⟧ = st⟦ᵣtarget⟧ % st⟦ᵣmodulusReg⟧ ∧
      (after branch = true ↔ st⟦ᵣmodulusReg⟧ ≤ st⟦ᵣtarget⟧) ∧
      ∀ w, w ∉ target → w ≠ branch → after w = st w := by
  let select := negativeMask branch modulusReg mask
  let st₁ := run (inPlaceSubCarry modulusReg target carry branch) st
  let st₂ := run select st₁
  let st₃ := run (inPlaceAddCarry mask target carry overflow) st₂
  let st₄ := run select.reverse st₃
  let after := run [Gate.X overflow, Gate.CX branch overflow] st₄
  have hmaster :
      (branch :: (modulusReg ++ (mask ++ (target ++ [carry, overflow])))).Nodup := by
    simpa [reductionWires, List.append_assoc] using hnd
  obtain ⟨hbranchRest, hrestNd⟩ := List.nodup_cons.mp hmaster
  obtain ⟨hmodNd, htail₁Nd, hmodCross⟩ := List.nodup_append.mp hrestNd
  obtain ⟨hmaskNd, htail₂Nd, hmaskCross⟩ := List.nodup_append.mp htail₁Nd
  obtain ⟨htargetNd, hflagsNd, htargetFlags⟩ := List.nodup_append.mp htail₂Nd
  have hcarryNeOverflow : carry ≠ overflow := by simpa using hflagsNd
  have hbranchNotMod : branch ∉ modulusReg := by
    intro hw; exact hbranchRest (by simp [hw])
  have hbranchNotMask : branch ∉ mask := by
    intro hw; exact hbranchRest (by simp [hw])
  have hbranchNotTarget : branch ∉ target := by
    intro hw; exact hbranchRest (by simp [hw])
  have hbranchNeCarry : branch ≠ carry := by
    intro e; exact hbranchRest (by simp [e])
  have hbranchNeOverflow : branch ≠ overflow := by
    intro e; exact hbranchRest (by simp [e])
  have hmodMask : (modulusReg ++ mask).Nodup :=
    List.nodup_append.mpr ⟨hmodNd, hmaskNd, by
      intro x hx y hy
      exact hmodCross x hx y (by simp [hy])⟩
  have hselectNd : (branch :: modulusReg ++ mask).Nodup :=
    List.nodup_cons.mpr ⟨by
      intro hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hbranchNotMod hw
      · exact hbranchNotMask hw, hmodMask⟩
  have haddNd : (mask ++ (target ++ [carry, overflow])).Nodup := htail₁Nd
  have htargetBranchFlags : (target ++ [carry, branch]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨htargetNd, by simp [hbranchNeCarry.symm], ?_⟩
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact htargetFlags x hx carry (by simp)
    · rw [hy]
      intro e
      exact hbranchNotTarget (e ▸ hx)
  have hsubNd : (modulusReg ++ (target ++ [carry, branch])).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hmodNd, htargetBranchFlags, ?_⟩
    intro x hx y hy
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy | hy
    · exact hmodCross x hx y (by simp [hy])
    · rw [hy]
      exact hmodCross x hx carry (by simp)
    · rw [hy]
      intro e
      exact hbranchNotMod (e ▸ hx)
  have hmaskNotTarget (w : Wire) (hw : w ∈ mask) : w ∉ target := by
    intro ht
    exact hmaskCross w hw w (by simp [ht]) rfl
  have hmaskNeBranch (w : Wire) (hw : w ∈ mask) : w ≠ branch := by
    intro e
    exact hbranchNotMask (e ▸ hw)
  have hoverflowNotTarget : overflow ∉ target := by
    intro hw
    exact htargetFlags overflow hw overflow (by simp) rfl
  have htargetOutsideSelect (w : Wire) (hw : w ∈ target) :
      w ∉ branch :: modulusReg ++ mask := by
    simp only [List.mem_cons, List.mem_append, not_or]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro e; exact hbranchNotTarget (e ▸ hw)
    · intro hm; exact hmodCross w hm w (by simp [hw]) rfl
    · intro hm; exact hmaskCross w hm w (by simp [hw]) rfl
  have hoverflowOutsideSelect : overflow ∉ branch :: modulusReg ++ mask := by
    simp only [List.mem_cons, List.mem_append, not_or]
    refine ⟨⟨hbranchNeOverflow.symm, ?_⟩, ?_⟩
    · intro hm; exact hmodCross overflow hm overflow (by simp) rfl
    · intro hm; exact hmaskCross overflow hm overflow (by simp) rfl
  have hcarryOutsideSelect : carry ∉ branch :: modulusReg ++ mask := by
    simp only [List.mem_cons, List.mem_append, not_or]
    refine ⟨⟨hbranchNeCarry.symm, ?_⟩, ?_⟩
    · intro hm; exact hmodCross carry hm carry (by simp) rfl
    · intro hm; exact hmaskCross carry hm carry (by simp) rfl
  have hsubCorrect := inPlaceSubCarry_correct modulusReg target carry branch st
    hmodLen.symm hsubNd hcarry hbranch
  dsimp only at hsubCorrect
  change AgreesOn modulusReg st st₁ ∧ st₁ carry = st carry ∧
    st₁⟦ᵣtarget⟧ + 2 ^ modulusReg.length * bit st₁ branch =
      st⟦ᵣtarget⟧ + 2 ^ modulusReg.length - st⟦ᵣmodulusReg⟧ ∧
    ∀ w, w ∉ target → w ≠ branch → st₁ w = st w at hsubCorrect
  have hnoBorrow := inPlaceSubCarry_noBorrow modulusReg target carry branch st
    hmodLen.symm hsubNd hcarry hbranch
  dsimp only at hnoBorrow
  change st₁ branch = true ↔ st⟦ᵣmodulusReg⟧ ≤ st⟦ᵣtarget⟧ at hnoBorrow
  have hmaskClean₁ : Clean mask st₁ := by
    intro w hw
    rw [hsubCorrect.2.2.2 w (hmaskNotTarget w hw) (hmaskNeBranch w hw)]
    exact hmask w hw
  have hoverflow₁ : st₁ overflow = false := by
    rw [hsubCorrect.2.2.2 overflow hoverflowNotTarget hbranchNeOverflow.symm]
    exact hoverflow
  have hselectCorrect := negativeMask_correct branch modulusReg mask st₁
    (by omega) hselectNd hmaskClean₁
  dsimp only at hselectCorrect
  change st₂⟦ᵣmask⟧ = (if st₁ branch then 0 else st₁⟦ᵣmodulusReg⟧) ∧
    ∀ w, w ∉ mask → st₂ w = st₁ w at hselectCorrect
  have hcarry₂ : st₂ carry = false := by
    rw [hselectCorrect.2 carry]
    · rw [hsubCorrect.2.1, hcarry]
    · intro hw
      exact hmaskCross carry hw carry (by simp) rfl
  have hoverflow₂ : st₂ overflow = false := by
    rw [hselectCorrect.2 overflow]
    · exact hoverflow₁
    · intro hw
      exact hmaskCross overflow hw overflow (by simp) rfl
  have haddCorrect := inPlaceAddCarry_correct mask target carry overflow st₂
    (by omega) haddNd hoverflow₂
  dsimp only at haddCorrect
  change AgreesOn mask st₂ st₃ ∧ st₃ carry = st₂ carry ∧
    st₃⟦ᵣtarget⟧ + 2 ^ mask.length * bit st₃ overflow =
      st₂⟦ᵣmask⟧ + st₂⟦ᵣtarget⟧ + bit st₂ carry ∧
    ∀ w, w ∉ target → w ≠ overflow → st₃ w = st₂ w at haddCorrect
  have hselectUses : CircuitUsesOnly (branch :: modulusReg ++ mask) select := by
    simpa [select] using negativeMask_usesOnly branch modulusReg mask
  have hselectFree : HPFree select := by
    simpa [select] using negativeMask_HPFree branch modulusReg mask
  have hselectWf : CircuitWellFormed select := by
    simpa [select] using negativeMask_wellFormed branch modulusReg mask hselectNd
  have hselectCancel : run select.reverse (run select st₁) = st₁ :=
    run_reverse_cancel select st₁ hselectFree hselectWf
  have hselectInputs : ∀ w ∈ branch :: modulusReg ++ mask, st₃ w = st₂ w := by
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with (heq | hw) | hw
    · rw [heq]
      apply haddCorrect.2.2.2 branch hbranchNotTarget
      exact hbranchNeOverflow
    · apply haddCorrect.2.2.2 w
      · intro ht; exact hmodCross w hw w (by simp [ht]) rfl
      · exact hmodCross w hw overflow (by simp)
    · exact haddCorrect.1 w hw
  have hcleanupSupport : ∀ w ∈ branch :: modulusReg ++ mask,
      st₄ w = st₁ w := by
    intro w hw
    calc
      st₄ w = run select.reverse st₂ w :=
        CircuitUsesOnly.run_congr (usesOnly_reverse hselectUses) hselectInputs w hw
      _ = st₁ w := congrFun hselectCancel w
  have htarget₄ : st₄⟦ᵣtarget⟧ = st₃⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    exact (usesOnly_reverse hselectUses).preservesOutside st₃ w
      (htargetOutsideSelect w hw)
  have hoverflow₄ : st₄ overflow = st₃ overflow :=
    (usesOnly_reverse hselectUses).preservesOutside st₃ overflow
      hoverflowOutsideSelect
  have hbranch₄ : st₄ branch = st₁ branch :=
    hcleanupSupport branch (by simp)
  have hrawEq :
      st₁⟦ᵣtarget⟧ + 2 ^ target.length *
          (if st₁ branch then 1 else 0) =
        st⟦ᵣtarget⟧ + 2 ^ target.length - st⟦ᵣmodulusReg⟧ := by
    simpa [bit, hmodLen] using hsubCorrect.2.2.1
  have htarget₂' : st₂⟦ᵣtarget⟧ = st₁⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    apply hselectCorrect.2
    intro hm
    exact hmaskCross w hm w (by simp [hw]) rfl
  have hmodulus₁ : st₁⟦ᵣmodulusReg⟧ = st⟦ᵣmodulusReg⟧ :=
    Arithmetic.AgreesOn.regValue hsubCorrect.1
  have haddEq :
      st₃⟦ᵣtarget⟧ + 2 ^ target.length *
          (if st₃ overflow then 1 else 0) =
        st₁⟦ᵣtarget⟧ +
          (if st₁ branch then 0 else st⟦ᵣmodulusReg⟧) := by
    have hsum := haddCorrect.2.2.1
    rw [hselectCorrect.1, htarget₂', hmodulus₁] at hsum
    simp [bit, hcarry₂, hmaskLen] at hsum ⊢
    omega
  have harith := reduce_addback_arithmetic
    st⟦ᵣmodulusReg⟧ (2 ^ target.length) st⟦ᵣtarget⟧
    st₁⟦ᵣtarget⟧
    (if st₁ branch then 0 else st⟦ᵣmodulusReg⟧)
    st₃⟦ᵣtarget⟧ (st₁ branch) (st₃ overflow)
    hmod hfit htarget (regValue_lt_two_pow target st₁)
    (regValue_lt_two_pow target st₃) hrawEq rfl haddEq
  have hafterTarget : after⟦ᵣtarget⟧ = st⟦ᵣtarget⟧ % st⟦ᵣmodulusReg⟧ := by
    calc
      after⟦ᵣtarget⟧ = st₄⟦ᵣtarget⟧ := by
        apply regValue_congr
        intro w hw
        have hwOverflow : w ≠ overflow := by
          intro e; exact hoverflowNotTarget (e ▸ hw)
        simp [after, run_cons, run_nil, applyGate, upd, hwOverflow]
      _ = st₃⟦ᵣtarget⟧ := htarget₄
      _ = _ := harith.1
  have hafterBranch : after branch = st₁ branch := by
    simp [after, run_cons, run_nil, applyGate, upd, hbranchNeOverflow,
      hbranch₄]
  have hafterOverflow : after overflow = false := by
    simp [after, run_cons, run_nil, applyGate, upd, hbranchNeOverflow,
      hoverflow₄, hbranch₄]
    cases hq : st₁ branch <;> simp [hq] at harith ⊢ <;> exact harith.2
  have hafterOther : ∀ w, w ∉ target → w ≠ branch → after w = st w := by
    intro w hwTarget hwBranch
    by_cases hwOverflow : w = overflow
    · subst w
      exact hafterOverflow.trans hoverflow.symm
    have hgateKeep : after w = st₄ w := by
      simp [after, run_cons, run_nil, applyGate, upd, hwOverflow]
    rw [hgateKeep]
    by_cases hwSelect : w ∈ branch :: modulusReg ++ mask
    · rw [hcleanupSupport w hwSelect]
      exact hsubCorrect.2.2.2 w hwTarget hwBranch
    · have hwMask : w ∉ mask := by
        intro hm
        exact hwSelect (by simp [hm])
      calc
        st₄ w = st₃ w :=
          (usesOnly_reverse hselectUses).preservesOutside st₃ w hwSelect
        _ = st₂ w := haddCorrect.2.2.2 w hwTarget hwOverflow
        _ = st₁ w := hselectCorrect.2 w hwMask
        _ = st w := hsubCorrect.2.2.2 w hwTarget hwBranch
  have hresult :
      after⟦ᵣtarget⟧ = st⟦ᵣtarget⟧ % st⟦ᵣmodulusReg⟧ ∧
      (after branch = true ↔ st⟦ᵣmodulusReg⟧ ≤ st⟦ᵣtarget⟧) ∧
      ∀ w, w ∉ target → w ≠ branch → after w = st w :=
    ⟨hafterTarget, hafterBranch ▸ hnoBorrow, hafterOther⟩
  change let result := run (reduceWithFlag modulusReg target mask carry branch overflow) st
    result⟦ᵣtarget⟧ = st⟦ᵣtarget⟧ % st⟦ᵣmodulusReg⟧ ∧
      (result branch = true ↔ st⟦ᵣmodulusReg⟧ ≤ st⟦ᵣtarget⟧) ∧
      ∀ w, w ∉ target → w ≠ branch → result w = st w
  simp only [reduceWithFlag, run_append]
  exact hresult

theorem reduceWithFlag_tCount
    (modulusReg target mask : List Wire) (carry branch overflow : Wire)
    (hmodLen : modulusReg.length = target.length)
    (hmaskLen : mask.length = target.length) :
    tCount (reduceWithFlag modulusReg target mask carry branch overflow) =
      42 * target.length := by
  simp only [reduceWithFlag, tCount_append, Arithmetic.tCount_reverse]
  rw [inPlaceSubCarry_tCount modulusReg target carry branch hmodLen.symm,
    negativeMask_tCount branch modulusReg mask (by omega),
    inPlaceAddCarry_tCount mask target carry overflow (by omega)]
  simp [tCost]
  omega

theorem reduceWithFlag_HPFree
    (modulusReg target mask : List Wire) (carry branch overflow : Wire) :
    HPFree (reduceWithFlag modulusReg target mask carry branch overflow) := by
  simp [reduceWithFlag, inPlaceSubCarry_HPFree, negativeMask_HPFree,
    inPlaceAddCarry_HPFree, Arithmetic.hpFree_reverse]

theorem reduceWithFlag_wellFormed
    (modulusReg target mask : List Wire) (carry branch overflow : Wire)
    (hmodLen : modulusReg.length = target.length)
    (hmaskLen : mask.length = target.length)
    (hnd : (reductionWires modulusReg target mask carry branch overflow).Nodup) :
    CircuitWellFormed (reduceWithFlag modulusReg target mask carry branch overflow) := by
  obtain ⟨hsubNd, hselectNd, haddNd, hbranchOverflow, _, _⟩ :=
    reduction_nodup_components modulusReg target mask carry branch overflow hnd
  have hsub := inPlaceSubCarry_wellFormed modulusReg target carry branch
    hmodLen.symm hsubNd
  have hselect := negativeMask_wellFormed branch modulusReg mask hselectNd
  have hadd := inPlaceAddCarry_wellFormed mask target carry overflow
    (by omega) haddNd
  simp [reduceWithFlag, circuitWellFormed_append, Gate.WellFormed, hsub, hselect,
    hadd, hbranchOverflow, Arithmetic.wellFormed_reverse]

theorem reduceWithFlag_usesOnly
    (modulusReg target mask : List Wire) (carry branch overflow : Wire) :
    CircuitUsesOnly (reductionWires modulusReg target mask carry branch overflow)
      (reduceWithFlag modulusReg target mask carry branch overflow) := by
  let ws := reductionWires modulusReg target mask carry branch overflow
  have hsub : CircuitUsesOnly ws
      (inPlaceSubCarry modulusReg target carry branch) := by
    apply usesOnly_mono (inPlaceSubCarry_usesOnly modulusReg target carry branch)
    intro w hw
    simp only [inPlaceAddCarryFootprint, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    simp [ws, reductionWires]
    rcases hw with (hw | hw) | hw | hw <;> simp [hw]
  have hselect : CircuitUsesOnly ws (negativeMask branch modulusReg mask) := by
    apply usesOnly_mono (negativeMask_usesOnly branch modulusReg mask)
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    simp [ws, reductionWires]
    rcases hw with (hw | hw) | hw <;> simp [hw]
  have hadd : CircuitUsesOnly ws (inPlaceAddCarry mask target carry overflow) := by
    apply usesOnly_mono (inPlaceAddCarry_usesOnly mask target carry overflow)
    intro w hw
    simp only [inPlaceAddCarryFootprint, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    simp [ws, reductionWires]
    rcases hw with (hw | hw) | hw | hw <;> simp [hw]
  have hgates : CircuitUsesOnly ws ([Gate.X overflow, Gate.CX branch overflow] : Circuit) := by
    simp [ws, reductionWires, CircuitUsesOnly, Gate.UsesOnly]
  change CircuitUsesOnly ws _
  simp only [reduceWithFlag]
  exact usesOnly_append
    (usesOnly_append
      (usesOnly_append (usesOnly_append hsub hselect) hadd)
      (usesOnly_reverse hselect)) hgates

/-! ## Clean modular doubling -/

/-- Double a canonical residue in place, reduce once, then erase the reduction flag from
the parity of the result.  The modulus must be odd. -/
def modularDouble (modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) : Circuit :=
  circuit! {
    shiftLeftCarry (low :: high) overflow;
    reduceWithFlag modulusReg (low :: high) mask carry branch overflow;
    gate! Gate.CX low branch
  }

/-- Clean whole-state correctness of odd-modulus doubling. -/
theorem modularDouble_correct
    (modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) (st : BasisState)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length)
    (hnd : (reductionWires modulusReg (low :: high) mask carry branch overflow).Nodup)
    (hmod : 0 < st⟦ᵣmodulusReg⟧)
    (hodd : st⟦ᵣmodulusReg⟧ % 2 = 1)
    (hfit : 2 * st⟦ᵣmodulusReg⟧ ≤ 2 ^ (low :: high).length)
    (htarget : st⟦ᵣlow :: high⟧ < st⟦ᵣmodulusReg⟧)
    (hmask : Clean mask st)
    (hcarry : st carry = false) (hbranch : st branch = false)
    (hoverflow : st overflow = false) :
    let after := run
      (modularDouble modulusReg low high mask carry branch overflow) st
    after⟦ᵣlow :: high⟧ =
        (2 * st⟦ᵣlow :: high⟧) % st⟦ᵣmodulusReg⟧ ∧
      ∀ w, w ∉ low :: high → after w = st w := by
  let target := low :: high
  let shifted := run (shiftLeftCarry target overflow) st
  let reduced := run (reduceWithFlag modulusReg target mask carry branch overflow) shifted
  let after := applyGate (Gate.CX low branch) reduced
  have htarget' : st⟦ᵣtarget⟧ < st⟦ᵣmodulusReg⟧ := by
    simpa [target] using htarget
  have hfit' : 2 * st⟦ᵣmodulusReg⟧ ≤ 2 ^ target.length := by
    simpa [target] using hfit
  have hmaster :
      (branch :: (modulusReg ++ (mask ++ (target ++ [carry, overflow])))).Nodup := by
    simpa [target, reductionWires, List.append_assoc] using hnd
  obtain ⟨hbranchRest, hrestNd⟩ := List.nodup_cons.mp hmaster
  obtain ⟨hmodNd, htail₁Nd, hmodCross⟩ := List.nodup_append.mp hrestNd
  obtain ⟨hmaskNd, htail₂Nd, hmaskCross⟩ := List.nodup_append.mp htail₁Nd
  obtain ⟨htargetNd, hflagsNd, htargetFlags⟩ := List.nodup_append.mp htail₂Nd
  have hoverflowOutside : overflow ∉ target := by
    intro hw
    exact htargetFlags overflow hw overflow (by simp) rfl
  have hbranchOutside : branch ∉ target := by
    intro hw
    exact hbranchRest (by simp [hw])
  have hbranchNeOverflow : branch ≠ overflow := by
    intro e
    exact hbranchRest (by simp [e])
  have hshiftFit : 2 * st⟦ᵣtarget⟧ < 2 ^ target.length := by
    omega
  have hshift := shiftLeftCarry_noOverflow target overflow st htargetNd
    hoverflowOutside hoverflow hshiftFit
  dsimp only at hshift
  change shifted⟦ᵣtarget⟧ = 2 * st⟦ᵣtarget⟧ ∧
    shifted overflow = false ∧
    ∀ w, w ∉ target → w ≠ overflow → shifted w = st w at hshift
  have hmodulusShifted : shifted⟦ᵣmodulusReg⟧ = st⟦ᵣmodulusReg⟧ := by
    apply regValue_congr
    intro w hw
    apply hshift.2.2 w
    · intro ht
      exact hmodCross w hw w (by simp [ht]) rfl
    · exact hmodCross w hw overflow (by simp)
  have hmaskShifted : Clean mask shifted := by
    intro w hw
    rw [hshift.2.2 w]
    · exact hmask w hw
    · intro ht
      exact hmaskCross w hw w (by simp [ht]) rfl
    · exact hmaskCross w hw overflow (by simp)
  have hcarryShifted : shifted carry = false := by
    rw [hshift.2.2 carry]
    · exact hcarry
    · intro ht
      exact htargetFlags carry ht carry (by simp) rfl
    · simpa using hflagsNd
  have hbranchShifted : shifted branch = false := by
    rw [hshift.2.2 branch hbranchOutside hbranchNeOverflow]
    exact hbranch
  have hreduce := reduceWithFlag_correct modulusReg target mask carry branch overflow shifted
    (by simpa [target] using hmodLen) (by simpa [target] using hmaskLen) (by
      simpa [target] using hnd)
    (by rw [hmodulusShifted]; exact hmod)
    (by simpa [hmodulusShifted, target] using hfit)
    (by rw [hshift.1, hmodulusShifted]; omega)
    hmaskShifted hcarryShifted hbranchShifted hshift.2.1
  dsimp only at hreduce
  change reduced⟦ᵣtarget⟧ = shifted⟦ᵣtarget⟧ % shifted⟦ᵣmodulusReg⟧ ∧
    (reduced branch = true ↔ shifted⟦ᵣmodulusReg⟧ ≤ shifted⟦ᵣtarget⟧) ∧
    ∀ w, w ∉ target → w ≠ branch → reduced w = shifted w at hreduce
  have hvalueReduced : reduced⟦ᵣtarget⟧ =
      (2 * st⟦ᵣtarget⟧) % st⟦ᵣmodulusReg⟧ := by
    rw [hreduce.1, hshift.1, hmodulusShifted]
  have hbranchReduced : reduced branch = true ↔
      st⟦ᵣmodulusReg⟧ ≤ 2 * st⟦ᵣtarget⟧ := by
    simpa [hshift.1, hmodulusShifted] using hreduce.2.1
  have hoddDecomp : 1 + 2 * (st⟦ᵣmodulusReg⟧ / 2) =
      st⟦ᵣmodulusReg⟧ := by
    have h := Nat.mod_add_div st⟦ᵣmodulusReg⟧ 2
    rw [hodd] at h
    omega
  have hparity : reduced low = reduced branch := by
    have hreg : reduced⟦ᵣtarget⟧ = bit reduced low + 2 * reduced⟦ᵣhigh⟧ := by
      simp [target, regValue_cons, bit]
    cases hq : reduced branch with
    | false =>
        have hsmall : 2 * st⟦ᵣtarget⟧ < st⟦ᵣmodulusReg⟧ := by
          apply Nat.lt_of_not_ge
          intro hge
          have := hbranchReduced.mpr hge
          simp [hq] at this
        have hvalue : reduced⟦ᵣtarget⟧ = 2 * st⟦ᵣtarget⟧ := by
          rw [hvalueReduced, Nat.mod_eq_of_lt hsmall]
        rw [hvalue] at hreg
        cases hl : reduced low with
        | false => rfl
        | true =>
            simp [bit, hl] at hreg
            omega
    | true =>
        have hge : st⟦ᵣmodulusReg⟧ ≤ 2 * st⟦ᵣtarget⟧ :=
          hbranchReduced.mp hq
        have hsubLt : 2 * st⟦ᵣtarget⟧ - st⟦ᵣmodulusReg⟧ <
            st⟦ᵣmodulusReg⟧ := by omega
        have hvalue : reduced⟦ᵣtarget⟧ =
            2 * st⟦ᵣtarget⟧ - st⟦ᵣmodulusReg⟧ := by
          rw [hvalueReduced, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsubLt]
        rw [hvalue] at hreg
        cases hl : reduced low with
        | false =>
            simp [bit, hl] at hreg
            omega
        | true => rfl
  have hafterBranch : after branch = false := by
    simp [after, applyGate, hparity]
  have hafterValue : after⟦ᵣtarget⟧ =
      (2 * st⟦ᵣtarget⟧) % st⟦ᵣmodulusReg⟧ := by
    rw [← hvalueReduced]
    apply regValue_congr
    intro w hw
    have hwBranch : w ≠ branch := by
      intro e; exact hbranchOutside (e ▸ hw)
    simp [after, applyGate, upd, hwBranch]
  have hother : ∀ w, w ∉ target → after w = st w := by
    intro w hwTarget
    by_cases hwBranch : w = branch
    · subst w
      exact hafterBranch.trans hbranch.symm
    have hafterKeep : after w = reduced w := by
      simp [after, applyGate, upd, hwBranch]
    rw [hafterKeep, hreduce.2.2 w hwTarget hwBranch]
    by_cases hwOverflow : w = overflow
    · subst w
      exact hshift.2.1.trans hoverflow.symm
    · exact hshift.2.2 w hwTarget hwOverflow
  have hresult : after⟦ᵣtarget⟧ =
        (2 * st⟦ᵣtarget⟧) % st⟦ᵣmodulusReg⟧ ∧
      ∀ w, w ∉ target → after w = st w := ⟨hafterValue, hother⟩
  have hrun : run (modularDouble modulusReg low high mask carry branch overflow) st = after := by
    simp [modularDouble, after, reduced, shifted, target, run_append]
  dsimp only
  rw [hrun]
  simpa [target] using hresult

theorem modularDouble_tCount
    (modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length) :
    tCount (modularDouble modulusReg low high mask carry branch overflow) =
      42 * (low :: high).length := by
  simp [modularDouble, tCount_append,
    reduceWithFlag_tCount modulusReg (low :: high) mask carry branch overflow
      hmodLen hmaskLen, tCost]

theorem modularDouble_HPFree
    (modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) :
    HPFree (modularDouble modulusReg low high mask carry branch overflow) := by
  simp [modularDouble, shiftLeftCarry_HPFree, reduceWithFlag_HPFree]

theorem modularDouble_wellFormed
    (modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length)
    (hnd : (reductionWires modulusReg (low :: high) mask
      carry branch overflow).Nodup) :
    CircuitWellFormed (modularDouble modulusReg low high mask carry branch overflow) := by
  obtain ⟨_, _, _, _, htargetNd, hoverflowOutside⟩ :=
    reduction_nodup_components modulusReg (low :: high) mask carry branch overflow hnd
  have hmaster :
      (branch :: (modulusReg ++ (mask ++ ((low :: high) ++ [carry, overflow])))).Nodup := by
    simpa [reductionWires, List.append_assoc] using hnd
  have hbranchRest := (List.nodup_cons.mp hmaster).1
  have hlowNeBranch : low ≠ branch := by
    intro e
    exact hbranchRest (by simp [e])
  have hshift := shiftLeftCarry_wellFormed (low :: high) overflow
    htargetNd hoverflowOutside
  have hreduce := reduceWithFlag_wellFormed modulusReg (low :: high) mask
    carry branch overflow hmodLen hmaskLen hnd
  simp [modularDouble, circuitWellFormed_append, Gate.WellFormed,
    hshift, hreduce, hlowNeBranch]

theorem modularDouble_usesOnly
    (modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) :
    CircuitUsesOnly (reductionWires modulusReg (low :: high) mask carry branch overflow)
      (modularDouble modulusReg low high mask carry branch overflow) := by
  let ws := reductionWires modulusReg (low :: high) mask carry branch overflow
  have hshift : CircuitUsesOnly ws (shiftLeftCarry (low :: high) overflow) := by
    apply usesOnly_mono (shiftLeftCarry_usesOnly (low :: high) overflow)
    intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · rcases List.mem_cons.mp hw with rfl | hw
      · simp [ws, reductionWires]
      · simp [ws, reductionWires, hw]
    · simp [ws, reductionWires]
  have hreduce : CircuitUsesOnly ws
      (reduceWithFlag modulusReg (low :: high) mask carry branch overflow) := by
    simpa [ws] using
      reduceWithFlag_usesOnly modulusReg (low :: high) mask carry branch overflow
  have hgate : CircuitUsesOnly ws ([Gate.CX low branch] : Circuit) := by
    simp [ws, reductionWires, CircuitUsesOnly, Gate.UsesOnly]
  change CircuitUsesOnly ws _
  simp only [modularDouble]
  exact usesOnly_append (usesOnly_append hshift hreduce) hgate

/-! ## Clean controlled modular addition -/

/-- For canonical residues, reduction occurred exactly when the reduced sum is below the
added residue. -/
private theorem reduced_sum_lt_addend
    (modulus x y : Nat) (hx : x < modulus) (hy : y < modulus) :
    ((x + y) % modulus < y ↔ modulus ≤ x + y) := by
  by_cases hsmall : x + y < modulus
  · have hvalue : (x + y) % modulus = x + y := Nat.mod_eq_of_lt hsmall
    constructor
    · rw [hvalue]
      omega
    · omega
  · have hge : modulus ≤ x + y := Nat.le_of_not_gt hsmall
    have hsubLt : x + y - modulus < modulus := by omega
    have hvalue : (x + y) % modulus = x + y - modulus := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsubLt]
    constructor
    · intro _; exact hge
    · intro _
      rw [hvalue]
      omega

/-- Full footprint of controlled modular addition. -/
def controlledModAddWires (control : Wire) (source modulusReg target mask : List Wire)
    (carry branch overflow : Wire) : List Wire :=
  control :: source ++ reductionWires modulusReg target mask carry branch overflow

/-- Add `source` to `target` modulo the loaded modulus exactly when `control` is true, while
returning the mask and all three bit ancillas to zero. -/
def controlledModAdd (control : Wire) (source modulusReg target mask : List Wire)
    (carry branch overflow : Wire) : Circuit :=
  let copy := ModMul.maskReg control source mask
  circuit! {
    copy;
    inPlaceAddCarry mask target carry overflow;
    copy.reverse;
    reduceWithFlag modulusReg target mask carry branch overflow;
    copy;
    lessThanXor mask target carry overflow branch;
    copy.reverse
  }

/-- Clean whole-state correctness of controlled modular addition. -/
theorem controlledModAdd_correct
    (control : Wire) (source modulusReg target mask : List Wire)
    (carry branch overflow : Wire) (st : BasisState)
    (hsourceLen : source.length = target.length)
    (hmodLen : modulusReg.length = target.length)
    (hmaskLen : mask.length = target.length)
    (hnd : (controlledModAddWires control source modulusReg target mask
      carry branch overflow).Nodup)
    (hmod : 0 < st⟦ᵣmodulusReg⟧)
    (hfit : 2 * st⟦ᵣmodulusReg⟧ ≤ 2 ^ target.length)
    (hsource : st⟦ᵣsource⟧ < st⟦ᵣmodulusReg⟧)
    (htarget : st⟦ᵣtarget⟧ < st⟦ᵣmodulusReg⟧)
    (hmask : Clean mask st)
    (hcarry : st carry = false) (hbranch : st branch = false)
    (hoverflow : st overflow = false) :
    let after := run (controlledModAdd control source modulusReg target mask
      carry branch overflow) st
    after⟦ᵣtarget⟧ =
        (st⟦ᵣtarget⟧ + if st control then st⟦ᵣsource⟧ else 0) %
          st⟦ᵣmodulusReg⟧ ∧
      ∀ w, w ∉ target → after w = st w := by
  let support := control :: source ++ mask
  let copy := ModMul.maskReg control source mask
  let st₁ := run copy st
  let st₂ := run (inPlaceAddCarry mask target carry overflow) st₁
  let st₃ := run copy.reverse st₂
  let st₄ := run (reduceWithFlag modulusReg target mask carry branch overflow) st₃
  let st₅ := run copy st₄
  let st₆ := run (lessThanXor mask target carry overflow branch) st₅
  let after := run copy.reverse st₆
  have hmaster : (control :: (source ++
      (branch :: (modulusReg ++ (mask ++ (target ++ [carry, overflow])))))).Nodup := by
    simpa [controlledModAddWires, reductionWires, List.append_assoc] using hnd
  obtain ⟨hcontrolRest, hrestNd⟩ := List.nodup_cons.mp hmaster
  obtain ⟨hsourceNd, hreductionNd, hsourceCross⟩ := List.nodup_append.mp hrestNd
  have hredNd : (reductionWires modulusReg target mask carry branch overflow).Nodup := by
    simpa [reductionWires, List.append_assoc] using hreductionNd
  obtain ⟨hbranchRest, hredRestNd⟩ := List.nodup_cons.mp hreductionNd
  obtain ⟨hmodNd, htail₁Nd, hmodCross⟩ := List.nodup_append.mp hredRestNd
  obtain ⟨hmaskNd, htail₂Nd, hmaskCross⟩ := List.nodup_append.mp htail₁Nd
  obtain ⟨htargetNd, hflagsNd, htargetFlags⟩ := List.nodup_append.mp htail₂Nd
  have hcarryNeOverflow : carry ≠ overflow := by simpa using hflagsNd
  have hbranchNotTarget : branch ∉ target := by
    intro hw; exact hbranchRest (by simp [hw])
  have hbranchNeCarry : branch ≠ carry := by
    intro e; exact hbranchRest (by simp [e])
  have hbranchNeOverflow : branch ≠ overflow := by
    intro e; exact hbranchRest (by simp [e])
  have hbranchNotMask : branch ∉ mask := by
    intro hw; exact hbranchRest (by simp [hw])
  have hcontrolNotSource : control ∉ source := by
    intro hw; exact hcontrolRest (by simp [hw])
  have hcontrolNotMask : control ∉ mask := by
    intro hw; exact hcontrolRest (by simp [hw])
  have hcontrolNotTarget : control ∉ target := by
    intro hw; exact hcontrolRest (by simp [hw])
  have hcontrolNeCarry : control ≠ carry := by
    intro e; exact hcontrolRest (by simp [e])
  have hcontrolNeBranch : control ≠ branch := by
    intro e; exact hcontrolRest (by simp [e])
  have hcontrolNeOverflow : control ≠ overflow := by
    intro e; exact hcontrolRest (by simp [e])
  have hsourceMask : (source ++ mask).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hsourceNd, hmaskNd, ?_⟩
    intro x hx y hy
    exact hsourceCross x hx y (by simp [hy])
  have hcopyNd : (control :: source ++ mask).Nodup :=
    List.nodup_cons.mpr ⟨by
      intro hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hcontrolNotSource hw
      · exact hcontrolNotMask hw, hsourceMask⟩
  have haddNd : (mask ++ (target ++ [carry, overflow])).Nodup := htail₁Nd
  have hbranchOutsideComparator :
      branch ∉ inPlaceAddCarryFootprint mask target carry overflow := by
    simp only [inPlaceAddCarryFootprint, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hbranchNotMask, hbranchNotTarget⟩,
      hbranchNeCarry, hbranchNeOverflow⟩
  have hcopyUses : CircuitUsesOnly support copy := by
    apply ModMul.maskReg_usesOnly control source mask support
    · simp [support]
    · intro w hw; simp [support, hw]
    · intro w hw; simp [support, hw]
  have hcopyFree : HPFree copy := by
    simp [copy, ModMul.maskReg_HPFree]
  have hcopyWf : CircuitWellFormed copy := by
    simpa [copy] using ModMul.maskReg_wellFormed control source mask hcopyNd
  have hcopyCancel (s : BasisState) : run copy.reverse (run copy s) = s :=
    run_reverse_cancel copy s hcopyFree hcopyWf
  have hcopyValue := ModMul.maskReg_correct control source mask st
    (by omega) hcopyNd hmask
  change st₁⟦ᵣmask⟧ = if st control then st⟦ᵣsource⟧ else 0 at hcopyValue
  have hcopyOther₁ : ∀ w, w ∉ mask → st₁ w = st w := by
    intro w hw
    exact ModMul.maskReg_other control w source mask st hw
  have hoverflow₁ : st₁ overflow = false := by
    rw [hcopyOther₁ overflow]
    · exact hoverflow
    · intro hm; exact hmaskCross overflow hm overflow (by simp) rfl
  have hcarry₁ : st₁ carry = false := by
    rw [hcopyOther₁ carry]
    · exact hcarry
    · intro hm; exact hmaskCross carry hm carry (by simp) rfl
  have hadd := inPlaceAddCarry_correct mask target carry overflow st₁
    (by omega) haddNd hoverflow₁
  dsimp only at hadd
  change AgreesOn mask st₁ st₂ ∧ st₂ carry = st₁ carry ∧
    st₂⟦ᵣtarget⟧ + 2 ^ mask.length * bit st₂ overflow =
      st₁⟦ᵣmask⟧ + st₁⟦ᵣtarget⟧ + bit st₁ carry ∧
    ∀ w, w ∉ target → w ≠ overflow → st₂ w = st₁ w at hadd
  have htarget₁ : st₁⟦ᵣtarget⟧ = st⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    apply hcopyOther₁ w
    intro hm
    exact hmaskCross w hm w (by simp [hw]) rfl
  have haddendBound : (if st control then st⟦ᵣsource⟧ else 0) <
      st⟦ᵣmodulusReg⟧ := by
    cases st control <;> simp [hmod, hsource]
  have hsumBound : st⟦ᵣtarget⟧ +
      (if st control then st⟦ᵣsource⟧ else 0) < 2 ^ target.length := by
    omega
  have haddEq : st₂⟦ᵣtarget⟧ + 2 ^ target.length * bit st₂ overflow =
      st⟦ᵣtarget⟧ + (if st control then st⟦ᵣsource⟧ else 0) := by
    have hsum := hadd.2.2.1
    rw [hcopyValue, htarget₁] at hsum
    simp [bit, hcarry₁, hmaskLen] at hsum ⊢
    omega
  have hoverflow₂ : st₂ overflow = false := by
    cases ho : st₂ overflow with
    | false => rfl
    | true =>
        simp [bit, ho] at haddEq
        omega
  have htarget₂ : st₂⟦ᵣtarget⟧ =
      st⟦ᵣtarget⟧ + (if st control then st⟦ᵣsource⟧ else 0) := by
    simpa [bit, hoverflow₂] using haddEq
  have hcopyInputs₂ : ∀ w ∈ support, st₂ w = st₁ w := by
    intro w hw
    simp only [support, List.mem_cons, List.mem_append] at hw
    rcases hw with (heq | hw) | hw
    · rw [heq]
      exact hadd.2.2.2 control hcontrolNotTarget hcontrolNeOverflow
    · exact hadd.2.2.2 w
        (fun ht => hsourceCross w hw w (by simp [ht]) rfl)
        (hsourceCross w hw overflow (by simp))
    · exact hadd.1 w hw
  have hcleanupSupport₃ : ∀ w ∈ support, st₃ w = st w := by
    intro w hw
    calc
      st₃ w = run copy.reverse st₁ w :=
        CircuitUsesOnly.run_congr (usesOnly_reverse hcopyUses) hcopyInputs₂ w hw
      _ = st w := congrFun (hcopyCancel st) w
  have htarget₃ : st₃⟦ᵣtarget⟧ = st₂⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    apply (usesOnly_reverse hcopyUses).preservesOutside st₂ w
    simp only [support, List.mem_cons, List.mem_append, not_or]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro e; exact hcontrolNotTarget (e ▸ hw)
    · intro hs; exact hsourceCross w hs w (by simp [hw]) rfl
    · intro hm; exact hmaskCross w hm w (by simp [hw]) rfl
  have hoverflow₃ : st₃ overflow = false := by
    have hout : overflow ∉ support := by
      simp only [support, List.mem_cons, List.mem_append, not_or]
      refine ⟨⟨hcontrolNeOverflow.symm, ?_⟩, ?_⟩
      · intro hs; exact hsourceCross overflow hs overflow (by simp) rfl
      · intro hm; exact hmaskCross overflow hm overflow (by simp) rfl
    calc
      st₃ overflow = st₂ overflow :=
        (usesOnly_reverse hcopyUses).preservesOutside st₂ overflow hout
      _ = false := hoverflow₂
  have hstageOneOther : ∀ w, w ∉ target → st₃ w = st w := by
    intro w hwTarget
    by_cases hwSupport : w ∈ support
    · exact hcleanupSupport₃ w hwSupport
    have hreverseKeep : st₃ w = st₂ w :=
      (usesOnly_reverse hcopyUses).preservesOutside st₂ w hwSupport
    rw [hreverseKeep]
    by_cases hwOverflow : w = overflow
    · subst w; exact hoverflow₂.trans hoverflow.symm
    rw [hadd.2.2.2 w hwTarget hwOverflow]
    have hwMask : w ∉ mask := by
      intro hm; exact hwSupport (by simp [support, hm])
    exact hcopyOther₁ w hwMask
  have hmask₃ : Clean mask st₃ := by
    intro w hw
    rw [hstageOneOther w]
    · exact hmask w hw
    · intro ht; exact hmaskCross w hw w (by simp [ht]) rfl
  have hmodulus₃ : st₃⟦ᵣmodulusReg⟧ = st⟦ᵣmodulusReg⟧ := by
    apply regValue_congr
    intro w hw
    apply hstageOneOther w
    intro ht; exact hmodCross w hw w (by simp [ht]) rfl
  have hreduce := reduceWithFlag_correct modulusReg target mask carry branch overflow st₃
    hmodLen hmaskLen hredNd (by rw [hmodulus₃]; exact hmod)
    (by simpa [hmodulus₃] using hfit)
    (by rw [htarget₃, htarget₂, hmodulus₃]; omega)
    hmask₃ (hstageOneOther carry (by
      intro ht; exact htargetFlags carry ht carry (by simp) rfl) ▸ hcarry)
    (hstageOneOther branch hbranchNotTarget ▸ hbranch)
    hoverflow₃
  dsimp only at hreduce
  change st₄⟦ᵣtarget⟧ = st₃⟦ᵣtarget⟧ % st₃⟦ᵣmodulusReg⟧ ∧
    (st₄ branch = true ↔ st₃⟦ᵣmodulusReg⟧ ≤ st₃⟦ᵣtarget⟧) ∧
    ∀ w, w ∉ target → w ≠ branch → st₄ w = st₃ w at hreduce
  have hmask₄ : Clean mask st₄ := by
    intro w hw
    rw [hreduce.2.2 w]
    · exact hmask₃ w hw
    · intro ht; exact hmaskCross w hw w (by simp [ht]) rfl
    · intro e; exact hbranchNotMask (e ▸ hw)
  have hsource₄ : st₄⟦ᵣsource⟧ = st⟦ᵣsource⟧ := by
    apply regValue_congr
    intro w hw
    rw [hreduce.2.2 w]
    · exact hstageOneOther w
        (fun ht => hsourceCross w hw w (by simp [ht]) rfl)
    · intro ht; exact hsourceCross w hw w (by simp [ht]) rfl
    · exact hsourceCross w hw branch (by simp)
  have hcontrol₄ : st₄ control = st control := by
    rw [hreduce.2.2 control hcontrolNotTarget hcontrolNeBranch]
    exact hstageOneOther control hcontrolNotTarget
  have hcopyValue₅ := ModMul.maskReg_correct control source mask st₄
    (by omega) hcopyNd hmask₄
  change st₅⟦ᵣmask⟧ = if st₄ control then st₄⟦ᵣsource⟧ else 0 at hcopyValue₅
  have hcopyOther₅ : ∀ w, w ∉ mask → st₅ w = st₄ w := by
    intro w hw
    exact ModMul.maskReg_other control w source mask st₄ hw
  have hcarry₅ : st₅ carry = false := by
    rw [hcopyOther₅ carry]
    · rw [hreduce.2.2 carry]
      · exact hstageOneOther carry (by
          intro ht; exact htargetFlags carry ht carry (by simp) rfl) |>.trans hcarry
      · intro ht; exact htargetFlags carry ht carry (by simp) rfl
      · exact hbranchNeCarry.symm
    · intro hm; exact hmaskCross carry hm carry (by simp) rfl
  have hoverflow₅ : st₅ overflow = false := by
    rw [hcopyOther₅ overflow]
    · rw [hreduce.2.2 overflow]
      · exact hoverflow₃
      · intro ht; exact htargetFlags overflow ht overflow (by simp) rfl
      · exact hbranchNeOverflow.symm
    · intro hm; exact hmaskCross overflow hm overflow (by simp) rfl
  have hcompare := lessThanXor_correct mask target carry overflow branch st₅
    (by omega) haddNd hbranchOutsideComparator hcarry₅ hoverflow₅
  dsimp only at hcompare
  change st₆ branch = Bool.xor (st₅ branch)
      (decide (st₅⟦ᵣtarget⟧ < st₅⟦ᵣmask⟧)) ∧
    ∀ w, w ≠ branch → st₆ w = st₅ w at hcompare
  have htarget₅ : st₅⟦ᵣtarget⟧ = st₄⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    apply hcopyOther₅ w
    intro hm; exact hmaskCross w hm w (by simp [hw]) rfl
  have hbranch₅ : st₅ branch = st₄ branch :=
    hcopyOther₅ branch hbranchNotMask
  have hmaskValue₅ : st₅⟦ᵣmask⟧ =
      if st control then st⟦ᵣsource⟧ else 0 := by
    simpa [hcontrol₄, hsource₄] using hcopyValue₅
  have htargetValue₄ : st₄⟦ᵣtarget⟧ =
      (st⟦ᵣtarget⟧ + if st control then st⟦ᵣsource⟧ else 0) %
        st⟦ᵣmodulusReg⟧ := by
    rw [hreduce.1, htarget₃, htarget₂, hmodulus₃]
  have hbranchValue₄ : st₄ branch = true ↔
      st⟦ᵣmodulusReg⟧ ≤
        st⟦ᵣtarget⟧ + (if st control then st⟦ᵣsource⟧ else 0) := by
    simpa [hmodulus₃, htarget₃, htarget₂] using hreduce.2.1
  have hbranch₆ : st₆ branch = false := by
    let y := if st control then st⟦ᵣsource⟧ else 0
    have hy : y < st⟦ᵣmodulusReg⟧ := by simpa [y] using haddendBound
    have hpred := reduced_sum_lt_addend st⟦ᵣmodulusReg⟧
      st⟦ᵣtarget⟧ y htarget hy
    have hflag : st₅ branch = true ↔
        decide (st₅⟦ᵣtarget⟧ < st₅⟦ᵣmask⟧) = true := by
      rw [hbranch₅, hbranchValue₄]
      simpa [y, htarget₅, htargetValue₄, hmaskValue₅] using hpred.symm
    rw [hcompare.1]
    cases hb : st₅ branch <;>
      cases hp : decide (st₅⟦ᵣtarget⟧ < st₅⟦ᵣmask⟧) <;>
      simp_all
  have hcopyInputs₆ : ∀ w ∈ support, st₆ w = st₅ w := by
    intro w hw
    apply hcompare.2 w
    intro e
    have : branch ∈ support := e ▸ hw
    simp only [support, List.mem_cons, List.mem_append] at this
    rcases this with (e | hs) | hm
    · exact hcontrolNeBranch e.symm
    · exact hsourceCross branch hs branch (by simp) rfl
    · exact hbranchNotMask hm
  have hcleanupSupport : ∀ w ∈ support, after w = st₄ w := by
    intro w hw
    calc
      after w = run copy.reverse st₅ w :=
        CircuitUsesOnly.run_congr (usesOnly_reverse hcopyUses) hcopyInputs₆ w hw
      _ = st₄ w := congrFun (hcopyCancel st₄) w
  have hafterTarget : after⟦ᵣtarget⟧ = st₄⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    have hwSupport : w ∉ support := by
      simp only [support, List.mem_cons, List.mem_append, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro e; exact hcontrolNotTarget (e ▸ hw)
      · intro hs; exact hsourceCross w hs w (by simp [hw]) rfl
      · intro hm; exact hmaskCross w hm w (by simp [hw]) rfl
    calc
      after w = st₆ w := (usesOnly_reverse hcopyUses).preservesOutside st₆ w hwSupport
      _ = st₅ w := hcompare.2 w (by
        intro e; exact hbranchNotTarget (e ▸ hw))
      _ = st₄ w := hcopyOther₅ w (by
        intro hm; exact hmaskCross w hm w (by simp [hw]) rfl)
  have hother : ∀ w, w ∉ target → after w = st w := by
    intro w hwTarget
    by_cases hwBranch : w = branch
    · subst w
      have hout : branch ∉ support := by
        simp only [support, List.mem_cons, List.mem_append, not_or]
        refine ⟨⟨hcontrolNeBranch.symm, ?_⟩, hbranchNotMask⟩
        intro hs; exact hsourceCross branch hs branch (by simp) rfl
      calc
        after branch = st₆ branch :=
          (usesOnly_reverse hcopyUses).preservesOutside st₆ branch hout
        _ = false := hbranch₆
        _ = st branch := hbranch.symm
    by_cases hwSupport : w ∈ support
    · rw [hcleanupSupport w hwSupport]
      rw [hreduce.2.2 w hwTarget hwBranch]
      exact hstageOneOther w hwTarget
    · calc
        after w = st₆ w :=
          (usesOnly_reverse hcopyUses).preservesOutside st₆ w hwSupport
        _ = st₅ w := hcompare.2 w hwBranch
        _ = st₄ w := hcopyOther₅ w (by
          intro hm; exact hwSupport (by simp [support, hm]))
        _ = st₃ w := hreduce.2.2 w hwTarget hwBranch
        _ = st w := hstageOneOther w hwTarget
  have hresult : after⟦ᵣtarget⟧ =
        (st⟦ᵣtarget⟧ + if st control then st⟦ᵣsource⟧ else 0) %
          st⟦ᵣmodulusReg⟧ ∧
      ∀ w, w ∉ target → after w = st w := by
    rw [hafterTarget, htargetValue₄]
    exact ⟨rfl, hother⟩
  have hrun : run (controlledModAdd control source modulusReg target mask
      carry branch overflow) st = after := by
    simp [controlledModAdd, after, st₆, st₅, st₄, st₃, st₂, st₁, copy, run_append]
  dsimp only
  rw [hrun]
  exact hresult

theorem controlledModAdd_tCount
    (control : Wire) (source modulusReg target mask : List Wire)
    (carry branch overflow : Wire)
    (hsourceLen : source.length = target.length)
    (hmodLen : modulusReg.length = target.length)
    (hmaskLen : mask.length = target.length) :
    tCount (controlledModAdd control source modulusReg target mask
      carry branch overflow) = 112 * target.length := by
  simp only [controlledModAdd, tCount_append, Arithmetic.tCount_reverse]
  rw [ModMul.maskReg_tCount control source mask (by omega),
    inPlaceAddCarry_tCount mask target carry overflow (by omega),
    reduceWithFlag_tCount modulusReg target mask carry branch overflow hmodLen hmaskLen,
    lessThanXor_tCount mask target carry overflow branch (by omega)]
  omega

theorem controlledModAdd_HPFree
    (control : Wire) (source modulusReg target mask : List Wire)
    (carry branch overflow : Wire) :
    HPFree (controlledModAdd control source modulusReg target mask
      carry branch overflow) := by
  simp [controlledModAdd, ModMul.maskReg_HPFree, inPlaceAddCarry_HPFree,
    reduceWithFlag_HPFree, lessThanXor_HPFree, Arithmetic.hpFree_reverse]

theorem controlledModAdd_wellFormed
    (control : Wire) (source modulusReg target mask : List Wire)
    (carry branch overflow : Wire)
    (hmodLen : modulusReg.length = target.length)
    (hmaskLen : mask.length = target.length)
    (hnd : (controlledModAddWires control source modulusReg target mask
      carry branch overflow).Nodup) :
    CircuitWellFormed (controlledModAdd control source modulusReg target mask
      carry branch overflow) := by
  have hmaster : (control :: (source ++
      (branch :: (modulusReg ++ (mask ++ (target ++ [carry, overflow])))))).Nodup := by
    simpa [controlledModAddWires, reductionWires, List.append_assoc] using hnd
  obtain ⟨hcontrolRest, hrestNd⟩ := List.nodup_cons.mp hmaster
  obtain ⟨hsourceNd, hreductionNd, hsourceCross⟩ := List.nodup_append.mp hrestNd
  obtain ⟨hbranchRest, hredRestNd⟩ := List.nodup_cons.mp hreductionNd
  obtain ⟨hmodNd, htail₁Nd, hmodCross⟩ := List.nodup_append.mp hredRestNd
  obtain ⟨hmaskNd, htail₂Nd, hmaskCross⟩ := List.nodup_append.mp htail₁Nd
  have hcontrolNotSource : control ∉ source := by
    intro hw; exact hcontrolRest (by simp [hw])
  have hcontrolNotMask : control ∉ mask := by
    intro hw; exact hcontrolRest (by simp [hw])
  have hsourceMask : (source ++ mask).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hsourceNd, hmaskNd, ?_⟩
    intro x hx y hy
    exact hsourceCross x hx y (by simp [hy])
  have hcopyNd : (control :: source ++ mask).Nodup :=
    List.nodup_cons.mpr ⟨by
      intro hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hcontrolNotSource hw
      · exact hcontrolNotMask hw, hsourceMask⟩
  have hredNd : (reductionWires modulusReg target mask carry branch overflow).Nodup := by
    simpa [reductionWires, List.append_assoc] using hreductionNd
  have hbranchOutside :
      branch ∉ inPlaceAddCarryFootprint mask target carry overflow := by
    have hbranchNotMask : branch ∉ mask := by
      intro hw; exact hbranchRest (by simp [hw])
    have hbranchNotTarget : branch ∉ target := by
      intro hw; exact hbranchRest (by simp [hw])
    have hbranchNeCarry : branch ≠ carry := by
      intro e; exact hbranchRest (by simp [e])
    have hbranchNeOverflow : branch ≠ overflow := by
      intro e; exact hbranchRest (by simp [e])
    simp only [inPlaceAddCarryFootprint, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨⟨hbranchNotMask, hbranchNotTarget⟩,
      hbranchNeCarry, hbranchNeOverflow⟩
  have hcopy := ModMul.maskReg_wellFormed control source mask hcopyNd
  have hadd := inPlaceAddCarry_wellFormed mask target carry overflow
    (by omega) htail₁Nd
  have hreduce := reduceWithFlag_wellFormed modulusReg target mask carry branch overflow
    hmodLen hmaskLen hredNd
  have hcompare := lessThanXor_wellFormed mask target carry overflow branch
    (by omega) htail₁Nd hbranchOutside
  simp [controlledModAdd, circuitWellFormed_append, hcopy, hadd, hreduce, hcompare,
    Arithmetic.wellFormed_reverse]

theorem controlledModAdd_usesOnly
    (control : Wire) (source modulusReg target mask : List Wire)
    (carry branch overflow : Wire) :
    CircuitUsesOnly
      (controlledModAddWires control source modulusReg target mask carry branch overflow)
      (controlledModAdd control source modulusReg target mask carry branch overflow) := by
  let ws := controlledModAddWires control source modulusReg target mask
    carry branch overflow
  have hcopy : CircuitUsesOnly ws (ModMul.maskReg control source mask) := by
    apply ModMul.maskReg_usesOnly control source mask ws
    · simp [ws, controlledModAddWires]
    · intro w hw; simp [ws, controlledModAddWires, hw]
    · intro w hw; simp [ws, controlledModAddWires, reductionWires, hw]
  have hadd : CircuitUsesOnly ws (inPlaceAddCarry mask target carry overflow) := by
    apply usesOnly_mono (inPlaceAddCarry_usesOnly mask target carry overflow)
    intro w hw
    simp only [inPlaceAddCarryFootprint, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    simp [ws, controlledModAddWires, reductionWires]
    rcases hw with (hw | hw) | hw | hw <;> simp [hw]
  have hreduce : CircuitUsesOnly ws
      (reduceWithFlag modulusReg target mask carry branch overflow) := by
    apply usesOnly_mono
      (reduceWithFlag_usesOnly modulusReg target mask carry branch overflow)
    intro w hw
    simp [ws, controlledModAddWires, hw]
  have hcompare : CircuitUsesOnly ws
      (lessThanXor mask target carry overflow branch) := by
    apply usesOnly_mono (lessThanXor_usesOnly mask target carry overflow branch)
    intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    simp [ws, controlledModAddWires, reductionWires]
    rcases hw with hw | hw
    · simp only [inPlaceAddCarryFootprint, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with (hw | hw) | hw | hw <;> simp [hw]
    · simp [hw]
  change CircuitUsesOnly ws _
  simp only [controlledModAdd]
  exact usesOnly_append
    (usesOnly_append
      (usesOnly_append
        (usesOnly_append
          (usesOnly_append
            (usesOnly_append hcopy hadd) (usesOnly_reverse hcopy)) hreduce) hcopy)
        hcompare)
      (usesOnly_reverse hcopy)

end ShorECDLP
