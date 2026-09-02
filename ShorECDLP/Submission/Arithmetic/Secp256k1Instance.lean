import ShorECDLP.Submission.Arithmetic.ModAdd
import ShorECDLP.Submission.Arithmetic.LowSpaceModMul
import ShorECDLP.Submission.Arithmetic.ModExp
import ShorECDLP.Submission.Arithmetic.FermatInv
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# Concrete secp256k1 base-field arithmetic allocation

The generic arithmetic modules certify any supplied wiring or plan.  This module supplies a
concrete instance for the secp256k1 base-field modulus `p`, at width 257.  The extra bit is
required by `ModAddWiring.fit`, namely `2 * p ≤ 2 ^ 257`.

## Programs (syntax-sugared)

```text
addProgram lhs rhs out scratch
  := modAdd over seven fresh scratch blocks

mulProgram lhs bits out scratch
  := load p into one scratch register;
     for bits from most significant to least significant:
       out := 2*out mod p;
       out := out + (bit ? lhs : 0) mod p;
     unload p

secpProgram
  := Bennett-clean square-and-multiply over all 257 exponent bits,
     using the concrete multiplier plan above and one shared multiplier workspace
```

Wire allocation uses numbered blocks of capacity 257.  Every register occupies a complete block;
one-bit carry registers occupy a one-wire block.  Distinct block identifiers imply disjoint wire
ranges.  The multiplier declares 771 public wires and 517 reusable work wires, for 1,288 total.
The fixed exponentiation schedule still owns 770 history registers, but every multiplication call
reuses that same 517-wire workspace.

## Specification

`add_wiring`, `mul_contract`, and `secp_modExp_contract` certify the exact programs above against
the existing `ModAddWiring`, `ModMulContract`, and `ModExpContract` interfaces. Direct
`*Program_correct` and `*Program_tCount` theorems expose the same correctness and cost facts
without a contract projection. Their instantiated costs are respectively `23,387`, `10,171,546`,
and `10,436,930,882` T gates. Finally, `secp_fermat_inverse` specializes `FermatInv.correct` to
this same `secpProgram`; it introduces no second circuit or independent inversion claim.
-/

namespace ShorECDLP
namespace Secp256k1Instance

open Classical
open scoped ArithmeticNotation

def fieldWidth : Nat := 257

structure Block where
  id : Nat
  size : Nat
  size_le : size ≤ fieldWidth

namespace Block

def wires (block : Block) : List Wire :=
  List.range' (fieldWidth * block.id) block.size

@[simp] theorem wires_length (block : Block) : block.wires.length = block.size := by
  simp [wires]

end Block

def regBlock (id : Nat) : Block := ⟨id, fieldWidth, le_rfl⟩

def bitBlock (id : Nat) : Block := ⟨id, 1, by simp [fieldWidth]⟩

def blocksWires (blocks : List Block) : List Wire := blocks.flatMap Block.wires

def reg (id : Nat) : ModExp.Reg fieldWidth where
  wires := (regBlock id).wires
  length_eq := by simp [regBlock, fieldWidth]

def bitWire (id : Nat) : Wire := fieldWidth * id

def addScratchBlocks (start : Nat) : List Block :=
  [regBlock start, regBlock (start + 1), regBlock (start + 2), bitBlock (start + 3),
    regBlock (start + 4), bitBlock (start + 5), regBlock (start + 6)]

def addWork (start : Nat) : List Wire := blocksWires (addScratchBlocks start)

def addProgram (lhsId rhsId outId start : Nat) : Circuit :=
  modAdd (reg lhsId).wires (reg rhsId).wires (reg outId).wires
    (reg start).wires (reg (start + 1)).wires (reg (start + 2)).wires
    (bitWire (start + 3)) (reg (start + 4)).wires
    (bitWire (start + 5)) (reg (start + 6)).wires p

def addCost : Nat := 91 * fieldWidth

/-! ## Allocation and arithmetic facts -/

namespace Block

theorem wires_nodup (block : Block) : block.wires.Nodup := by
  exact List.nodup_range'

theorem mem_bounds {block : Block} {wire : Wire} (hmem : wire ∈ block.wires) :
    fieldWidth * block.id ≤ wire ∧ wire < fieldWidth * (block.id + 1) := by
  rw [wires, List.mem_range'] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  constructor
  · omega
  · calc
      fieldWidth * block.id + 1 * i < fieldWidth * block.id + block.size := by omega
      _ ≤ fieldWidth * block.id + fieldWidth := Nat.add_le_add_left block.size_le _
      _ = fieldWidth * (block.id + 1) := by simp [fieldWidth, Nat.mul_add]

theorem disjoint_of_id_ne {left right : Block} (hne : left.id ≠ right.id) :
    List.Disjoint left.wires right.wires := by
  rw [List.disjoint_left]
  intro wire hleft hright
  have hl := mem_bounds hleft
  have hr := mem_bounds hright
  by_cases hlt : left.id < right.id
  · have hsep : fieldWidth * (left.id + 1) ≤ fieldWidth * right.id :=
      Nat.mul_le_mul_left fieldWidth (Nat.succ_le_iff.mpr hlt)
    exact (Nat.not_lt_of_ge hr.1) (Nat.lt_of_lt_of_le hl.2 hsep)
  · have hgt : right.id < left.id := by omega
    have hsep : fieldWidth * (right.id + 1) ≤ fieldWidth * left.id :=
      Nat.mul_le_mul_left fieldWidth (Nat.succ_le_iff.mpr hgt)
    exact (Nat.not_lt_of_ge hl.1) (Nat.lt_of_lt_of_le hr.2 hsep)

end Block

@[simp] theorem regBlock_id (id : Nat) : (regBlock id).id = id := rfl
@[simp] theorem bitBlock_id (id : Nat) : (bitBlock id).id = id := rfl

theorem blocksWires_nodup (blocks : List Block) (hids : (blocks.map Block.id).Nodup) :
    (blocksWires blocks).Nodup := by
  induction blocks with
  | nil => simp [blocksWires]
  | cons block blocks ih =>
      rw [blocksWires, List.flatMap_cons, List.nodup_append]
      have hid := List.nodup_cons.mp hids
      refine ⟨block.wires_nodup, ih hid.2, ?_⟩
      intro x hx y hy
      simp only [List.mem_flatMap] at hy
      obtain ⟨other, hother, hy⟩ := hy
      have hne : block.id ≠ other.id := by
        intro e
        apply hid.1
        rw [List.mem_map]
        exact ⟨other, hother, e.symm⟩
      intro e
      subst y
      exact (List.disjoint_left.mp (block.disjoint_of_id_ne hne)) hx hy

@[simp] theorem bitBlock_wires (id : Nat) : (bitBlock id).wires = [bitWire id] := by
  simp [Block.wires, bitBlock, bitWire]

@[simp] theorem reg_wires (id : Nat) : (reg id).wires = (regBlock id).wires := rfl

theorem p_pos : 0 < p := by norm_num [p]

set_option exponentiation.threshold 300 in
theorem p_fits : 2 * p ≤ 2 ^ fieldWidth := by
  have hp : p ≤ 2 ^ 256 := by
    unfold p
    exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  calc
    2 * p ≤ 2 * 2 ^ 256 := Nat.mul_le_mul_left 2 hp
    _ = 2 ^ fieldWidth := by
      change 2 * 2 ^ 256 = 2 ^ 256 * 2
      omega

theorem carryOut_mem_of_nonempty (cin : Wire) :
    ∀ (couts : List Wire), couts ≠ [] → carryOut cin couts ∈ couts
  | [], h => (h rfl).elim
  | co :: cs, _ => by
      cases cs with
      | nil => simp [carryOut]
      | cons next rest =>
          rw [carryOut]
          exact List.mem_cons_of_mem co
            (carryOut_mem_of_nonempty co (next :: rest) (by simp))

theorem addWork_eq_layoutWork (lhsId rhsId outId start : Nat) :
    addWork start =
      (modAddLayout (reg lhsId).wires (reg rhsId).wires (reg outId).wires
        (reg start).wires (reg (start + 1)).wires (reg (start + 2)).wires
        (bitWire (start + 3)) (reg (start + 4)).wires
        (bitWire (start + 5)) (reg (start + 6)).wires).work := by
  simp [addWork, addScratchBlocks, blocksWires, modAddLayout, bitBlock_wires,
    List.append_assoc]

/-- Equal-length, globally distinct register and carry wires satisfy the ripple wiring predicate. -/
theorem wiresOK_of_nodup :
    ∀ (a b sum : List Wire) (cin : Wire) (couts : List Wire),
      b.length = a.length → sum.length = a.length → couts.length = a.length →
      (a ++ b ++ sum ++ [cin] ++ couts).Nodup → wiresOK a b sum cin couts := by
  intro a
  induction a with
  | nil =>
      intro b sum cin couts hb hs hc _
      obtain rfl : b = [] := List.length_eq_zero_iff.mp hb
      obtain rfl : sum = [] := List.length_eq_zero_iff.mp hs
      obtain rfl : couts = [] := List.length_eq_zero_iff.mp hc
      trivial
  | cons a as ih =>
      intro b sum cin couts hb hs hc hnd
      cases b with
      | nil => simp at hb
      | cons b bs =>
          cases sum with
          | nil => simp at hs
          | cons s ss =>
              cases couts with
              | nil => simp at hc
              | cons co cs =>
                  have hb' : bs.length = as.length := by simpa using hb
                  have hs' : ss.length = as.length := by simpa using hs
                  have hc' : cs.length = as.length := by simpa using hc
                  have hlocalSub : [a, b, s, cin, co].Sublist
                      ((a :: as) ++ (b :: bs) ++ (s :: ss) ++ [cin] ++ (co :: cs)) := by
                    have ha : [a].Sublist (a :: as) := by simp
                    have hb : [b].Sublist (b :: bs) := by simp
                    have hs : [s].Sublist (s :: ss) := by simp
                    have hcin : [cin].Sublist [cin] := List.Sublist.refl _
                    have hco : [co].Sublist (co :: cs) := by simp
                    simpa [List.append_assoc] using
                      ((((ha.append hb).append hs).append hcin).append hco)
                  have hlocal := List.Nodup.sublist hlocalSub hnd
                  have hab : a ≠ b := by intro e; subst b; simp at hlocal
                  have hacin : a ≠ cin := by intro e; subst cin; simp at hlocal
                  have has : a ≠ s := by intro e; subst s; simp at hlocal
                  have haco : a ≠ co := by intro e; subst co; simp at hlocal
                  have hbcin : b ≠ cin := by intro e; subst cin; simp at hlocal
                  have hbs : b ≠ s := by intro e; subst s; simp at hlocal
                  have hbco : b ≠ co := by intro e; subst co; simp at hlocal
                  have hcins : cin ≠ s := by intro e; subst s; simp at hlocal
                  have hcinco : cin ≠ co := by intro e; subst co; simp at hlocal
                  have hsco : s ≠ co := by intro e; subst co; simp at hlocal
                  have hselectedSub : (as ++ bs ++ (s :: ss) ++ (co :: cs)).Sublist
                      ((a :: as) ++ (b :: bs) ++ (s :: ss) ++ [cin] ++ (co :: cs)) := by
                    have ha : as.Sublist (a :: as) :=
                      List.Sublist.cons a (List.Sublist.refl as)
                    have hb : bs.Sublist (b :: bs) :=
                      List.Sublist.cons b (List.Sublist.refl bs)
                    have hcin : ([] : List Wire).Sublist [cin] := List.nil_sublist _
                    simpa [List.append_assoc] using
                      ((((ha.append hb).append (List.Sublist.refl (s :: ss))).append hcin).append
                        (List.Sublist.refl (co :: cs)))
                  have hselected := List.Nodup.sublist hselectedSub hnd
                  have hshape : (as ++ (bs ++ ((s :: ss) ++ (co :: cs)))).Nodup := by
                    simpa [List.append_assoc] using hselected
                  obtain ⟨_, hrest, hAsRest⟩ := List.nodup_append.mp hshape
                  obtain ⟨_, hSC, hBsRest⟩ := List.nodup_append.mp hrest
                  obtain ⟨hS, hCo, hSCross⟩ := List.nodup_append.mp hSC
                  have hAs : ∀ x ∈ as, s ≠ x ∧ co ≠ x := by
                    intro x hx
                    exact ⟨(hAsRest x hx s (by simp)).symm,
                      (hAsRest x hx co (by simp)).symm⟩
                  have hBs : ∀ x ∈ bs, s ≠ x ∧ co ≠ x := by
                    intro x hx
                    exact ⟨(hBsRest x hx s (by simp)).symm,
                      (hBsRest x hx co (by simp)).symm⟩
                  have hSs : ∀ x ∈ ss, s ≠ x ∧ co ≠ x := by
                    intro x hx
                    refine ⟨?_, (hSCross x (by simp [hx]) co (by simp)).symm⟩
                    intro e; subst x; exact (List.nodup_cons.mp hS).1 hx
                  have hCs : ∀ x ∈ cs, s ≠ x ∧ co ≠ x := by
                    intro x hx
                    refine ⟨hSCross s (by simp) x (by simp [hx]), ?_⟩
                    intro e; subst x; exact (List.nodup_cons.mp hCo).1 hx
                  have htailSub : (as ++ bs ++ ss ++ [co] ++ cs).Sublist
                      (as ++ bs ++ (s :: ss) ++ (co :: cs)) := by
                    simp [List.append_assoc]
                  have htail := List.Nodup.sublist htailSub hselected
                  simp only [wiresOK]
                  exact ⟨⟨hab, hacin, has, haco, hbcin, hbs, hbco, hcins, hcinco, hsco⟩,
                    hAs, hBs, hSs, hCs, ih bs ss co cs hb' hs' hc' htail⟩

set_option maxRecDepth 10000 in
theorem add_wiring (lhsId rhsId outId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hout : outId < start)
    (hlr : lhsId ≠ rhsId) :
    ModAddWiring (reg lhsId).wires (reg rhsId).wires (reg outId).wires
      (reg start).wires (reg (start + 1)).wires (reg (start + 2)).wires
      (bitWire (start + 3)) (reg (start + 4)).wires
      (bitWire (start + 5)) (reg (start + 6)).wires p := by
  let lhs := (reg lhsId).wires
  let rhs := (reg rhsId).wires
  let out := (reg outId).wires
  let sum := (reg start).wires
  let constReg := (reg (start + 1)).wires
  let candidate := (reg (start + 2)).wires
  let cin₁ := bitWire (start + 3)
  let couts₁ := (reg (start + 4)).wires
  let cin₂ := bitWire (start + 5)
  let couts₂ := (reg (start + 6)).wires
  have hAddIds :
      ([lhsId, rhsId, start, start + 3, start + 4] : List Nat).Nodup := by
    simp [List.nodup_cons, hlr]
    omega
  have hAddNodup :
      ((reg lhsId).wires ++ (reg rhsId).wires ++ (reg start).wires ++
        [cin₁] ++ couts₁).Nodup := by
    have h := blocksWires_nodup
      [regBlock lhsId, regBlock rhsId, regBlock start, bitBlock (start + 3),
        regBlock (start + 4)] (by simpa using hAddIds)
    simpa [blocksWires, cin₁, couts₁, List.append_assoc] using h
  have hRedIds :
      ([start, start + 1, start + 2, start + 5, start + 6] : List Nat).Nodup := by
    simp [List.nodup_cons]
  have hRedNodup :
      ((reg start).wires ++ (reg (start + 1)).wires ++ (reg (start + 2)).wires ++
        [cin₂] ++ couts₂).Nodup := by
    have h := blocksWires_nodup
      [regBlock start, regBlock (start + 1), regBlock (start + 2), bitBlock (start + 5),
        regBlock (start + 6)] (by
          change [start, start + 1, start + 2, start + 5, start + 6].Nodup
          exact hRedIds)
    simpa [blocksWires, cin₂, couts₂, List.append_assoc] using h
  have hSelectIds :
      ([start + 6, start, start + 2, outId] : List Nat).Nodup := by
    simp [List.nodup_cons]
    omega
  have hSelectAll :
      (couts₂ ++ (reg start).wires ++ (reg (start + 2)).wires ++
        (reg outId).wires).Nodup := by
    have h := blocksWires_nodup
      [regBlock (start + 6), regBlock start, regBlock (start + 2), regBlock outId]
      (by simpa using hSelectIds)
    simpa [blocksWires, couts₂, List.append_assoc] using h
  have hcouts₂Nonempty : couts₂ ≠ [] := by
    intro e
    have := congrArg List.length e
    simp [couts₂, regBlock, fieldWidth] at this
  have hcarryMem : carryOut cin₂ couts₂ ∈ couts₂ :=
    carryOut_mem_of_nonempty cin₂ couts₂ hcouts₂Nonempty
  have hselectNodup :
      (carryOut cin₂ couts₂ ::
        ((reg start).wires ++ (reg (start + 2)).wires ++ (reg outId).wires)).Nodup := by
    obtain ⟨hcoutNd, hbodyNd, hcross⟩ := List.nodup_append.mp (by
      simpa [List.append_assoc] using hSelectAll)
    exact List.nodup_cons.mpr ⟨fun hmem => hcross _ hcarryMem _ hmem rfl, hbodyNd⟩
  have wiring :
      ModAddWiring lhs rhs out sum constReg candidate cin₁ couts₁ cin₂ couts₂ p := by
    refine {
      rhsLen := (reg rhsId).length_eq.trans (reg lhsId).length_eq.symm
      sumLen := (reg start).length_eq.trans (reg lhsId).length_eq.symm
      addCarryLen := (reg (start + 4)).length_eq.trans (reg lhsId).length_eq.symm
      constLen := (reg (start + 1)).length_eq.trans (reg start).length_eq.symm
      candidateLen := (reg (start + 2)).length_eq.trans (reg start).length_eq.symm
      redCarryLen := (reg (start + 6)).length_eq.trans (reg start).length_eq.symm
      outLen := (reg outId).length_eq.trans (reg lhsId).length_eq.symm
      addOK := ?_
      redOK := ?_
      selectOK := ?_
      modulusPos := p_pos
      fit := by
        change 2 * p ≤ 2 ^ (reg lhsId).wires.length
        rw [(reg lhsId).length_eq]
        exact p_fits
    }
    · change wiresOK (reg lhsId).wires (reg rhsId).wires (reg start).wires cin₁ couts₁
      apply wiresOK_of_nodup
      · exact (reg rhsId).length_eq.trans (reg lhsId).length_eq.symm
      · exact (reg start).length_eq.trans (reg lhsId).length_eq.symm
      · exact (reg (start + 4)).length_eq.trans (reg lhsId).length_eq.symm
      · exact hAddNodup
    · change wiresOK (reg start).wires (reg (start + 1)).wires
        (reg (start + 2)).wires cin₂ couts₂
      apply wiresOK_of_nodup
      · exact (reg (start + 1)).length_eq.trans (reg start).length_eq.symm
      · exact (reg (start + 2)).length_eq.trans (reg start).length_eq.symm
      · exact (reg (start + 6)).length_eq.trans (reg start).length_eq.symm
      · exact hRedNodup
    · change selectOK (carryOut cin₂ couts₂) (reg start).wires
        (reg (start + 2)).wires (reg outId).wires
      exact ModExp.selectOK_of_nodup _ _ _ _ hselectNodup
  simpa [lhs, rhs, out, sum, constReg, candidate, cin₁, couts₁, cin₂, couts₂]
    using wiring

set_option maxRecDepth 10000 in
theorem add_contract (lhsId rhsId outId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hout : outId < start)
    (hlr : lhsId ≠ rhsId) :
    ModAddContract (addProgram lhsId rhsId outId start)
      { lhs := (reg lhsId).wires, rhs := (reg rhsId).wires,
        out := (reg outId).wires, work := addWork start }
      p addCost := by
  have hcontract := modAdd_contract (reg lhsId).wires (reg rhsId).wires (reg outId).wires
    (reg start).wires (reg (start + 1)).wires (reg (start + 2)).wires
    (bitWire (start + 3)) (reg (start + 4)).wires
    (bitWire (start + 5)) (reg (start + 6)).wires p
    (add_wiring lhsId rhsId outId start hlhs hrhs hout hlr)
  rw [(reg lhsId).length_eq] at hcontract
  simpa [addProgram, addCost, addWork_eq_layoutWork lhsId rhsId outId start] using hcontract

set_option maxRecDepth 10000 in
/-- Direct correctness theorem for a placed width-257 modular-addition program. -/
theorem addProgram_correct (lhsId rhsId outId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hout : outId < start)
    (hlr : lhsId ≠ rhsId) (st : BasisState)
    (hlayout :
      ({ lhs := (reg lhsId).wires
         rhs := (reg rhsId).wires
         out := (reg outId).wires
         work := addWork start } : RegisterLayout).Valid)
    (hlhsBound : st⟦ᵣ(reg lhsId).wires⟧ < p)
    (hrhsBound : st⟦ᵣ(reg rhsId).wires⟧ < p)
    (hclean : clean((reg outId).wires ++ addWork start, st)) :
    let after := ⟪addProgram lhsId rhsId outId start⟫ st
    AgreesOn (reg lhsId).wires st after ∧
      AgreesOn (reg rhsId).wires st after ∧
      after⟦ᵣ(reg outId).wires⟧ =
        (st⟦ᵣ(reg lhsId).wires⟧ + st⟦ᵣ(reg rhsId).wires⟧) % p ∧
      clean(addWork start, after) := by
  exact (add_contract lhsId rhsId outId start hlhs hrhs hout hlr).correct
    st hlayout hlhsBound hrhsBound hclean

set_option maxRecDepth 10000 in
/-- Exact T-count for any placed width-257 modular-addition program. -/
theorem addProgram_tCount (lhsId rhsId outId start : Nat) :
    tCount (addProgram lhsId rhsId outId start) = addCost := by
  simpa [addProgram, addCost] using
    modAdd_tCount (reg lhsId).wires (reg rhsId).wires (reg outId).wires
      (reg start).wires (reg (start + 1)).wires (reg (start + 2)).wires
      (bitWire (start + 3)) (reg (start + 4)).wires
      (bitWire (start + 5)) (reg (start + 6)).wires p
      ((reg rhsId).length_eq.trans (reg lhsId).length_eq.symm)
      ((reg start).length_eq.trans (reg lhsId).length_eq.symm)
      ((reg (start + 4)).length_eq.trans (reg lhsId).length_eq.symm)
      ((reg (start + 1)).length_eq.trans (reg start).length_eq.symm)
      ((reg (start + 2)).length_eq.trans (reg start).length_eq.symm)
      ((reg (start + 6)).length_eq.trans (reg start).length_eq.symm)
      ((reg outId).length_eq.trans (reg lhsId).length_eq.symm)

theorem not_mem_blocksWires_of_source (source : Block) (blocks : List Block) (wire : Wire)
    (hwire : wire ∈ source.wires) (hid : source.id ∉ blocks.map Block.id) :
    wire ∉ blocksWires blocks := by
  intro hmem
  simp only [blocksWires, List.mem_flatMap] at hmem
  obtain ⟨block, hblock, hwireBlock⟩ := hmem
  have hne : source.id ≠ block.id := by
    intro e
    apply hid
    rw [List.mem_map]
    exact ⟨block, hblock, e.symm⟩
  exact (List.disjoint_left.mp (source.disjoint_of_id_ne hne)) hwire hwireBlock

theorem blocksWires_disjoint_of_ids (left right : List Block)
    (hids : ((left ++ right).map Block.id).Nodup) :
    ∀ x ∈ blocksWires left, ∀ y ∈ blocksWires right, x ≠ y := by
  have h := blocksWires_nodup (left ++ right) hids
  rw [blocksWires, List.flatMap_append, List.nodup_append] at h
  exact h.2.2

/-! ## Low-space multiplication allocation -/

/-- All but the low bit of a concrete field register. -/
def regHigh (id : Nat) : List Wire :=
  List.range' (bitWire id + 1) (fieldWidth - 1)

@[simp] theorem reg_wires_eq_low_high (id : Nat) :
    (reg id).wires = bitWire id :: regHigh id := by
  change List.range' (257 * id) 257 =
    257 * id :: List.range' (257 * id + 1) 256
  rw [show (257 : Nat) = 256 + 1 by omega, List.range'_succ]

def mulCarry (start : Nat) : Wire := bitWire (start + 1)
def mulBranch (start : Nat) : Wire := bitWire (start + 2)
def mulOverflow (start : Nat) : Wire := bitWire (start + 3)

/-- One loaded modulus register, one reusable mask, and three one-bit flags. -/
def mulWork (modulusId start : Nat) : List Wire :=
  LowSpaceModMul.work (reg modulusId).wires (reg start).wires
    (mulCarry start) (mulBranch start) (mulOverflow start)

/-- Concrete low-space multiplier program. -/
def mulProgram (lhsId rhsId outId modulusId start : Nat) : Circuit :=
  LowSpaceModMul.program p (reg lhsId).wires (reg rhsId).wires
    (reg modulusId).wires (bitWire outId) (regHigh outId) (reg start).wires
    (mulCarry start) (mulBranch start) (mulOverflow start)

def mulCost : Nat := 154 * fieldWidth * fieldWidth

set_option maxRecDepth 10000 in
theorem mul_contract (lhsId rhsId outId modulusId start : Nat)
    (_hlhs : lhsId < start) (_hrhs : rhsId < start) (_hmodulus : modulusId < start)
    (_hlr : lhsId ≠ rhsId) (_hlm : lhsId ≠ modulusId) (_hrm : rhsId ≠ modulusId) :
    ModMulContract (mulProgram lhsId rhsId outId modulusId start)
      { lhs := (reg lhsId).wires, rhs := (reg rhsId).wires,
        out := (reg outId).wires, work := mulWork modulusId start }
      p mulCost := by
  have hsourceLen : (reg lhsId).wires.length =
      (bitWire outId :: regHigh outId).length := by
    rw [← reg_wires_eq_low_high]
    exact (reg lhsId).length_eq.trans (reg outId).length_eq.symm
  have hmodLen : (reg modulusId).wires.length =
      (bitWire outId :: regHigh outId).length := by
    rw [← reg_wires_eq_low_high]
    exact (reg modulusId).length_eq.trans (reg outId).length_eq.symm
  have hmaskLen : (reg start).wires.length =
      (bitWire outId :: regHigh outId).length := by
    rw [← reg_wires_eq_low_high]
    exact (reg start).length_eq.trans (reg outId).length_eq.symm
  have hcontract := LowSpaceModMul.modMul_contract p (reg lhsId).wires
    (reg rhsId).wires (reg modulusId).wires (bitWire outId) (regHigh outId)
    (reg start).wires (mulCarry start) (mulBranch start) (mulOverflow start)
    p_pos (by norm_num [p]) hsourceLen hmodLen hmaskLen p_fits
  simpa [mulProgram, mulWork, mulCost, LowSpaceModMul.layout,
    reg_wires_eq_low_high] using hcontract

/-- Direct correctness theorem for any placed low-space width-257 multiplier. -/
theorem mulProgram_correct (lhsId rhsId outId modulusId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hmodulus : modulusId < start)
    (hlr : lhsId ≠ rhsId) (hlm : lhsId ≠ modulusId) (hrm : rhsId ≠ modulusId)
    (st : BasisState)
    (hlayout :
      ({ lhs := (reg lhsId).wires
         rhs := (reg rhsId).wires
         out := (reg outId).wires
         work := mulWork modulusId start } : RegisterLayout).Valid)
    (hlhsBound : st⟦ᵣ(reg lhsId).wires⟧ < p)
    (hrhsBound : st⟦ᵣ(reg rhsId).wires⟧ < p)
    (hclean : clean((reg outId).wires ++ mulWork modulusId start, st)) :
    let after := ⟪mulProgram lhsId rhsId outId modulusId start⟫ st
    AgreesOn (reg lhsId).wires st after ∧
      AgreesOn (reg rhsId).wires st after ∧
      after⟦ᵣ(reg outId).wires⟧ =
        st⟦ᵣ(reg lhsId).wires⟧ * st⟦ᵣ(reg rhsId).wires⟧ % p ∧
      clean(mulWork modulusId start, after) := by
  exact (mul_contract lhsId rhsId outId modulusId start hlhs hrhs hmodulus
    hlr hlm hrm).correct st hlayout hlhsBound hrhsBound hclean

/-- Exact T-count for any placed low-space width-257 multiplier. -/
theorem mulProgram_tCount (lhsId rhsId outId modulusId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hmodulus : modulusId < start)
    (hlr : lhsId ≠ rhsId) (hlm : lhsId ≠ modulusId) (hrm : rhsId ≠ modulusId) :
    tCount (mulProgram lhsId rhsId outId modulusId start) = mulCost :=
  (mul_contract lhsId rhsId outId modulusId start hlhs hrhs hmodulus hlr hlm hrm).counted

def mulCall (lhsId rhsId outId accId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hacc : accId < start)
    (hlr : lhsId ≠ rhsId) (hla : lhsId ≠ accId) (hra : rhsId ≠ accId) :
    ModExp.MulCall fieldWidth p where
  ports := {
    lhs := reg lhsId
    rhs := reg rhsId
    out := reg outId
    work := mulWork accId start
  }
  program := mulProgram lhsId rhsId outId accId start
  cost := mulCost
  certified := mul_contract lhsId rhsId outId accId start hlhs hrhs hacc hlr hla hra

def historyCount : Nat → Nat
  | 0 => 0
  | 1 => 2
  | n + 2 => 3 + historyCount (n + 1)

def historyBlocks : Nat → Nat → List Block
  | _, 0 => []
  | start, 1 => [regBlock start, regBlock (start + 1)]
  | start, n + 2 =>
      [regBlock start, regBlock (start + 1), regBlock (start + 2)] ++
        historyBlocks (start + 3) (n + 1)

@[simp] theorem historyBlocks_ids (start bits : Nat) :
    (historyBlocks start bits).map Block.id = List.range' start (historyCount bits) := by
  induction bits using Nat.twoStepInduction generalizing start with
  | zero => simp [historyBlocks, historyCount]
  | one => simp [historyBlocks, historyCount, List.range']
  | more bits ih₀ ih₁ =>
      rw [historyBlocks, List.map_append, ih₁]
      change [start, start + 1, start + 2] ++
          List.range' (start + 3) (historyCount (bits + 1)) =
        List.range' start (3 + historyCount (bits + 1))
      rw [show [start, start + 1, start + 2] = List.range' start 3 by
        simp [List.range', Nat.add_assoc]]
      exact List.range'_append

structure BuiltSchedule (bits : List Wire) (accId powerId duplicateId mulAccId mulStart : Nat)
    where
  finalAcc : ModExp.Reg fieldWidth
  schedule : ModExp.Schedule fieldWidth p (mulWork mulAccId mulStart) (reg duplicateId)
    (reg accId) (reg powerId) bits finalAcc

def buildSchedule : (bits : List Wire) → (accId powerId historyStart duplicateId mulAccId
    mulStart : Nat) → accId < historyStart → powerId < historyStart →
    accId ≠ powerId → historyStart + historyCount bits.length ≤ duplicateId →
    duplicateId < mulAccId → mulAccId < mulStart →
    BuiltSchedule bits accId powerId duplicateId mulAccId mulStart
  | [], accId, powerId, _historyStart, duplicateId, mulAccId, mulStart,
      _hacc, _hpower, _hpa, _hbudget, _hdup, _hmul =>
      { finalAcc := reg accId
        schedule := .nil (reg accId) (reg powerId) }
  | [bit], accId, powerId, historyStart, duplicateId, mulAccId, mulStart,
      hacc, hpower, hpa, hbudget, hdup, hmul =>
      let productId := historyStart
      let nextAccId := historyStart + 1
      let accMul := mulCall powerId accId productId mulAccId mulStart
        (by omega) (by omega) hmul hpa.symm (by omega) (by omega)
      { finalAcc := reg nextAccId
        schedule := .last (reg accId) (reg powerId) bit (reg productId) (reg nextAccId)
          accMul rfl rfl rfl rfl }
  | bit :: nextBit :: bits, accId, powerId, historyStart, duplicateId, mulAccId,
      mulStart, hacc, hpower, hpa, hbudget, hdup, hmul =>
      let nextPowerId := historyStart
      let productId := historyStart + 1
      let nextAccId := historyStart + 2
      let accMul := mulCall powerId accId productId mulAccId mulStart
        (by omega) (by omega) hmul hpa.symm (by omega) (by omega)
      let squareMul := mulCall powerId duplicateId nextPowerId mulAccId mulStart
        (by omega) (by omega) hmul (by omega) (by omega) (by omega)
      let tail := buildSchedule (nextBit :: bits) nextAccId nextPowerId (historyStart + 3)
        duplicateId mulAccId mulStart (by omega) (by omega) (by omega)
        (by simp only [List.length_cons, historyCount] at hbudget ⊢; omega) hdup hmul
      { finalAcc := tail.finalAcc
        schedule := .cons (reg accId) (reg powerId) bit nextBit bits (reg nextPowerId)
          (reg productId) (reg nextAccId) tail.finalAcc accMul squareMul
          rfl rfl rfl rfl rfl rfl rfl rfl tail.schedule }

theorem buildSchedule_owned (bits : List Wire) (accId powerId historyStart duplicateId
    mulAccId mulStart : Nat) (hacc : accId < historyStart) (hpower : powerId < historyStart)
    (hpa : accId ≠ powerId) (hbudget : historyStart + historyCount bits.length ≤ duplicateId)
    (hdup : duplicateId < mulAccId) (hmul : mulAccId < mulStart) :
    (buildSchedule bits accId powerId historyStart duplicateId mulAccId mulStart hacc hpower
      hpa hbudget hdup hmul).schedule.owned =
      blocksWires (historyBlocks historyStart bits.length) := by
  induction bits using List.twoStepInduction generalizing accId powerId historyStart with
  | nil => simp [buildSchedule, ModExp.Schedule.owned, historyBlocks, blocksWires]
  | singleton bit =>
      simp [buildSchedule, ModExp.Schedule.owned, historyBlocks, blocksWires]
  | cons_cons bit nextBit bits ih₀ ih₁ =>
      simp only [buildSchedule, ModExp.Schedule.owned, List.length_cons, historyBlocks]
      rw [ih₁]
      simp [blocksWires, List.append_assoc]

theorem buildSchedule_uniform (bits : List Wire) (accId powerId historyStart duplicateId
    mulAccId mulStart : Nat) (hacc : accId < historyStart) (hpower : powerId < historyStart)
    (hpa : accId ≠ powerId) (hbudget : historyStart + historyCount bits.length ≤ duplicateId)
    (hdup : duplicateId < mulAccId) (hmul : mulAccId < mulStart) :
    (buildSchedule bits accId powerId historyStart duplicateId mulAccId mulStart hacc hpower
      hpa hbudget hdup hmul).schedule.UniformMulCost mulCost := by
  induction bits using List.twoStepInduction generalizing accId powerId historyStart with
  | nil => simp [buildSchedule, ModExp.Schedule.UniformMulCost]
  | singleton bit => simp [buildSchedule, ModExp.Schedule.UniformMulCost, mulCall]
  | cons_cons bit nextBit bits ih₀ ih₁ =>
      simp only [buildSchedule, ModExp.Schedule.UniformMulCost]
      exact ⟨rfl, rfl, ih₁ _ _ _ _ _ _ _ _⟩

def mulWorkBlocks (mulAccId mulStart : Nat) : List Block :=
  [bitBlock (mulStart + 2), regBlock mulAccId, regBlock mulStart,
    bitBlock (mulStart + 1), bitBlock (mulStart + 3)]

@[simp] theorem mulWorkBlocks_ids (mulAccId mulStart : Nat) :
    (mulWorkBlocks mulAccId mulStart).map Block.id =
      [mulStart + 2, mulAccId, mulStart, mulStart + 1, mulStart + 3] := by
  simp [mulWorkBlocks]

theorem mulWork_eq_blocksWires (mulAccId mulStart : Nat) :
    mulWork mulAccId mulStart = blocksWires (mulWorkBlocks mulAccId mulStart) := by
  simp [mulWork, mulWorkBlocks, blocksWires, LowSpaceModMul.work,
    mulCarry, mulBranch, mulOverflow, List.append_assoc]

theorem append_mulWorkBlocks_ids_nodup (front : List Block) (mulAccId mulStart : Nat)
    (hfront : (front.map Block.id).Nodup)
    (hbefore : ∀ id ∈ front.map Block.id, id < mulAccId)
    (hmul : mulAccId < mulStart) :
    ((front ++ mulWorkBlocks mulAccId mulStart).map Block.id).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hfront, ?_, ?_⟩
  · simp [mulWorkBlocks, List.nodup_cons]
    omega
  · intro left hleft right hright
    have hleftBound := hbefore left hleft
    simp [mulWorkBlocks] at hright
    rcases hright with rfl | rfl | rfl | rfl | rfl <;> omega

def lastSupportBlocks (powerId accId historyStart mulAccId mulStart : Nat) : List Block :=
  [regBlock powerId, regBlock accId, regBlock historyStart,
    regBlock (historyStart + 1)] ++ mulWorkBlocks mulAccId mulStart

def consSupportBlocks (powerId accId historyStart duplicateId mulAccId mulStart : Nat) :
    List Block :=
  [regBlock powerId, regBlock accId, regBlock (historyStart + 1),
    regBlock (historyStart + 2), regBlock duplicateId, regBlock historyStart] ++
      mulWorkBlocks mulAccId mulStart

@[simp] theorem lastSupport_eq (flag : Wire) (powerId accId historyStart mulAccId mulStart : Nat) :
    ModExp.Schedule.lastSupport flag (reg powerId) (reg accId) (reg historyStart)
      (reg (historyStart + 1)) (mulWork mulAccId mulStart) =
      flag :: blocksWires (lastSupportBlocks powerId accId historyStart mulAccId mulStart) := by
  simp [ModExp.Schedule.lastSupport, lastSupportBlocks, mulWork_eq_blocksWires,
    blocksWires, List.append_assoc]

@[simp] theorem consSupport_eq (flag : Wire) (powerId accId historyStart duplicateId
    mulAccId mulStart : Nat) :
    ModExp.Schedule.consSupport flag (reg powerId) (reg accId) (reg (historyStart + 1))
      (reg (historyStart + 2)) (reg duplicateId) (reg historyStart)
      (mulWork mulAccId mulStart) =
      flag :: blocksWires
        (consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart) := by
  simp [ModExp.Schedule.consSupport, consSupportBlocks, mulWork_eq_blocksWires,
    blocksWires, List.append_assoc]

theorem lastSupportBlocks_ids_nodup (powerId accId historyStart duplicateId mulAccId
    mulStart : Nat) (hpower : powerId < historyStart) (hacc : accId < historyStart)
    (hpa : powerId ≠ accId) (hbudget : historyStart + 2 ≤ duplicateId)
    (hdup : duplicateId < mulAccId) (hmul : mulAccId < mulStart) :
    ((lastSupportBlocks powerId accId historyStart mulAccId mulStart).map Block.id).Nodup := by
  apply append_mulWorkBlocks_ids_nodup
  · simp [List.nodup_cons]
    omega
  · intro id hid
    simp at hid
    rcases hid with rfl | rfl | rfl | rfl <;> omega
  · exact hmul

theorem consSupportBlocks_ids_nodup (powerId accId historyStart duplicateId mulAccId
    mulStart : Nat) (hpower : powerId < historyStart) (hacc : accId < historyStart)
    (hpa : powerId ≠ accId) (hbudget : historyStart + 3 ≤ duplicateId)
    (hdup : duplicateId < mulAccId) (hmul : mulAccId < mulStart) :
    ((consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart).map
      Block.id).Nodup := by
  apply append_mulWorkBlocks_ids_nodup
  · simp [List.nodup_cons]
    omega
  · intro id hid
    simp at hid
    rcases hid with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact hmul

theorem exponent_not_mem_lastSupportIds (exponentId powerId accId historyStart duplicateId
    mulAccId mulStart : Nat) (hexp : exponentId < historyStart)
    (hep : exponentId ≠ powerId) (hea : exponentId ≠ accId)
    (hbudget : historyStart + 2 ≤ duplicateId) (hdup : duplicateId < mulAccId)
    (hmul : mulAccId < mulStart) :
    exponentId ∉ (lastSupportBlocks powerId accId historyStart mulAccId mulStart).map Block.id := by
  rw [lastSupportBlocks, List.map_append, List.mem_append, not_or]
  constructor
  · simp [hep, hea]
    omega
  · intro h
    simp [mulWorkBlocks] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

theorem exponent_not_mem_consSupportIds (exponentId powerId accId historyStart duplicateId
    mulAccId mulStart : Nat) (hexp : exponentId < historyStart)
    (hep : exponentId ≠ powerId) (hea : exponentId ≠ accId)
    (hbudget : historyStart + 3 ≤ duplicateId)
    (hdup : duplicateId < mulAccId) (hmul : mulAccId < mulStart) :
    exponentId ∉
      (consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart).map Block.id := by
  rw [consSupportBlocks, List.map_append, List.mem_append, not_or]
  constructor
  · simp [hep, hea]
    omega
  · intro h
    simp [mulWorkBlocks] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

theorem consSupport_tail_ids_nodup (powerId accId historyStart duplicateId mulAccId
    mulStart tailBits : Nat) (hpower : powerId < historyStart) (hacc : accId < historyStart)
    (hpa : powerId ≠ accId)
    (hbudget : historyStart + 3 + historyCount tailBits ≤ duplicateId)
    (hdup : duplicateId < mulAccId) (hmul : mulAccId < mulStart) :
    (((consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart) ++
      historyBlocks (historyStart + 3) tailBits).map Block.id).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨consSupportBlocks_ids_nodup powerId accId historyStart duplicateId mulAccId
    mulStart hpower hacc hpa (by omega) hdup hmul, ?_, ?_⟩
  · rw [historyBlocks_ids]
    exact List.nodup_range'
  · intro x hx y hy
    rw [historyBlocks_ids, List.mem_range'] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [consSupportBlocks, List.map_append, List.mem_append] at hx
    rcases hx with hx | hx
    · simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · simp [mulWorkBlocks] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega

theorem exponent_not_mem_historyBlocks (exponentId historyStart bits : Nat)
    (hexp : exponentId < historyStart) :
    exponentId ∉ (historyBlocks historyStart bits).map Block.id := by
  rw [historyBlocks_ids, List.mem_range']
  intro h
  obtain ⟨i, hi, heq⟩ := h
  omega

set_option maxRecDepth 10000 in
theorem buildSchedule_valid (exponentId : Nat) :
    ∀ (bits : List Wire) (accId powerId historyStart duplicateId mulAccId mulStart : Nat)
      (hacc : accId < historyStart) (hpower : powerId < historyStart)
      (hpa : accId ≠ powerId)
      (hbudget : historyStart + historyCount bits.length ≤ duplicateId)
      (hdup : duplicateId < mulAccId) (hmul : mulAccId < mulStart),
      bits.Nodup →
      (∀ bit ∈ bits, bit ∈ (reg exponentId).wires) →
      exponentId < historyStart → exponentId ≠ accId → exponentId ≠ powerId →
      (buildSchedule bits accId powerId historyStart duplicateId mulAccId mulStart hacc hpower
        hpa hbudget hdup hmul).schedule.Valid := by
  intro bits
  induction bits using List.twoStepInduction with
  | nil =>
      intro accId powerId historyStart duplicateId mulAccId mulStart hacc hpower hpa
        hbudget hdup hmul _ _ _ _ _
      simp [buildSchedule, ModExp.Schedule.Valid]
  | singleton flag =>
      intro accId powerId historyStart duplicateId mulAccId mulStart hacc hpower hpa
        hbudget hdup hmul hbits hmem hexp hea hep
      have hbudget₂ : historyStart + 2 ≤ duplicateId := by
        simpa [historyCount] using hbudget
      have hflagMem : flag ∈ (reg exponentId).wires :=
        hmem flag (by simp)
      have hids := lastSupportBlocks_ids_nodup powerId accId historyStart duplicateId
        mulAccId mulStart hpower hacc hpa.symm hbudget₂ hdup hmul
      have hexpFresh := exponent_not_mem_lastSupportIds exponentId powerId accId historyStart
        duplicateId mulAccId mulStart hexp hep hea hbudget₂ hdup hmul
      have hflagFresh : flag ∉
          blocksWires (lastSupportBlocks powerId accId historyStart mulAccId mulStart) :=
        not_mem_blocksWires_of_source (regBlock exponentId) _ flag hflagMem hexpFresh
      have hstage : (flag ::
          blocksWires (lastSupportBlocks powerId accId historyStart mulAccId mulStart)).Nodup :=
        List.nodup_cons.mpr ⟨hflagFresh, blocksWires_nodup _ hids⟩
      change (buildSchedule [flag] accId powerId historyStart duplicateId mulAccId mulStart
        hacc hpower hpa hbudget hdup hmul).schedule.Valid
      simp only [buildSchedule, ModExp.Schedule.Valid]
      rw [lastSupport_eq]
      exact hstage
  | cons_cons flag nextFlag bits ih₀ ih₁ =>
      intro accId powerId historyStart duplicateId mulAccId mulStart hacc hpower hpa
        hbudget hdup hmul hbits hmem hexp hea hep
      have htailNodup : (nextFlag :: bits).Nodup :=
        (List.nodup_cons.mp hbits).2
      have hflagTail : flag ∉ nextFlag :: bits :=
        (List.nodup_cons.mp hbits).1
      have hflagMem : flag ∈ (reg exponentId).wires :=
        hmem flag (List.mem_cons_self ..)
      have htailMem : ∀ bit ∈ nextFlag :: bits, bit ∈ (reg exponentId).wires := by
        intro bit hbit
        exact hmem bit (List.mem_cons_of_mem flag hbit)
      have hbudgetTail : historyStart + 3 + historyCount (bits.length + 1) ≤ duplicateId := by
        simp only [List.length_cons, historyCount] at hbudget
        omega
      have hids := consSupportBlocks_ids_nodup powerId accId historyStart duplicateId
        mulAccId mulStart hpower hacc hpa.symm (by omega) hdup hmul
      have hexpFresh := exponent_not_mem_consSupportIds exponentId powerId accId historyStart
        duplicateId mulAccId mulStart hexp hep hea (by omega) hdup hmul
      have hflagFresh : flag ∉ blocksWires
          (consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart) :=
        not_mem_blocksWires_of_source (regBlock exponentId) _ flag hflagMem hexpFresh
      have hstage : (flag :: blocksWires
          (consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart)).Nodup :=
        List.nodup_cons.mpr ⟨hflagFresh, blocksWires_nodup _ hids⟩
      let tail := buildSchedule (nextFlag :: bits) (historyStart + 2) historyStart
        (historyStart + 3) duplicateId mulAccId mulStart (by omega) (by omega) (by omega)
        (by simp only [List.length_cons] at hbudgetTail ⊢; exact hbudgetTail) hdup hmul
      have htailOwned : tail.schedule.owned =
          blocksWires (historyBlocks (historyStart + 3) (bits.length + 1)) := by
        simpa [tail] using buildSchedule_owned (nextFlag :: bits) (historyStart + 2)
          historyStart (historyStart + 3) duplicateId mulAccId mulStart (by omega)
          (by omega) (by omega)
          (by simp only [List.length_cons] at hbudgetTail ⊢; exact hbudgetTail) hdup hmul
      have hcombined := consSupport_tail_ids_nodup powerId accId historyStart duplicateId
        mulAccId mulStart (bits.length + 1) hpower hacc hpa.symm hbudgetTail hdup hmul
      have hcurrentTail := blocksWires_disjoint_of_ids
        (consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart)
        (historyBlocks (historyStart + 3) (bits.length + 1)) hcombined
      have hexpNotHistory := exponent_not_mem_historyBlocks exponentId (historyStart + 3)
        (bits.length + 1) (by omega)
      have hfuture : ModExp.Schedule.WireDisjoint
          (flag :: blocksWires
            (consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart))
          ((nextFlag :: bits) ++ tail.schedule.owned) := by
        intro x hx y hy
        rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · subst x
          rcases List.mem_append.mp hy with hy | hy
          · exact fun e => hflagTail (e ▸ hy)
          · rw [htailOwned] at hy
            exact fun e => not_mem_blocksWires_of_source (regBlock exponentId)
              (historyBlocks (historyStart + 3) (bits.length + 1)) flag hflagMem
              hexpNotHistory (e ▸ hy)
        · rcases List.mem_append.mp hy with hy | hy
          · have hyMem := htailMem y hy
            exact fun e => not_mem_blocksWires_of_source (regBlock exponentId)
              (consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart)
              y hyMem hexpFresh (e ▸ hx)
          · rw [htailOwned] at hy
            exact hcurrentTail x hx y hy
      have htailValid := ih₁ nextFlag (historyStart + 2) historyStart (historyStart + 3)
        duplicateId mulAccId mulStart (by omega) (by omega) (by omega)
        (by simpa only [List.length_cons] using hbudgetTail) hdup hmul
        htailNodup htailMem (by omega) (by omega) (by omega)
      change (buildSchedule (flag :: nextFlag :: bits) accId powerId historyStart
        duplicateId mulAccId mulStart hacc hpower hpa hbudget hdup hmul).schedule.Valid
      simp only [buildSchedule, ModExp.Schedule.Valid]
      refine ⟨?_, ?_, htailValid⟩
      · rw [consSupport_eq]
        exact hstage
      · rw [consSupport_eq]
        change ModExp.Schedule.WireDisjoint
          (flag :: blocksWires
            (consSupportBlocks powerId accId historyStart duplicateId mulAccId mulStart))
          ((nextFlag :: bits) ++ tail.schedule.owned)
        exact hfuture

def baseId : Nat := 0
def exponentId : Nat := 1
def outId : Nat := 2
def initialAccId : Nat := 3
def historyStartId : Nat := 4
def duplicateId : Nat := historyStartId + historyCount fieldWidth
def mulAccId : Nat := duplicateId + 1
def mulStartId : Nat := mulAccId + 1

/-- One fully instantiated width-257 modular-adder wiring.  The exponentiation schedule uses the
same relative seven-block allocation at every modular-addition call. -/
def secpAddWiring :
    ModAddWiring (reg baseId).wires (reg exponentId).wires (reg outId).wires
      (reg initialAccId).wires (reg (initialAccId + 1)).wires
      (reg (initialAccId + 2)).wires
      (bitWire (initialAccId + 3)) (reg (initialAccId + 4)).wires
      (bitWire (initialAccId + 5)) (reg (initialAccId + 6)).wires p :=
  add_wiring baseId exponentId outId initialAccId (by norm_num [baseId, initialAccId])
    (by norm_num [exponentId, initialAccId]) (by norm_num [outId, initialAccId])
    (by norm_num [baseId, exponentId])

def secpAddProgram : Circuit := addProgram baseId exponentId outId initialAccId

def secpAddLayout : RegisterLayout :=
  { lhs := (reg baseId).wires
    rhs := (reg exponentId).wires
    out := (reg outId).wires
    work := addWork initialAccId }

set_option maxRecDepth 10000 in
/-- Same-program contract for the fixed width-257 modular adder above. -/
theorem secp_modAdd_contract : ModAddContract secpAddProgram secpAddLayout p addCost := by
  simpa [secpAddProgram, secpAddLayout] using
    (add_contract baseId exponentId outId initialAccId
      (by norm_num [baseId, initialAccId])
      (by norm_num [exponentId, initialAccId])
      (by norm_num [outId, initialAccId])
      (by norm_num [baseId, exponentId]))

/-- Direct functional correctness of the fixed width-257 modular-addition program. -/
theorem secpAddProgram_correct (st : BasisState)
    (hlayout : secpAddLayout.Valid)
    (hlhsBound : st⟦ᵣsecpAddLayout.lhs⟧ < p)
    (hrhsBound : st⟦ᵣsecpAddLayout.rhs⟧ < p)
    (hclean : clean(secpAddLayout.out ++ secpAddLayout.work, st)) :
    let after := ⟪secpAddProgram⟫ st
    AgreesOn secpAddLayout.lhs st after ∧
      AgreesOn secpAddLayout.rhs st after ∧
      after⟦ᵣsecpAddLayout.out⟧ =
        (st⟦ᵣsecpAddLayout.lhs⟧ + st⟦ᵣsecpAddLayout.rhs⟧) % p ∧
      clean(secpAddLayout.work, after) := by
  exact secp_modAdd_contract.correct st hlayout hlhsBound hrhsBound hclean

/-- One fully instantiated width-257 low-space modular multiplier. -/
def secpMulProgram : Circuit :=
  mulProgram baseId exponentId outId initialAccId historyStartId

def secpMulLayout : RegisterLayout :=
  { lhs := (reg baseId).wires
    rhs := (reg exponentId).wires
    out := (reg outId).wires
    work := mulWork initialAccId historyStartId }

/-- The complete concrete multiplier layout is 771 public wires plus 517 reusable work wires. -/
theorem secpMulLayout_allWires_length : secpMulLayout.allWires.length = 1288 := by
  norm_num [secpMulLayout, RegisterLayout.allWires, mulWork, LowSpaceModMul.work,
    reg, regBlock, Block.wires, regHigh, bitWire, fieldWidth]

set_option maxRecDepth 10000 in
/-- Same-program contract for the fixed width-257 low-space multiplier above. -/
theorem secp_modMul_contract : ModMulContract secpMulProgram secpMulLayout p mulCost := by
  simpa [secpMulProgram, secpMulLayout] using
    (mul_contract baseId exponentId outId initialAccId historyStartId
      (by norm_num [baseId, historyStartId])
      (by norm_num [exponentId, historyStartId])
      (by norm_num [initialAccId, historyStartId])
      (by norm_num [baseId, exponentId])
      (by norm_num [baseId, initialAccId])
      (by norm_num [exponentId, initialAccId]))

/-- Direct functional correctness of the fixed width-257 modular-multiplication program. -/
theorem secpMulProgram_correct (st : BasisState)
    (hlayout : secpMulLayout.Valid)
    (hlhsBound : st⟦ᵣsecpMulLayout.lhs⟧ < p)
    (hrhsBound : st⟦ᵣsecpMulLayout.rhs⟧ < p)
    (hclean : clean(secpMulLayout.out ++ secpMulLayout.work, st)) :
    let after := ⟪secpMulProgram⟫ st
    AgreesOn secpMulLayout.lhs st after ∧
      AgreesOn secpMulLayout.rhs st after ∧
      after⟦ᵣsecpMulLayout.out⟧ =
        st⟦ᵣsecpMulLayout.lhs⟧ * st⟦ᵣsecpMulLayout.rhs⟧ % p ∧
      clean(secpMulLayout.work, after) := by
  exact secp_modMul_contract.correct st hlayout hlhsBound hrhsBound hclean

private theorem initial_budget :
    historyStartId + historyCount (reg exponentId).wires.length ≤ duplicateId := by
  rw [(reg exponentId).length_eq]
  rfl

def secpSchedule : BuiltSchedule (reg exponentId).wires initialAccId baseId duplicateId
    mulAccId mulStartId :=
  buildSchedule (reg exponentId).wires initialAccId baseId historyStartId duplicateId
    mulAccId mulStartId (by norm_num [initialAccId, historyStartId])
    (by norm_num [baseId, historyStartId]) (by norm_num [initialAccId, baseId])
    initial_budget (by simp [mulAccId]) (by simp [mulStartId])

theorem secpSchedule_owned : secpSchedule.schedule.owned =
    blocksWires (historyBlocks historyStartId fieldWidth) := by
  have h := buildSchedule_owned (reg exponentId).wires initialAccId baseId historyStartId
    duplicateId mulAccId mulStartId (by norm_num [initialAccId, historyStartId])
    (by norm_num [baseId, historyStartId]) (by norm_num [initialAccId, baseId])
    initial_budget (by simp [mulAccId]) (by simp [mulStartId])
  rw [(reg exponentId).length_eq] at h
  exact h

set_option maxRecDepth 10000 in
theorem secpSchedule_valid : secpSchedule.schedule.Valid := by
  apply buildSchedule_valid exponentId (reg exponentId).wires initialAccId baseId historyStartId
    duplicateId mulAccId mulStartId (by norm_num [initialAccId, historyStartId])
    (by norm_num [baseId, historyStartId]) (by norm_num [initialAccId, baseId])
    initial_budget (by simp [mulAccId]) (by simp [mulStartId])
  · exact (regBlock exponentId).wires_nodup
  · intro bit hbit
    exact hbit
  · norm_num [exponentId, historyStartId]
  · norm_num [exponentId, initialAccId]
  · norm_num [exponentId, baseId]

set_option maxRecDepth 10000 in
theorem secpSchedule_uniform : secpSchedule.schedule.UniformMulCost mulCost := by
  exact buildSchedule_uniform (reg exponentId).wires initialAccId baseId historyStartId
    duplicateId mulAccId mulStartId (by norm_num [initialAccId, historyStartId])
    (by norm_num [baseId, historyStartId]) (by norm_num [initialAccId, baseId])
    initial_budget (by simp [mulAccId]) (by simp [mulStartId])

theorem p_large : 1 < p := by norm_num [p]

set_option maxRecDepth 10000 in
def secpPlan : ModExp.Plan fieldWidth p where
  base := reg baseId
  exponent := reg exponentId
  out := reg outId
  initialAcc := reg initialAccId
  finalAcc := secpSchedule.finalAcc
  mulWork := mulWork mulAccId mulStartId
  duplicate := reg duplicateId
  schedule := secpSchedule.schedule
  valid := secpSchedule_valid
  widthPos := by norm_num [fieldWidth]
  modulusLarge := p_large

def secpLayoutBlocks : List Block :=
  [regBlock baseId, regBlock exponentId, regBlock outId, regBlock initialAccId] ++
    historyBlocks historyStartId fieldWidth ++ [regBlock duplicateId] ++
    mulWorkBlocks mulAccId mulStartId

set_option maxRecDepth 10000 in
private theorem secpLayoutFrontBlocks_ids :
    (([regBlock baseId, regBlock exponentId, regBlock outId, regBlock initialAccId] ++
      historyBlocks historyStartId fieldWidth ++ [regBlock duplicateId]).map Block.id) =
      List.range' 0 mulAccId := by
  let history := historyCount fieldWidth
  rw [List.map_append, List.map_append, historyBlocks_ids]
  simp only [List.map_cons, List.map_nil, regBlock_id]
  unfold baseId exponentId outId initialAccId historyStartId duplicateId mulAccId
  change
    [0, 1, 2, 3] ++ List.range' 4 history ++ [4 + history] =
      List.range' 0 (4 + history + 1)
  have hprefix : [0, 1, 2, 3] = List.range' 0 4 := by decide
  rw [hprefix]
  rw [show [4 + history] = List.range' (4 + history) 1 by simp [List.range']]
  rw [List.range'_append]
  exact List.range'_append

theorem secpLayoutBlocks_ids_nodup : (secpLayoutBlocks.map Block.id).Nodup := by
  unfold secpLayoutBlocks
  apply append_mulWorkBlocks_ids_nodup
  · rw [secpLayoutFrontBlocks_ids]
    exact List.nodup_range'
  · intro id hid
    rw [secpLayoutFrontBlocks_ids, List.mem_range'] at hid
    omega
  · exact (by simp [mulAccId, mulStartId] : mulAccId < mulStartId)

theorem secpPlan_allWires : secpPlan.layout.allWires = blocksWires secpLayoutBlocks := by
  have howned := secpSchedule_owned
  simp only [ModExp.Plan.layout, RegisterLayout.allWires, secpPlan]
  rw [howned, mulWork_eq_blocksWires]
  simp [secpLayoutBlocks, blocksWires, List.append_assoc]

theorem secpPlan_layout_valid : secpPlan.layout.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · exact (reg baseId).length_eq.trans (reg exponentId).length_eq.symm
  · exact (reg baseId).length_eq.trans (reg outId).length_eq.symm
  · rw [secpPlan_allWires]
    exact blocksWires_nodup _ secpLayoutBlocks_ids_nodup

def secpCost : Nat :=
  2 * ((2 * fieldWidth - 1) * mulCost + 7 * fieldWidth * fieldWidth)

def secpProgram : Circuit := secpPlan.program

def secpLayout : RegisterLayout := secpPlan.layout

set_option maxRecDepth 10000 in
theorem secp_modExp_contract : ModExpContract secpProgram secpLayout p secpCost := by
  exact ModExp.Plan.modExp_contract_uniform secpPlan secpSchedule_uniform

/-- Direct functional correctness of the concrete secp256k1-field exponentiation program. -/
theorem secpProgram_correct (st : BasisState)
    (hlayout : secpLayout.Valid)
    (hbaseBound : st⟦ᵣsecpLayout.lhs⟧ < p)
    (hexponentBound : st⟦ᵣsecpLayout.rhs⟧ < p)
    (hclean : clean(secpLayout.out ++ secpLayout.work, st)) :
    let after := ⟪secpProgram⟫ st
    AgreesOn secpLayout.lhs st after ∧
      AgreesOn secpLayout.rhs st after ∧
      after⟦ᵣsecpLayout.out⟧ =
        st⟦ᵣsecpLayout.lhs⟧ ^ st⟦ᵣsecpLayout.rhs⟧ % p ∧
      clean(secpLayout.work, after) := by
  exact secp_modExp_contract.correct st hlayout hbaseBound hexponentBound hclean

/-- The instantiated 257-bit modular adder has this exact Clifford+T cost. -/
theorem addCost_eq : addCost = 23387 := by
  norm_num [addCost, fieldWidth]

/-- The instantiated 257-bit low-space multiplier has this exact Clifford+T cost. -/
theorem mulCost_eq : mulCost = 10171546 := by
  norm_num [mulCost, fieldWidth]

/-- Exact numeric T-count for the fixed width-257 modular-addition program. -/
theorem secpAddProgram_tCount : tCount secpAddProgram = 23387 := by
  rw [secp_modAdd_contract.counted]
  exact addCost_eq

/-- Exact numeric T-count for the fixed width-257 modular-multiplication program. -/
theorem secpMulProgram_tCount : tCount secpMulProgram = 10171546 := by
  rw [secp_modMul_contract.counted]
  exact mulCost_eq

set_option maxRecDepth 10000 in
/-- The fixed 257-bit exponent schedule stores 770 intermediate field registers. -/
theorem historyCount_eq : historyCount fieldWidth = 770 := by
  norm_num [historyCount, fieldWidth]

/-- The instantiated 257-bit modular exponentiator has this exact Clifford+T cost. -/
theorem secpCost_eq : secpCost = 10436930882 := by
  norm_num [secpCost, mulCost, fieldWidth]

/-- Exact numeric T-count for the concrete secp256k1-field exponentiation program. -/
theorem secpProgram_tCount : tCount secpProgram = 10436930882 := by
  rw [secp_modExp_contract.counted]
  exact secpCost_eq

set_option maxRecDepth 10000 in
/-- The exact instantiated exponentiation circuit computes inversion in the secp256k1 base
field when its preserved exponent register contains `p - 2`.  This is a direct specialization of
`FermatInv.correct`; it introduces no second circuit and no new field-theory argument. -/
theorem secp_fermat_inverse [Fact (Nat.Prime p)] (st : BasisState)
    (hbase : st⟦ᵣsecpLayout.lhs⟧ < p)
    (hexponent : st⟦ᵣsecpLayout.rhs⟧ = p - 2)
    (hclean : clean(secpLayout.out ++ secpLayout.work, st))
    (hnonzero : ((st⟦ᵣsecpLayout.lhs⟧ : Nat) : Fp) ≠ 0) :
    let after := run secpProgram st
    AgreesOn secpLayout.lhs st after ∧
      AgreesOn secpLayout.rhs st after ∧
      ((after⟦ᵣsecpLayout.out⟧ : Nat) : Fp) =
        ((st⟦ᵣsecpLayout.lhs⟧ : Nat) : Fp)⁻¹ ∧
      clean(secpLayout.work, after) := by
  exact FermatInv.correct secp_modExp_contract st secpPlan_layout_valid hbase hexponent hclean
    hnonzero

end Secp256k1Instance

end ShorECDLP
