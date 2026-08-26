import ShorECDLP.Submission.Arithmetic.ModAdd
import ShorECDLP.Submission.Arithmetic.ModMul
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

mulPlan bits power acc scratch
  := for each multiplier bit:
       duplicate power; add power+power; mask by bit; add mask+acc

secpProgram
  := Bennett-clean square-and-multiply over all 257 exponent bits,
     using the concrete multiplier plan above and one shared multiplier workspace
```

Wire allocation uses numbered blocks of capacity 257.  Every register occupies a complete block;
one-bit carry registers occupy a one-wire block.  Distinct block identifiers imply disjoint wire
ranges.  The fixed exponentiation layout uses one contiguous block-ID interval, while its schedule
owns 770 history registers and reuses the same 257-stage multiplier workspace at every call.

## Specification

`add_wiring`, `mul_contract`, and `secp_modExp_contract` certify the exact programs above against
the existing `ModAddWiring`, `ModMulContract`, and `ModExpContract` interfaces.  Their instantiated
costs are respectively `23,387`, `24,966,522`, and `25,616,576,258` T gates.  Finally,
`secp_fermat_inverse` specializes `FermatInv.correct` to this same `secpProgram`; it introduces no
second circuit or independent inversion claim.
-/

namespace ShorECDLP
namespace Secp256k1Instance

open Classical

theorem wiresOK_of_footprint_nodup :
    ∀ (cols : List (Wire × Wire × Wire)) (cin : Wire) (couts : List Wire),
      couts.length = cols.length →
      (ShorECDLP.ModAddSupport.rippleFootprint cols cin couts).Nodup →
      wiresOK cols cin couts := by
  intro cols
  induction cols with
  | nil =>
      intro cin couts hlen _
      obtain rfl : couts = [] := List.length_eq_zero_iff.mp hlen
      trivial
  | cons head rest ih =>
      intro cin couts hlen hnd
      obtain ⟨a, b, s⟩ := head
      cases couts with
      | nil => simp at hlen
      | cons co cs =>
          have hlen' : cs.length = rest.length := by simpa using hlen
          simp only [ShorECDLP.ModAddSupport.rippleFootprint,
            ShorECDLP.ModAddSupport.colsWires,
            List.flatMap_cons] at hnd
          have hrecursive :
              (ModAddSupport.rippleFootprint rest co cs).Nodup := by
            let flat := rest.flatMap (fun c => [c.1, c.2.1, c.2.2])
            have hsub : (co :: cs ++ flat).Sublist
                (cin :: (co :: cs ++ ([a, b, s] ++ flat))) := by
              apply List.Sublist.cons cin
              have h := List.Sublist.append (List.Sublist.refl (co :: cs))
                (List.sublist_append_right [a, b, s] flat)
              simpa [List.append_assoc] using h
            apply List.Nodup.sublist hsub
            simpa [flat, List.append_assoc] using hnd
          have hrest := ih co cs hlen' hrecursive
          let flat := rest.flatMap (fun c => [c.1, c.2.1, c.2.2])
          have hshape :
              (cin :: co :: (cs ++ ([a, b, s] ++ flat))).Nodup := by
            simpa [flat, List.append_assoc] using hnd
          obtain ⟨hcin, hafterCin⟩ := List.nodup_cons.mp hshape
          obtain ⟨hco, hafterCo⟩ := List.nodup_cons.mp hafterCin
          obtain ⟨hcs, htripleFlat, hcsTripleFlat⟩ :=
            List.nodup_append.mp hafterCo
          obtain ⟨htriple, hflat, htripleFlatCross⟩ :=
            List.nodup_append.mp htripleFlat
          have htriple' : a ≠ b ∧ a ≠ s ∧ b ≠ s := by
            obtain ⟨ha, habs⟩ := List.nodup_cons.mp htriple
            obtain ⟨hb, _⟩ := List.nodup_cons.mp habs
            exact ⟨fun e => ha (by simp [e]), fun e => ha (by simp [e]),
              fun e => hb (by simp [e])⟩
          simp only [wiresOK]
          refine ⟨?_, ?_, ?_, hrest⟩
          · -- The five local wires are distinct because all occur once in the footprint.
            refine ⟨htriple'.1, ?_, htriple'.2.1, ?_, ?_, htriple'.2.2, ?_, ?_, ?_, ?_⟩
            · intro e; apply hcin; simp [e]
            · intro e; apply hco; simp [e]
            · intro e; apply hcin; simp [e]
            · intro e; apply hco; simp [e]
            · intro e; apply hcin; simp [e]
            · intro e; apply hcin; simp [e]
            · intro e; apply hco; simp [e]
          · intro c hc
            have hcmem : c.1 ∈ flat ∧ c.2.1 ∈ flat ∧ c.2.2 ∈ flat := by
              simp only [flat, List.mem_flatMap]
              exact ⟨⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩⟩
            exact ⟨⟨htripleFlatCross s (by simp) c.1 hcmem.1,
              fun e => hco (by simp [e, hcmem.1])⟩,
              ⟨htripleFlatCross s (by simp) c.2.1 hcmem.2.1,
                fun e => hco (by simp [e, hcmem.2.1])⟩,
              ⟨htripleFlatCross s (by simp) c.2.2 hcmem.2.2,
                fun e => hco (by simp [e, hcmem.2.2])⟩⟩
          · intro x hx
            exact ⟨fun e => hcsTripleFlat x hx s (by simp) e.symm,
              fun e => hco (by simp [hx, e])⟩

theorem triple_interleave_perm {a b s : Wire} (as bs ss : List Wire) :
    ([a, b, s] ++ (as ++ bs ++ ss)).Perm
      ((a :: as) ++ (b :: bs) ++ (s :: ss)) := by
  have p₁ := (List.perm_append_comm (l₁ := [b, s]) (l₂ := as)).append_right (bs ++ ss)
  have p₂ := (List.perm_append_comm (l₁ := [s]) (l₂ := bs)).append_right ss
  have p₂' := p₂.append_left (as ++ [b])
  have p₂'' : (as ++ [b, s] ++ (bs ++ ss)).Perm
      (as ++ [b] ++ (bs ++ [s] ++ ss)) := by
    simpa [List.append_assoc] using p₂'
  simpa [List.append_assoc] using (p₁.trans p₂'').cons a

theorem selectorColumns_colsWires_perm :
    ∀ (as bs ss : List Wire), as.length = bs.length → as.length = ss.length →
      (ModAddSupport.colsWires (ModExp.selectorColumns as bs ss)).Perm (as ++ bs ++ ss) := by
  intro as
  induction as with
  | nil =>
      intro bs ss hab has
      obtain rfl : bs = [] := List.length_eq_zero_iff.mp hab.symm
      obtain rfl : ss = [] := List.length_eq_zero_iff.mp has.symm
      simp [ModExp.selectorColumns, ModAddSupport.colsWires]
  | cons a as ih =>
      intro bs ss hab has
      cases bs with
      | nil => simp at hab
      | cons b bs =>
          cases ss with
          | nil => simp at has
          | cons s ss =>
              have hab' : as.length = bs.length := by simpa using hab
              have has' : as.length = ss.length := by simpa using has
              have htail := ih bs ss hab' has'
              have hfront := htail.append_left [a, b, s]
              exact hfront.trans (triple_interleave_perm as bs ss)

theorem wiresOK_selectorColumns_of_nodup (as bs ss : List Wire) (cin : Wire)
    (couts : List Wire) (hab : as.length = bs.length) (has : as.length = ss.length)
    (hcout : couts.length = as.length)
    (hnd : (as ++ bs ++ ss ++ [cin] ++ couts).Nodup) :
    wiresOK (ModExp.selectorColumns as bs ss) cin couts := by
  apply wiresOK_of_footprint_nodup
  · calc
      couts.length = as.length := hcout
      _ = (ModExp.selectorColumns as bs ss).length := by
        have hm := congrArg List.length
          (ModExp.selectorColumns_maps as bs ss hab has).1
        simpa using hm.symm
  · have hcols := selectorColumns_colsWires_perm as bs ss hab has
    have hfront := List.perm_append_comm (l₁ := cin :: couts)
      (l₂ := ModAddSupport.colsWires (ModExp.selectorColumns as bs ss))
    have hback := hcols.append_right (cin :: couts)
    apply (hfront.trans hback).symm.nodup
    simpa [ModAddSupport.rippleFootprint, List.append_assoc] using hnd

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

def regBlock (id : Nat) : Block := ⟨id, fieldWidth, le_rfl⟩

def bitBlock (id : Nat) : Block := ⟨id, 1, by simp [fieldWidth]⟩

@[simp] theorem regBlock_id (id : Nat) : (regBlock id).id = id := rfl
@[simp] theorem bitBlock_id (id : Nat) : (bitBlock id).id = id := rfl

def blocksWires (blocks : List Block) : List Wire := blocks.flatMap Block.wires

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

def reg (id : Nat) : ModExp.Reg fieldWidth where
  wires := (regBlock id).wires
  length_eq := by simp [regBlock, fieldWidth]

def bitWire (id : Nat) : Wire := fieldWidth * id

@[simp] theorem bitBlock_wires (id : Nat) : (bitBlock id).wires = [bitWire id] := by
  simp [Block.wires, bitBlock, bitWire]

@[simp] theorem reg_wires (id : Nat) : (reg id).wires = (regBlock id).wires := rfl

def addCols (lhsId rhsId start : Nat) : List (Wire × Wire × Wire) :=
  (reg lhsId).selectorColumns (reg rhsId) (reg start)

def redCols (start : Nat) : List (Wire × Wire × Wire) :=
  (reg start).selectorColumns (reg (start + 1)) (reg (start + 2))

def selectCols (outId start : Nat) : List (Wire × Wire × Wire) :=
  (reg start).selectorColumns (reg (start + 2)) (reg outId)

def addScratchBlocks (start : Nat) : List Block :=
  [regBlock start, regBlock (start + 1), regBlock (start + 2), bitBlock (start + 3),
    regBlock (start + 4), bitBlock (start + 5), regBlock (start + 6)]

def addWork (start : Nat) : List Wire := blocksWires (addScratchBlocks start)

def addProgram (lhsId rhsId outId start : Nat) : Circuit :=
  modAdd (addCols lhsId rhsId start) (redCols start) (selectCols outId start)
    (bitWire (start + 3)) (reg (start + 4)).wires
    (bitWire (start + 5)) (reg (start + 6)).wires p

def addCost : Nat := 91 * fieldWidth

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
      (modAddLayout (addCols lhsId rhsId start) (redCols start) (selectCols outId start)
        (bitWire (start + 3)) (reg (start + 4)).wires
        (bitWire (start + 5)) (reg (start + 6)).wires).work := by
  have hadd := (reg lhsId).selectorColumns_maps (reg rhsId) (reg start)
  have hred := (reg start).selectorColumns_maps (reg (start + 1)) (reg (start + 2))
  simp [addWork, addScratchBlocks, blocksWires, modAddLayout, addCols, redCols,
    selectCols, hadd.2.2, hred.2.1, hred.2.2, bitBlock_wires, List.append_assoc]

set_option maxRecDepth 10000 in
theorem add_wiring (lhsId rhsId outId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hout : outId < start)
    (hlr : lhsId ≠ rhsId) :
    ModAddWiring (addCols lhsId rhsId start) (redCols start) (selectCols outId start)
      (bitWire (start + 3)) (reg (start + 4)).wires
      (bitWire (start + 5)) (reg (start + 6)).wires p := by
  let add := addCols lhsId rhsId start
  let red := redCols start
  let select := selectCols outId start
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
  have haddMaps := (reg lhsId).selectorColumns_maps (reg rhsId) (reg start)
  have hredMaps := (reg start).selectorColumns_maps (reg (start + 1)) (reg (start + 2))
  have hselectMaps := (reg start).selectorColumns_maps (reg (start + 2)) (reg outId)
  have wiring : ModAddWiring add red select cin₁ couts₁ cin₂ couts₂ p := by
    refine {
      addLen := by
        change (reg (start + 4)).wires.length =
          ((reg lhsId).selectorColumns (reg rhsId) (reg start)).length
        rw [(reg (start + 4)).length_eq,
          (reg lhsId).selectorColumns_length (reg rhsId) (reg start)]
      redLen := by
        change (reg (start + 6)).wires.length =
          ((reg start).selectorColumns (reg (start + 1)) (reg (start + 2))).length
        rw [(reg (start + 6)).length_eq,
          (reg start).selectorColumns_length (reg (start + 1)) (reg (start + 2))]
      width := by
        change ((reg start).selectorColumns (reg (start + 1)) (reg (start + 2))).length =
          ((reg lhsId).selectorColumns (reg rhsId) (reg start)).length
        rw [(reg start).selectorColumns_length (reg (start + 1)) (reg (start + 2)),
          (reg lhsId).selectorColumns_length (reg rhsId) (reg start)]
      selectLen := by
        change ((reg start).selectorColumns (reg (start + 2)) (reg outId)).length =
          ((reg lhsId).selectorColumns (reg rhsId) (reg start)).length
        rw [(reg start).selectorColumns_length (reg (start + 2)) (reg outId),
          (reg lhsId).selectorColumns_length (reg rhsId) (reg start)]
      addOK := ?_
      redOK := ?_
      selectOK := ?_
      redA := ?_
      selectX := ?_
      selectY := ?_
      modulusPos := p_pos
      fit := by
        change 2 * p ≤
          2 ^ ((reg lhsId).selectorColumns (reg rhsId) (reg start)).length
        rw [(reg lhsId).selectorColumns_length (reg rhsId) (reg start)]
        exact p_fits
    }
    · change wiresOK ((reg lhsId).selectorColumns (reg rhsId) (reg start)) cin₁ couts₁
      apply wiresOK_selectorColumns_of_nodup
      · exact (reg lhsId).length_eq.trans (reg rhsId).length_eq.symm
      · exact (reg lhsId).length_eq.trans (reg start).length_eq.symm
      · exact (reg (start + 4)).length_eq.trans (reg lhsId).length_eq.symm
      · exact hAddNodup
    · change wiresOK ((reg start).selectorColumns (reg (start + 1)) (reg (start + 2)))
        cin₂ couts₂
      apply wiresOK_selectorColumns_of_nodup
      · exact (reg start).length_eq.trans (reg (start + 1)).length_eq.symm
      · exact (reg start).length_eq.trans (reg (start + 2)).length_eq.symm
      · exact (reg (start + 6)).length_eq.trans (reg start).length_eq.symm
      · exact hRedNodup
    · change selectOK (carryOut cin₂ couts₂)
        ((reg start).selectorColumns (reg (start + 2)) (reg outId))
      exact ModExp.selectOK_of_nodup _ _ _ _ hselectNodup
    · dsimp only [red, add, redCols, addCols]
      exact hredMaps.1.trans haddMaps.2.2.symm
    · dsimp only [select, add, selectCols, addCols]
      exact hselectMaps.1.trans haddMaps.2.2.symm
    · dsimp only [select, red, selectCols, redCols]
      exact hselectMaps.2.1.trans hredMaps.2.2.symm
  simpa [add, red, select, cin₁, couts₁, cin₂, couts₂] using wiring

set_option maxRecDepth 10000 in
theorem add_contract (lhsId rhsId outId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hout : outId < start)
    (hlr : lhsId ≠ rhsId) :
    ModAddContract (addProgram lhsId rhsId outId start)
      { lhs := (reg lhsId).wires, rhs := (reg rhsId).wires,
        out := (reg outId).wires, work := addWork start }
      p addCost := by
  have hcontract := modAdd_contract (addCols lhsId rhsId start) (redCols start)
    (selectCols outId start) (bitWire (start + 3)) (reg (start + 4)).wires
    (bitWire (start + 5)) (reg (start + 6)).wires p
    (add_wiring lhsId rhsId outId start hlhs hrhs hout hlr)
  simpa [addProgram, addCost, addWork_eq_layoutWork lhsId rhsId outId start] using hcontract

def mulStageBlocks (start : Nat) : List Block :=
  [regBlock start, regBlock (start + 1)] ++ addScratchBlocks (start + 2) ++
    [regBlock (start + 9), regBlock (start + 10)] ++ addScratchBlocks (start + 11)

def mulPrivateBlocks : Nat → Nat → List Block
  | _, 0 => []
  | start, steps + 1 => mulStageBlocks start ++ mulPrivateBlocks (start + 18) steps

def mulPlan : (controls : List Wire) → (powerId accId start : Nat) →
    powerId < start → accId < start →
    ModMul.Plan p addCost controls (reg powerId).wires (reg accId).wires
  | [], powerId, accId, _start, _hpower, _hacc => .done (reg powerId).wires (reg accId).wires
  | control :: controls, powerId, accId, start, hpower, hacc =>
      .step (reg start).wires (reg (start + 1)).wires (reg (start + 9)).wires
        (reg (start + 10)).wires (addWork (start + 2)) (addWork (start + 11))
        (addProgram powerId start (start + 1) (start + 2))
        (addProgram (start + 9) accId (start + 10) (start + 11))
        (add_contract powerId start (start + 1) (start + 2) (by omega) (by omega)
          (by omega) (by omega))
        (add_contract (start + 9) accId (start + 10) (start + 11) (by omega)
          (by omega) (by omega) (by omega))
        (mulPlan controls (start + 1) (start + 10) (start + 18) (by omega) (by omega))

@[simp] theorem mulStageBlocks_ids (start : Nat) :
    (mulStageBlocks start).map Block.id = List.range' start 18 := by
  simp [mulStageBlocks, addScratchBlocks, List.range', Nat.add_assoc]

@[simp] theorem mulPrivateBlocks_ids (start steps : Nat) :
    (mulPrivateBlocks start steps).map Block.id = List.range' start (18 * steps) := by
  induction steps generalizing start with
  | zero => simp [mulPrivateBlocks]
  | succ steps ih =>
      rw [mulPrivateBlocks, List.map_append, mulStageBlocks_ids, ih]
      rw [List.range'_append]
      congr 1
      simp [Nat.mul_succ, Nat.add_comm]

theorem mulPlan_privateWires (controls : List Wire) (powerId accId start : Nat)
    (hpower : powerId < start) (hacc : accId < start) :
    (mulPlan controls powerId accId start hpower hacc).privateWires =
      blocksWires (mulPrivateBlocks start controls.length) := by
  induction controls generalizing powerId accId start with
  | nil => simp [mulPlan, ModMul.Plan.privateWires, mulPrivateBlocks, blocksWires]
  | cons control controls ih =>
      simp only [mulPlan, ModMul.Plan.privateWires, List.length_cons, mulPrivateBlocks]
      rw [ih]
      simp [mulStageBlocks, addWork, blocksWires, List.append_assoc]

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

def mulStageSupportBlocks (powerId accId start : Nat) : List Block :=
  [regBlock powerId, regBlock start, regBlock (start + 1)] ++
    addScratchBlocks (start + 2) ++
    [regBlock (start + 9), regBlock accId, regBlock (start + 10)] ++
    addScratchBlocks (start + 11)

@[simp] theorem mulStageSupport_eq (control : Wire) (powerId accId start : Nat) :
    ModMul.Plan.stageSupport control (reg powerId).wires (reg start).wires
      (reg (start + 1)).wires (addWork (start + 2)) (reg (start + 9)).wires
      (reg accId).wires (reg (start + 10)).wires (addWork (start + 11)) =
      control :: blocksWires (mulStageSupportBlocks powerId accId start) := by
  simp [ModMul.Plan.stageSupport, mulStageSupportBlocks, addWork, blocksWires,
    List.append_assoc]

theorem mulStageSupportBlocks_ids_nodup (powerId accId start : Nat)
    (hpower : powerId < start) (hacc : accId < start) (hpa : powerId ≠ accId) :
    ((mulStageSupportBlocks powerId accId start).map Block.id).Nodup := by
  simp [mulStageSupportBlocks, addScratchBlocks, List.nodup_cons]
  omega

theorem mulStage_rest_ids_nodup (powerId accId start steps : Nat)
    (hpower : powerId < start) (hacc : accId < start) (hpa : powerId ≠ accId) :
    (((mulStageSupportBlocks powerId accId start) ++
      mulPrivateBlocks (start + 18) steps).map Block.id).Nodup := by
  rw [List.map_append, mulPrivateBlocks_ids, List.nodup_append]
  refine ⟨mulStageSupportBlocks_ids_nodup powerId accId start hpower hacc hpa,
    List.nodup_range', ?_⟩
  intro x hx y hy
  rw [List.mem_range'] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  simp [mulStageSupportBlocks, addScratchBlocks] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

set_option maxRecDepth 10000 in
theorem mulPlan_valid (rhsId : Nat) :
    ∀ (controls : List Wire) (powerId accId start : Nat)
      (hpower : powerId < start) (hacc : accId < start),
      controls.Nodup →
      (∀ control ∈ controls, control ∈ (reg rhsId).wires) →
      rhsId < start → rhsId ≠ powerId → rhsId ≠ accId → powerId ≠ accId →
      (mulPlan controls powerId accId start hpower hacc).Valid fieldWidth := by
  intro controls
  induction controls with
  | nil =>
      intro powerId accId start hpower hacc _ _ _ _ _ _
      simp [mulPlan, ModMul.Plan.Valid, reg, regBlock, fieldWidth]
  | cons control controls ih =>
      intro powerId accId start hpower hacc hcontrols hmem hrhs hrp hra hpa
      obtain ⟨hcontrolTail, htailNodup⟩ := List.nodup_cons.mp hcontrols
      have hcontrolMem : control ∈ (reg rhsId).wires :=
        hmem control (List.mem_cons_self ..)
      have htailMem : ∀ wire ∈ controls, wire ∈ (reg rhsId).wires := by
        intro wire hwire
        exact hmem wire (List.mem_cons_of_mem control hwire)
      have hstageIds := mulStageSupportBlocks_ids_nodup powerId accId start hpower hacc hpa
      have hrhsNotStage : rhsId ∉
          (mulStageSupportBlocks powerId accId start).map Block.id := by
        simp [mulStageSupportBlocks, addScratchBlocks]
        omega
      have hcontrolFresh : control ∉
          blocksWires (mulStageSupportBlocks powerId accId start) :=
        not_mem_blocksWires_of_source (regBlock rhsId)
          (mulStageSupportBlocks powerId accId start) control hcontrolMem hrhsNotStage
      have hstageNodup :
          (control :: blocksWires (mulStageSupportBlocks powerId accId start)).Nodup :=
        List.nodup_cons.mpr ⟨hcontrolFresh,
          blocksWires_nodup _ hstageIds⟩
      let rest := mulPlan controls (start + 1) (start + 10) (start + 18)
        (by omega) (by omega)
      have hrestPrivate : rest.privateWires =
          blocksWires (mulPrivateBlocks (start + 18) controls.length) := by
        simpa [rest] using mulPlan_privateWires controls (start + 1) (start + 10)
          (start + 18) (by omega) (by omega)
      have hrhsNotRest : rhsId ∉
          (mulPrivateBlocks (start + 18) controls.length).map Block.id := by
        rw [mulPrivateBlocks_ids, List.mem_range']
        intro h
        obtain ⟨i, hi, heq⟩ := h
        omega
      have hcurrentRest := blocksWires_disjoint_of_ids
        (mulStageSupportBlocks powerId accId start)
        (mulPrivateBlocks (start + 18) controls.length)
        (mulStage_rest_ids_nodup powerId accId start controls.length hpower hacc hpa)
      have hfuture : ModMul.Plan.WireDisjoint
          (control :: blocksWires (mulStageSupportBlocks powerId accId start))
          (controls ++ rest.privateWires) := by
        intro x hx y hy
        rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · subst x
          rcases List.mem_append.mp hy with hy | hy
          · exact fun e => hcontrolTail (e ▸ hy)
          · rw [hrestPrivate] at hy
            exact fun e => not_mem_blocksWires_of_source (regBlock rhsId)
              (mulPrivateBlocks (start + 18) controls.length) control hcontrolMem
              hrhsNotRest (e ▸ hy)
        · rcases List.mem_append.mp hy with hy | hy
          · have hyMem := htailMem y hy
            exact fun e => not_mem_blocksWires_of_source (regBlock rhsId)
              (mulStageSupportBlocks powerId accId start) y hyMem hrhsNotStage
              (e ▸ hx)
          · rw [hrestPrivate] at hy
            exact hcurrentRest x hx y hy
      have hrestValid := ih (start + 1) (start + 10) (start + 18)
        (by omega) (by omega) htailNodup htailMem (by omega) (by omega) (by omega)
        (by omega)
      change (mulPlan (control :: controls) powerId accId start hpower hacc).Valid fieldWidth
      simp only [mulPlan, ModMul.Plan.Valid]
      refine ⟨(reg powerId).length_eq, (reg accId).length_eq, (reg start).length_eq,
        (reg (start + 1)).length_eq, (reg (start + 9)).length_eq,
        (reg (start + 10)).length_eq, ?_, ?_, hrestValid⟩
      · rw [mulStageSupport_eq]
        exact hstageNodup
      · rw [mulStageSupport_eq]
        change ModMul.Plan.WireDisjoint
          (control :: blocksWires (mulStageSupportBlocks powerId accId start))
          (controls ++ rest.privateWires)
        exact hfuture

def placedMulPlan (lhsId rhsId accId start : Nat) (hlhs : lhsId < start)
    (hacc : accId < start) :
    ModMul.Plan p addCost (reg rhsId).wires (reg lhsId).wires (reg accId).wires :=
  mulPlan (reg rhsId).wires lhsId accId start hlhs hacc

def mulWork (accId start : Nat) : List Wire :=
  (reg accId).wires ++ blocksWires (mulPrivateBlocks start fieldWidth)

def mulCost : Nat := 2 * fieldWidth * (2 * addCost + 7 * fieldWidth)

theorem placedMulPlan_valid (lhsId rhsId accId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hacc : accId < start)
    (hlr : lhsId ≠ rhsId) (hla : lhsId ≠ accId) (hra : rhsId ≠ accId) :
    (placedMulPlan lhsId rhsId accId start hlhs hacc).Valid fieldWidth := by
  apply mulPlan_valid rhsId (reg rhsId).wires lhsId accId start hlhs hacc
  · exact (regBlock rhsId).wires_nodup
  · intro wire hwire
    exact hwire
  · exact hrhs
  · exact hlr.symm
  · exact hra
  · exact hla

set_option maxRecDepth 10000 in
theorem mul_contract (lhsId rhsId outId accId start : Nat)
    (hlhs : lhsId < start) (hrhs : rhsId < start) (hacc : accId < start)
    (hlr : lhsId ≠ rhsId) (hla : lhsId ≠ accId) (hra : rhsId ≠ accId) :
    let plan := placedMulPlan lhsId rhsId accId start hlhs hacc
    ModMulContract (plan.program (reg outId).wires)
      { lhs := (reg lhsId).wires, rhs := (reg rhsId).wires,
        out := (reg outId).wires, work := mulWork accId start }
      p mulCost := by
  let plan := placedMulPlan lhsId rhsId accId start hlhs hacc
  have hvalid : plan.Valid fieldWidth :=
    placedMulPlan_valid lhsId rhsId accId start hlhs hrhs hacc hlr hla hra
  have hcontract := ModMul.Plan.modMul_contract plan (reg outId).wires fieldWidth hvalid p_pos
  have hprivate := mulPlan_privateWires (reg rhsId).wires lhsId accId start hlhs hacc
  rw [(reg rhsId).length_eq] at hcontract
  rw [(reg rhsId).length_eq] at hprivate
  change ModMulContract (plan.program (reg outId).wires)
    { lhs := (reg lhsId).wires, rhs := (reg rhsId).wires,
      out := (reg outId).wires, work := mulWork accId start }
    p mulCost
  rw [mulWork, ← hprivate]
  change ModMulContract (plan.program (reg outId).wires)
    (plan.layout (reg outId).wires) p mulCost
  exact hcontract

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
  program := (placedMulPlan lhsId rhsId accId start hlhs hacc).program (reg outId).wires
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
  regBlock mulAccId :: mulPrivateBlocks mulStart fieldWidth

@[simp] theorem mulWorkBlocks_ids (mulAccId mulStart : Nat) :
    (mulWorkBlocks mulAccId mulStart).map Block.id =
      mulAccId :: List.range' mulStart (18 * fieldWidth) := by
  simp [mulWorkBlocks]

theorem mulWork_eq_blocksWires (mulAccId mulStart : Nat) :
    mulWork mulAccId mulStart = blocksWires (mulWorkBlocks mulAccId mulStart) := by
  simp [mulWork, mulWorkBlocks, blocksWires]

theorem append_mulWorkBlocks_ids_nodup (front : List Block) (mulAccId mulStart : Nat)
    (hfront : (front.map Block.id).Nodup)
    (hbefore : ∀ id ∈ front.map Block.id, id < mulAccId)
    (hmul : mulAccId < mulStart) :
    ((front ++ mulWorkBlocks mulAccId mulStart).map Block.id).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hfront, ?_, ?_⟩
  · rw [mulWorkBlocks_ids, List.nodup_cons]
    refine ⟨?_, List.nodup_range'⟩
    rw [List.mem_range']
    intro h
    obtain ⟨i, hi, heq⟩ := h
    omega
  · intro left hleft right hright
    have hleftBound := hbefore left hleft
    rw [mulWorkBlocks_ids, List.mem_cons] at hright
    rcases hright with rfl | hright
    · omega
    · rw [List.mem_range'] at hright
      obtain ⟨i, hi, rfl⟩ := hright
      omega

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
  · rw [mulWorkBlocks_ids, List.mem_cons]
    intro h
    rcases h with heq | h
    · omega
    · rw [List.mem_range'] at h
      obtain ⟨i, hi, heq⟩ := h
      omega

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
  · rw [mulWorkBlocks_ids, List.mem_cons]
    intro h
    rcases h with heq | h
    · omega
    · rw [List.mem_range'] at h
      obtain ⟨i, hi, heq⟩ := h
      omega

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
    · rw [mulWorkBlocks_ids, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · rw [List.mem_range'] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        omega

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
    ModAddWiring (addCols baseId exponentId initialAccId)
      (redCols initialAccId) (selectCols outId initialAccId)
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

/-- One fully instantiated width-257 schoolbook multiplication plan.  It is also the relative
plan used to build every certified multiplier call in `secpSchedule`. -/
def secpMulPlan :
    ModMul.Plan p addCost (reg exponentId).wires (reg baseId).wires
      (reg initialAccId).wires :=
  placedMulPlan baseId exponentId initialAccId historyStartId
    (by norm_num [baseId, historyStartId])
    (by norm_num [initialAccId, historyStartId])

def secpMulProgram : Circuit := secpMulPlan.program (reg outId).wires

def secpMulLayout : RegisterLayout :=
  { lhs := (reg baseId).wires
    rhs := (reg exponentId).wires
    out := (reg outId).wires
    work := mulWork initialAccId historyStartId }

set_option maxRecDepth 10000 in
/-- Validity of the fixed width-257 multiplication plan. -/
theorem secpMulPlan_valid : secpMulPlan.Valid fieldWidth := by
  exact placedMulPlan_valid baseId exponentId initialAccId historyStartId
    (by norm_num [baseId, historyStartId])
    (by norm_num [exponentId, historyStartId])
    (by norm_num [initialAccId, historyStartId])
    (by norm_num [baseId, exponentId])
    (by norm_num [baseId, initialAccId])
    (by norm_num [exponentId, initialAccId])

set_option maxRecDepth 10000 in
/-- Same-program contract for the fixed width-257 schoolbook multiplier above. -/
theorem secp_modMul_contract : ModMulContract secpMulProgram secpMulLayout p mulCost := by
  simpa [secpMulProgram, secpMulLayout, secpMulPlan] using
    (mul_contract baseId exponentId outId initialAccId historyStartId
      (by norm_num [baseId, historyStartId])
      (by norm_num [exponentId, historyStartId])
      (by norm_num [initialAccId, historyStartId])
      (by norm_num [baseId, exponentId])
      (by norm_num [baseId, initialAccId])
      (by norm_num [exponentId, initialAccId]))

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
theorem secpLayoutBlocks_ids : secpLayoutBlocks.map Block.id =
    List.range' 0 (mulStartId + 18 * fieldWidth) := by
  let history := historyCount fieldWidth
  let privateCount := 18 * fieldWidth
  unfold secpLayoutBlocks
  rw [List.map_append, List.map_append, List.map_append, historyBlocks_ids,
    mulWorkBlocks_ids]
  simp only [List.map_cons, List.map_nil, regBlock_id]
  unfold baseId exponentId outId initialAccId historyStartId duplicateId mulAccId mulStartId
  change
    [0, 1, 2, 3] ++ List.range' 4 history ++
        [4 + history] ++ ((4 + history + 1) :: List.range' (4 + history + 2) privateCount) =
      List.range' 0 (4 + history + 2 + privateCount)
  have hprefix : [0, 1, 2, 3] = List.range' 0 4 := by decide
  have htwo : [4 + history, 4 + history + 1] = List.range' (4 + history) 2 := by
    simp [List.range']
  have hpair : [4 + history] ++
      ((4 + history + 1) :: List.range' (4 + history + 2) privateCount) =
      [4 + history, 4 + history + 1] ++
        List.range' (4 + history + 2) privateCount := by simp
  rw [hprefix]
  simp only [List.append_assoc]
  rw [hpair, htwo]
  have htail : List.range' (4 + history) 2 ++
      List.range' (4 + history + 2) privateCount =
      List.range' (4 + history) (2 + privateCount) := by
    exact List.range'_append
  rw [htail]
  have hmid : List.range' 4 history ++
      List.range' (4 + history) (2 + privateCount) =
      List.range' 4 (history + (2 + privateCount)) := by
    exact List.range'_append
  rw [hmid]
  simpa [Nat.add_assoc] using
    (List.range'_append (s := 0) (m := 4) (n := history + (2 + privateCount))
      (step := 1))

theorem secpLayoutBlocks_ids_nodup : (secpLayoutBlocks.map Block.id).Nodup := by
  rw [secpLayoutBlocks_ids]
  exact List.nodup_range'

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

/-- The instantiated 257-bit modular adder has this exact Clifford+T cost. -/
theorem addCost_eq : addCost = 23387 := by
  norm_num [addCost, fieldWidth]

/-- The instantiated 257-bit schoolbook multiplier has this exact Clifford+T cost. -/
theorem mulCost_eq : mulCost = 24966522 := by
  norm_num [mulCost, addCost, fieldWidth]

/-- Exact numeric T-count for the fixed width-257 modular-addition program. -/
theorem secpAddProgram_tCount : tCount secpAddProgram = 23387 := by
  rw [secp_modAdd_contract.counted]
  exact addCost_eq

/-- Exact numeric T-count for the fixed width-257 modular-multiplication program. -/
theorem secpMulProgram_tCount : tCount secpMulProgram = 24966522 := by
  rw [secp_modMul_contract.counted]
  exact mulCost_eq

set_option maxRecDepth 10000 in
/-- The fixed 257-bit exponent schedule stores 770 intermediate field registers. -/
theorem historyCount_eq : historyCount fieldWidth = 770 := by
  norm_num [historyCount, fieldWidth]

/-- The instantiated 257-bit modular exponentiator has this exact Clifford+T cost. -/
theorem secpCost_eq : secpCost = 25616576258 := by
  norm_num [secpCost, mulCost, addCost, fieldWidth]

/-- Exact numeric T-count for the concrete secp256k1-field exponentiation program. -/
theorem secpProgram_tCount : tCount secpProgram = 25616576258 := by
  rw [secp_modExp_contract.counted]
  exact secpCost_eq

set_option maxRecDepth 10000 in
/-- The exact instantiated exponentiation circuit computes inversion in the secp256k1 base
field when its preserved exponent register contains `p - 2`.  This is a direct specialization of
`FermatInv.correct`; it introduces no second circuit and no new field-theory argument. -/
theorem secp_fermat_inverse [Fact (Nat.Prime p)] (st : BasisState)
    (hbase : regValue secpLayout.lhs st < p)
    (hexponent : regValue secpLayout.rhs st = p - 2)
    (hclean : Clean (secpLayout.out ++ secpLayout.work) st)
    (hnonzero : ((regValue secpLayout.lhs st : Nat) : Fp) ≠ 0) :
    let after := run secpProgram st
    AgreesOn secpLayout.lhs st after ∧
      AgreesOn secpLayout.rhs st after ∧
      ((regValue secpLayout.out after : Nat) : Fp) =
        ((regValue secpLayout.lhs st : Nat) : Fp)⁻¹ ∧
      Clean secpLayout.work after := by
  exact FermatInv.correct secp_modExp_contract st secpPlan_layout_valid hbase hexponent hclean
    hnonzero

end Secp256k1Instance

end ShorECDLP
