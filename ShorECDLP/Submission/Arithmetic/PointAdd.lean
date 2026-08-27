import ShorECDLP.Submission.EllipticCurve.AffineFormula
import ShorECDLP.Submission.EllipticCurve.PointRegister
import ShorECDLP.Submission.Arithmetic.ModSub
import ShorECDLP.Submission.Arithmetic.Predicates
import ShorECDLP.Submission.Arithmetic.Secp256k1Instance

namespace ShorECDLP
namespace Secp256k1

open Classical
open Arithmetic
open scoped ArithmeticNotation

/-!
# Clean addition of a classical secp256k1 point

This file constructs the reversible operation

    |R⟩ |0⟩ |0_work⟩
      ↦
    |R⟩ |R + C⟩ |0_work⟩

where

* `R` is a quantum secp256k1 point;
* `C` is a classical constant point;
* the input point is preserved;
* every scratch wire is restored.

For a finite constant `C = (x₂,y₂)`, the circuit implements the same
decision tree as `affineAdd`:

    R = O          -> C
    R = -C         -> O
    R = C          -> double R
    otherwise      -> generic affine addition

The generic affine formula is

    λ  = (y₁ - y₂) / (x₁ - x₂)
    x₃ = λ² - x₁ - x₂
    y₃ = λ(x₁ - x₃) - y₁

and doubling is

    λ  = 3x₁² / 2y₁
    x₃ = λ² - 2x₁
    y₃ = λ(x₁ - x₃) - y₁.

All field operations are built from the concrete width-257 arithmetic
already supplied by `Secp256k1Instance`.
-/

private def fieldWidth : Nat :=
  Secp256k1Instance.fieldWidth

/-! -------------------------------------------------------------------------
    Wire relabelling

`Secp256k1Instance` gives us one concrete field-arithmetic circuit whose
wires start at zero.  Point addition needs to place that arithmetic engine
inside a larger circuit, so we translate every arithmetic wire by a fixed
offset.

This does not introduce a new gate.  It simply renames the wires of the
already-defined circuit.
------------------------------------------------------------------------- -/

def shiftGate (offset : Wire) : Gate → Gate
  | .X t       => .X (offset + t)
  | .H t       => .H (offset + t)
  | .CX c t    => .CX (offset + c) (offset + t)
  | .CCX a b t => .CCX (offset + a) (offset + b) (offset + t)
  | .P dir k t => .P dir k (offset + t)

def shiftCircuit (offset : Wire) (c : Circuit) : Circuit :=
  c.map (shiftGate offset)

def shiftWires (offset : Wire) (ws : List Wire) : List Wire :=
  ws.map fun w => offset + w

private theorem shiftGate_isClassical
    (offset : Wire) (g : Gate)
    (h : Classical.IsClassicalGate g) :
    Classical.IsClassicalGate (shiftGate offset g) := by
  cases g <;> simp_all [shiftGate]

private theorem shiftCircuit_HPFree
    (offset : Wire) (c : Circuit)
    (h : Classical.HPFree c) :
    Classical.HPFree (shiftCircuit offset c) := by
  intro g hg
  simp only [shiftCircuit, List.mem_map] at hg
  obtain ⟨source, hsource, rfl⟩ := hg
  exact shiftGate_isClassical offset source (h source hsource)

private theorem shiftGate_wellFormed
    (offset : Wire) (g : Gate)
    (h : g.WellFormed) :
    (shiftGate offset g).WellFormed := by
  cases g with
  | X _ => trivial
  | H _ => trivial
  | CX _ _ =>
      simp only [Gate.WellFormed, shiftGate] at h ⊢
      intro heq
      exact h (Nat.add_left_cancel heq)
  | CCX _ _ _ =>
      simp only [Gate.WellFormed, shiftGate] at h ⊢
      exact
        ⟨fun heq => h.1 (Nat.add_left_cancel heq),
          fun heq => h.2.1 (Nat.add_left_cancel heq),
          fun heq => h.2.2 (Nat.add_left_cancel heq)⟩
  | P _ _ _ => trivial

private theorem shiftCircuit_wellFormed
    (offset : Wire) (c : Circuit)
    (h : CircuitWellFormed c) :
    CircuitWellFormed (shiftCircuit offset c) := by
  intro g hg
  simp only [shiftCircuit, List.mem_map] at hg
  obtain ⟨source, hsource, rfl⟩ := hg
  exact shiftGate_wellFormed offset source (h source hsource)

private theorem shiftGate_usesOnly
    (offset : Wire) (ws : List Wire) (g : Gate)
    (h : g.UsesOnly ws) :
    (shiftGate offset g).UsesOnly (shiftWires offset ws) := by
  cases g <;>
    simp only [Gate.UsesOnly, shiftGate, shiftWires,
      List.mem_map] at h ⊢ <;>
    aesop

private theorem shiftCircuit_usesOnly
    (offset : Wire) (ws : List Wire) (c : Circuit)
    (h : CircuitUsesOnly ws c) :
    CircuitUsesOnly
      (shiftWires offset ws)
      (shiftCircuit offset c) := by
  intro g hg
  simp only [shiftCircuit, List.mem_map] at hg
  obtain ⟨source, hsource, rfl⟩ := hg
  exact shiftGate_usesOnly offset ws source (h source hsource)

private theorem shiftWires_nodup
    (offset : Wire) (ws : List Wire)
    (h : ws.Nodup) :
    (shiftWires offset ws).Nodup := by
  apply h.map
  intro a b hab
  exact Nat.add_left_cancel hab

private theorem shiftWires_lower
    (offset : Wire) (ws : List Wire) :
    ∀ w ∈ shiftWires offset ws, offset ≤ w := by
  intro w hw
  simp only [shiftWires, List.mem_map] at hw
  obtain ⟨source, _, rfl⟩ := hw
  exact Nat.le_add_right offset source

private theorem shiftWires_mono
    (offset : Wire) {xs ys : List Wire}
    (hsub : ∀ w ∈ xs, w ∈ ys) :
    ∀ w ∈ shiftWires offset xs,
      w ∈ shiftWires offset ys := by
  intro w hw
  simp only [shiftWires, List.mem_map] at hw ⊢
  obtain ⟨source, hsource, rfl⟩ := hw
  exact ⟨source, hsub source hsource, rfl⟩

private def shiftedView
    (offset : Wire) (st : BasisState) : BasisState :=
  fun w => st (offset + w)

private theorem shiftedView_applyShiftGate
    (offset : Wire) (g : Gate) (st : BasisState) :
    shiftedView offset
        (Classical.applyGate (shiftGate offset g) st) =
      Classical.applyGate g (shiftedView offset st) := by
  cases g <;>
    funext w <;>
    simp [shiftedView, shiftGate, Classical.applyGate, upd,
      Nat.add_left_cancel_iff]

private theorem shiftedView_runShiftCircuit
    (offset : Wire) (c : Circuit) (st : BasisState) :
    shiftedView offset (Classical.run (shiftCircuit offset c) st) =
      Classical.run c (shiftedView offset st) := by
  induction c generalizing st with
  | nil => rfl
  | cons g c ih =>
      simp only [shiftCircuit, List.map_cons, Classical.run_cons]
      change shiftedView offset
          (Classical.run (shiftCircuit offset c)
            (Classical.applyGate (shiftGate offset g) st)) =
        Classical.run c
          (Classical.applyGate g (shiftedView offset st))
      rw [ih, shiftedView_applyShiftGate]

private theorem regValue_shiftWires
    (offset : Wire) (ws : List Wire) (st : BasisState) :
    regValue (shiftWires offset ws) st =
      regValue ws (shiftedView offset st) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      change regValue ((offset + w) :: shiftWires offset ws) st =
        regValue (w :: ws) (shiftedView offset st)
      rw [regValue_cons, regValue_cons, ih]
      rfl

private theorem clean_shiftWires_iff
    (offset : Wire) (ws : List Wire) (st : BasisState) :
    Clean (shiftWires offset ws) st ↔
      Clean ws (shiftedView offset st) := by
  constructor
  · intro h w hw
    exact h (offset + w) (by
      simp [shiftWires, hw])
  · intro h w hw
    simp only [shiftWires, List.mem_map] at hw
    obtain ⟨source, hsource, rfl⟩ := hw
    exact h source hsource

private theorem append_nodup_of_lt_of_le
    (left right : List Wire) (boundary : Wire)
    (hleftNodup : left.Nodup)
    (hrightNodup : right.Nodup)
    (hleft : ∀ w ∈ left, w < boundary)
    (hright : ∀ w ∈ right, boundary ≤ w) :
    (left ++ right).Nodup := by
  rw [List.nodup_append]
  refine ⟨hleftNodup, hrightNodup, ?_⟩
  intro a ha b hb hab
  subst b
  exact (Nat.not_lt_of_ge (hright a hb)) (hleft a ha)

private theorem range'_append_nodup_of_le
    (start₁ length₁ start₂ length₂ : Nat)
    (hseparated : start₁ + length₁ ≤ start₂) :
    (List.range' start₁ length₁ ++
      List.range' start₂ length₂).Nodup := by
  apply append_nodup_of_lt_of_le _ _ start₂
  · exact List.nodup_range'
  · exact List.nodup_range'
  · intro w hw
    exact (List.mem_range'_1.mp hw).2.trans_le hseparated
  · intro w hw
    exact (List.mem_range'_1.mp hw).1

/-! -------------------------------------------------------------------------
    Local PointAdd workspace

The public registers `pointReg` and `outReg` are supplied to `pointAdd`.

Everything else is allocated consecutively beginning at `workStart`.

There are seven 257-bit field registers:

    xField, yField
        Copies of the quantum point coordinates, padded from 256 to 257 bits.

    t0 ... t4
        Five reusable field temporaries.  Their meanings change as the
        affine formulas progress.

After those come the predicate workspace, branch flags, one candidate
point, and the selected result.

The much larger multiplication/exponentiation scratch is placed after this
small local workspace and is reused by every field operation.
------------------------------------------------------------------------- -/

private def fieldAreaSize : Nat :=
  7 * fieldWidth

private def constOffset : Nat :=
  fieldAreaSize

private def zeroHistoryOffset : Nat :=
  constOffset + 256

private def xDifferenceOffset : Nat :=
  zeroHistoryOffset + 1

private def xHistoryOffset : Nat :=
  xDifferenceOffset + 256

private def yDifferenceOffset : Nat :=
  xHistoryOffset + 256

private def yHistoryOffset : Nat :=
  yDifferenceOffset + 256

private def flagOffset : Nat :=
  yHistoryOffset + 256

private def candidateOffset : Nat :=
  flagOffset + 6

private def selectedOffset : Nat :=
  candidateOffset + pointWidth

private def localWorkSize : Nat :=
  selectedOffset + pointWidth

/-! The seven reusable 257-bit registers. -/

def pointAddX (workStart : Wire) : List Wire :=
  List.range' workStart fieldWidth

def pointAddY (workStart : Wire) : List Wire :=
  List.range' (workStart + fieldWidth) fieldWidth

def pointAddT0 (workStart : Wire) : List Wire :=
  List.range' (workStart + 2 * fieldWidth) fieldWidth

def pointAddT1 (workStart : Wire) : List Wire :=
  List.range' (workStart + 3 * fieldWidth) fieldWidth

def pointAddT2 (workStart : Wire) : List Wire :=
  List.range' (workStart + 4 * fieldWidth) fieldWidth

def pointAddT3 (workStart : Wire) : List Wire :=
  List.range' (workStart + 5 * fieldWidth) fieldWidth

def pointAddT4 (workStart : Wire) : List Wire :=
  List.range' (workStart + 6 * fieldWidth) fieldWidth

/-!
Temporary 256-bit classical-coordinate register.

It is used only while computing

    x_R = x_C
    y_R = -y_C.

The constant is loaded, the clean equality predicate is computed, and the
constant is immediately unloaded.
-/

def pointAddConst (workStart : Wire) : List Wire :=
  List.range' (workStart + constOffset) 256

/-! Predicate histories used by `zeroFlag` and `equalFlag`. -/

def pointAddZeroHistory (workStart : Wire) : List Wire :=
  [workStart + zeroHistoryOffset]

def pointAddXDifference (workStart : Wire) : List Wire :=
  List.range' (workStart + xDifferenceOffset) 256

def pointAddXHistory (workStart : Wire) : List Wire :=
  List.range' (workStart + xHistoryOffset) 256

def pointAddYDifference (workStart : Wire) : List Wire :=
  List.range' (workStart + yDifferenceOffset) 256

def pointAddYHistory (workStart : Wire) : List Wire :=
  List.range' (workStart + yHistoryOffset) 256

/-!
Branch flags.

`infinityFlag`
    1 iff the quantum input point is O.

`xEqFlag`
    1 iff x_R = x_C.

`yNegFlag`
    1 iff y_R = -y_C.

`genericFlag`
    1 iff R is finite and x_R ≠ x_C.

`pairFlag`
    temporary conjunction x_R = x_C and y_R ≠ -y_C.

`doubleFlag`
    1 iff R is finite and the doubling branch must be used.
-/

def pointAddInfinityFlag (workStart : Wire) : Wire :=
  workStart + flagOffset

def pointAddXEqFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 1

def pointAddYNegFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 2

def pointAddGenericFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 3

def pointAddPairFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 4

def pointAddDoubleFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 5

/-!
`candidate` is reused:

* first it stores the generic-addition point;
* then the doubling point;
* finally the classical constant C.

After each use it is uncomputed back to zero.

`selected` accumulates exactly one of these mutually-exclusive branches.
-/

def pointAddCandidate (workStart : Wire) : List Wire :=
  List.range' (workStart + candidateOffset) pointWidth

def pointAddSelected (workStart : Wire) : List Wire :=
  List.range' (workStart + selectedOffset) pointWidth

/-!
The concrete M1 arithmetic engine is placed immediately after the local
PointAdd workspace.

Every field operation below loads its operands into this engine, runs the
already-defined concrete arithmetic circuit, copies the result out, and
reverses the engine.  Therefore this same workspace can be reused for every
field operation in one point addition.
-/

def pointAddArithmeticOffset (workStart : Wire) : Wire :=
  workStart + localWorkSize

def pointAddArithmeticWork (workStart : Wire) : List Wire :=
  (shiftWires
      (pointAddArithmeticOffset workStart)
      Secp256k1Instance.secpAddLayout.allWires ++
    shiftWires
      (pointAddArithmeticOffset workStart)
      Secp256k1Instance.secpMulLayout.allWires ++
    shiftWires
      (pointAddArithmeticOffset workStart)
      Secp256k1Instance.secpLayout.allWires).dedup

private theorem pointAddArithmeticWork_lower
    (workStart : Wire) :
    ∀ w ∈ pointAddArithmeticWork workStart,
      pointAddArithmeticOffset workStart ≤ w := by
  intro w hw
  simp only [pointAddArithmeticWork, List.mem_dedup,
    List.mem_append] at hw
  rcases hw with (hadd | hmul) | hinv
  · exact shiftWires_lower _ _ w hadd
  · exact shiftWires_lower _ _ w hmul
  · exact shiftWires_lower _ _ w hinv

def pointAddWork (workStart : Wire) : List Wire :=
  List.range' workStart localWorkSize ++
    pointAddArithmeticWork workStart

/-! -------------------------------------------------------------------------
    Small reversible helpers
------------------------------------------------------------------------- -/

/--
Conditionally XOR-copy one aligned register into another.

If `control = 0`, `dst` is unchanged.
If `control = 1`, `dst := dst XOR src`.

When `dst` starts at zero this is a controlled copy.
-/
def controlledCopyReg (control : Wire) :
    List Wire → List Wire → Circuit
  | s :: src, d :: dst =>
      circuit! {
        gate! Gate.CCX control s d;
        controlledCopyReg control src dst
      }
  | _, _ => circuit! {}

private theorem controlledCopyReg_HPFree
    (control : Wire) :
    ∀ (src dst : List Wire),
      Classical.HPFree (controlledCopyReg control src dst) := by
  intro src
  induction src with
  | nil => intro dst; simp [controlledCopyReg]
  | cons s src ih =>
      intro dst
      cases dst with
      | nil => simp [controlledCopyReg]
      | cons d dst => simp [controlledCopyReg, ih dst]

private theorem controlledCopyReg_usesOnly
    (control : Wire) :
    ∀ (src dst : List Wire),
      CircuitUsesOnly (control :: src ++ dst)
        (controlledCopyReg control src dst) := by
  intro src
  induction src with
  | nil =>
      intro dst
      simp [controlledCopyReg, CircuitUsesOnly]
  | cons s src ih =>
      intro dst
      cases dst with
      | nil => simp [controlledCopyReg, CircuitUsesOnly]
      | cons d dst =>
          rw [controlledCopyReg]
          intro g hg
          simp only [List.mem_cons] at hg
          rcases hg with rfl | hg
          · simp [Gate.UsesOnly]
          · apply (usesOnly_mono (ih dst) ?_) g hg
            intro w hw
            simp only [List.mem_cons, List.mem_append] at hw ⊢
            tauto

private theorem controlledCopyReg_wellFormed
    (control : Wire) :
    ∀ (src dst : List Wire),
      (control :: src ++ dst).Nodup →
      CircuitWellFormed (controlledCopyReg control src dst) := by
  intro src
  induction src with
  | nil => intro dst _; simp [controlledCopyReg]
  | cons s src ih =>
      intro dst hnodup
      cases dst with
      | nil => simp [controlledCopyReg]
      | cons d dst =>
          have htail : (control :: src ++ dst).Nodup := by
            apply List.Nodup.sublist _ hnodup
            apply List.Sublist.cons₂
            exact (List.Sublist.cons s (List.Sublist.refl src)).append
              (List.Sublist.cons d (List.Sublist.refl dst))
          have hgate : (Gate.CCX control s d).WellFormed := by
            have hsub : [control, s, d].Sublist
                (control :: (s :: src) ++ (d :: dst)) := by
              simp
            have hnd : [control, s, d].Nodup :=
              List.Nodup.sublist hsub hnodup
            simp only [List.nodup_cons, List.mem_cons,
              List.not_mem_nil, or_false, not_or] at hnd
            exact ⟨hnd.1.1, hnd.1.2, hnd.2.1⟩
          rw [controlledCopyReg, circuitWellFormed_cons]
          exact ⟨hgate, ih dst htail⟩

private theorem run_controlledCopyReg_false
    (control : Wire) :
    ∀ (src dst : List Wire) (st : BasisState),
      st control = false →
      Classical.run (controlledCopyReg control src dst) st = st := by
  intro src
  induction src with
  | nil => intro dst st _; simp [controlledCopyReg]
  | cons s src ih =>
      intro dst st hcontrol
      cases dst with
      | nil => simp [controlledCopyReg]
      | cons d dst =>
          have hgate :
              Classical.applyGate (Gate.CCX control s d) st = st := by
            funext w
            by_cases hwd : w = d
            · subst w
              simp [Classical.applyGate, hcontrol]
            · exact upd_other st d _ hwd
          rw [controlledCopyReg, Classical.run_cons, hgate]
          exact ih dst st hcontrol

private theorem run_controlledCopyReg_true
    (control : Wire) :
    ∀ (src dst : List Wire) (st : BasisState),
      (control :: src ++ dst).Nodup →
      st control = true →
      Classical.run (controlledCopyReg control src dst) st =
        Classical.run (Arithmetic.copyReg src dst) st := by
  intro src
  induction src with
  | nil =>
      intro dst st _ _
      simp [controlledCopyReg, Arithmetic.copyReg]
  | cons s src ih =>
      intro dst st hnodup hcontrol
      cases dst with
      | nil => simp [controlledCopyReg, Arithmetic.copyReg]
      | cons d dst =>
          have htail : (control :: src ++ dst).Nodup := by
            apply List.Nodup.sublist _ hnodup
            apply List.Sublist.cons₂
            exact (List.Sublist.cons s (List.Sublist.refl src)).append
              (List.Sublist.cons d (List.Sublist.refl dst))
          have hcontrolD : control ≠ d := by
            intro heq
            subst d
            simp at hnodup
          let next :=
            Classical.applyGate (Gate.CCX control s d) st
          have hnextControl : next control = true := by
            change
              st[d ↦ Bool.xor (st d) (st control && st s)] control =
                true
            rw [upd_other _ _ _ hcontrolD]
            exact hcontrol
          have hgate :
              Classical.applyGate (Gate.CCX control s d) st =
                Classical.applyGate (Gate.CX s d) st := by
            funext w
            simp [Classical.applyGate, hcontrol]
          rw [controlledCopyReg, Arithmetic.copyReg]
          simp only [Classical.run_cons]
          rw [hgate]
          exact
            ih dst (Classical.applyGate (Gate.CX s d) st)
              htail (by
                rw [← hgate]
                exact hnextControl)

private theorem applyCX_run_commute
    (support : List Wire) (c : Circuit)
    (source target : Wire)
    (huses : CircuitUsesOnly support c)
    (hsource : source ∉ support)
    (htarget : target ∉ support)
    (st : BasisState) :
    Classical.applyGate (Gate.CX source target)
        (Classical.run c st) =
      Classical.run c
        (Classical.applyGate (Gate.CX source target) st) := by
  have hgateAgrees :
      ∀ w ∈ support,
        Classical.applyGate (Gate.CX source target) st w = st w := by
    intro w hw
    have hwt : w ≠ target := by
      intro heq
      subst w
      exact htarget hw
    simp [Classical.applyGate, upd, hwt]
  funext w
  by_cases hw : w ∈ support
  · have hrunCongr :=
      CircuitUsesOnly.run_congr huses hgateAgrees w hw
    have hwt : w ≠ target := by
      intro heq
      exact htarget (heq ▸ hw)
    simpa [Classical.applyGate, upd, hwt] using hrunCongr.symm
  · rw [huses.preservesOutside
      (Classical.applyGate (Gate.CX source target) st) w hw]
    by_cases hwt : w = target
    · subst w
      simp [Classical.applyGate, upd,
        huses.preservesOutside st target htarget,
        huses.preservesOutside st source hsource]
    · simp [Classical.applyGate, upd, hwt,
        huses.preservesOutside st w hw]

private theorem run_copyReg_reverse_eq
    (src dst : List Wire) (st : BasisState)
    (hnodup : (src ++ dst).Nodup) :
    Classical.run (Arithmetic.copyReg src dst).reverse st =
      Classical.run (Arithmetic.copyReg src dst) st := by
  induction src generalizing dst st with
  | nil => rfl
  | cons source src ih =>
      cases dst with
      | nil => rfl
      | cons target dst =>
          obtain ⟨hsrcNodup, hdstNodup, hcross⟩ :=
            List.nodup_append.mp hnodup
          have htailNodup : (src ++ dst).Nodup :=
            List.nodup_append.mpr
              ⟨(List.nodup_cons.mp hsrcNodup).2,
                (List.nodup_cons.mp hdstNodup).2,
                fun a ha b hb => hcross a
                  (List.mem_cons_of_mem source ha) b
                  (List.mem_cons_of_mem target hb)⟩
          have hsourceOutside : source ∉ src ++ dst := by
            intro hw
            rcases List.mem_append.mp hw with hw | hw
            · exact (List.nodup_cons.mp hsrcNodup).1 hw
            · exact hcross source (List.mem_cons_self ..)
                source (List.mem_cons_of_mem target hw) rfl
          have htargetOutside : target ∉ src ++ dst := by
            intro hw
            rcases List.mem_append.mp hw with hw | hw
            · exact hcross target (List.mem_cons_of_mem source hw)
                target (List.mem_cons_self ..) rfl
            · exact (List.nodup_cons.mp hdstNodup).1 hw
          have htailUses :
              CircuitUsesOnly (src ++ dst)
                (Arithmetic.copyReg src dst) :=
            Arithmetic.copyReg_usesOnly src dst (src ++ dst)
              (fun w hw => List.mem_append_left _ hw)
              (fun w hw => List.mem_append_right _ hw)
          rw [Arithmetic.copyReg, List.reverse_cons,
            Classical.run_append, ih dst st htailNodup]
          simp only [Classical.run_cons, Classical.run_nil]
          exact applyCX_run_commute
            (src ++ dst) (Arithmetic.copyReg src dst)
            source target htailUses hsourceOutside htargetOutside st

private theorem run_copyReg_twice
    (src dst : List Wire) (st : BasisState)
    (hnodup : (src ++ dst).Nodup) :
    Classical.run (Arithmetic.copyReg src dst)
        (Classical.run (Arithmetic.copyReg src dst) st) =
      st := by
  have hcancel := Arithmetic.run_reverse_cancel
    (Arithmetic.copyReg src dst) st
    (Arithmetic.copyReg_HPFree src dst)
    (Arithmetic.copyReg_wellFormed src dst hnodup)
  rw [run_copyReg_reverse_eq src dst
    (Classical.run (Arithmetic.copyReg src dst) st) hnodup]
    at hcancel
  exact hcancel

/--
Pack two 257-bit field values into the 513-bit finite-point representation.

Only the low 256 bits of each field register are used.  The most-significant
257th arithmetic bit is zero for every canonical field element.
-/
def packFinitePoint
    (x y point : List Wire) : Circuit :=
  circuit! {
    loadConst (PointRegister.tag point) 1;
    Arithmetic.copyReg
      (x.take 256)
      (PointRegister.x point);
    Arithmetic.copyReg
      (y.take 256)
      (PointRegister.y point)
  }

/-! -------------------------------------------------------------------------
    Reusable concrete field operations

These wrappers let PointAdd treat the fixed `Secp256k1Instance` circuits
as ordinary clean operations on arbitrary PointAdd registers.

Each wrapper has the conceptual behavior

    |a⟩ |b⟩ |0_out⟩ |0_engine⟩
      ->
    |a⟩ |b⟩ |f(a,b)⟩ |0_engine⟩.

The arithmetic engine is clean again before the wrapper returns.
------------------------------------------------------------------------- -/

private def engineAddLhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.lhs

private def engineAddRhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.rhs

private def engineAddOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.out

def fieldAdd
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineAddLhs offset
  let b := engineAddRhs offset
  let r := engineAddOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpAddProgram
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/-!
A concrete modular-subtraction core using the same first arithmetic blocks
as the concrete modular adder.

Relative blocks:

    0  lhs
    1  rhs
    2  out
    3  raw subtraction
    4  modulus constant
    5  corrected candidate
    6  subtraction carry-in
    7  subtraction carry bank
    8  correction carry-in
    9  correction carry bank
-/

private def fieldSubCore : Circuit :=
  modSub
    (Secp256k1Instance.reg 0).wires
    (Secp256k1Instance.reg 1).wires
    (Secp256k1Instance.reg 2).wires
    (Secp256k1Instance.reg 3).wires
    (Secp256k1Instance.reg 4).wires
    (Secp256k1Instance.reg 5).wires
    (Secp256k1Instance.bitWire 6)
    (Secp256k1Instance.reg 7).wires
    (Secp256k1Instance.bitWire 8)
    (Secp256k1Instance.reg 9).wires
    p

private def engineSubLhs (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 0).wires

private def engineSubRhs (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 1).wires

private def engineSubOut (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 2).wires

def fieldSub
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineSubLhs offset
  let b := engineSubRhs offset
  let r := engineSubOut offset
  let core := shiftCircuit offset fieldSubCore
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/--
Specialized subtraction by a classical constant.

This avoids reserving a permanent 257-bit register for every classical
constant appearing in the affine formulas.
-/
def fieldSubConst
    (offset : Wire)
    (lhs : List Wire)
    (c : Nat)
    (out : List Wire) : Circuit :=
  let a := engineSubLhs offset
  let b := engineSubRhs offset
  let r := engineSubOut offset
  let core := shiftCircuit offset fieldSubCore
  circuit! {
    Arithmetic.copyReg lhs a;
    loadConst b c;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    loadConst b c;
    Arithmetic.copyReg lhs a
  }

private def engineMulLhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.lhs

private def engineMulRhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.rhs

private def engineMulOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.out

def fieldMul
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineMulLhs offset
  let b := engineMulRhs offset
  let r := engineMulOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpMulProgram
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/-!
Fermat inversion.

The concrete exponentiation circuit computes

    a^(p-2) = a⁻¹

for nonzero field elements.

The exponent register is loaded with the classical constant `p - 2`.
-/

private def engineInvBase (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.lhs

private def engineInvExponent (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.rhs

private def engineInvOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.out

def fieldInv
    (offset : Wire)
    (input out : List Wire) : Circuit :=
  let base := engineInvBase offset
  let exponent := engineInvExponent offset
  let result := engineInvOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpProgram
  circuit! {
    Arithmetic.copyReg input base;
    loadConst exponent (p - 2);

    core;

    Arithmetic.copyReg result out;

    core.reverse;

    loadConst exponent (p - 2);
    Arithmetic.copyReg input base
  }

/-! -------------------------------------------------------------------------
    Structural facts for placed field operations

These lemmas isolate the wire-translation and layout reasoning used by all
three point branches.  The branch correctness proofs can consequently reason
about compute/copy/uncompute at the circuit level without reopening the
concrete modular-arithmetic implementations.
------------------------------------------------------------------------- -/

private theorem localWorkSize_eq : localWorkSize = 4112 := by
  norm_num [localWorkSize, selectedOffset, candidateOffset, flagOffset,
    yHistoryOffset, yDifferenceOffset, xHistoryOffset,
    xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
    fieldWidth, Secp256k1Instance.fieldWidth, pointWidth]

private def IsPointAddFieldRegister
    (workStart : Wire) (register : List Wire) : Prop :=
  register = pointAddX workStart ∨
  register = pointAddY workStart ∨
  register = pointAddT0 workStart ∨
  register = pointAddT1 workStart ∨
  register = pointAddT2 workStart ∨
  register = pointAddT3 workStart ∨
  register = pointAddT4 workStart

private theorem pointAddFieldRegister_nodup
    (workStart : Wire) (register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register) :
    register.Nodup := by
  rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact List.nodup_range'

private theorem pointAddFieldRegister_belowArithmetic
    (workStart : Wire) (register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register) :
    ∀ w ∈ register, w < pointAddArithmeticOffset workStart := by
  intro w hw
  rw [pointAddArithmeticOffset, localWorkSize_eq]
  rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hbounds := List.mem_range'_1.mp hw
    apply hbounds.2.trans_le
    norm_num [pointAddX, pointAddY, pointAddT0, pointAddT1,
      pointAddT2, pointAddT3, pointAddT4, fieldWidth,
      Secp256k1Instance.fieldWidth]

private theorem pointAddField_shifted_nodup
    (workStart : Wire) (register engineRegister : List Wire)
    (hregister : IsPointAddFieldRegister workStart register)
    (hengine : engineRegister.Nodup) :
    (register ++
      shiftWires (pointAddArithmeticOffset workStart) engineRegister).Nodup := by
  exact append_nodup_of_lt_of_le _ _
    (pointAddArithmeticOffset workStart)
    (pointAddFieldRegister_nodup workStart register hregister)
    (shiftWires_nodup _ _ hengine)
    (pointAddFieldRegister_belowArithmetic workStart register hregister)
    (shiftWires_lower _ _)

private theorem shifted_pointAddField_nodup
    (workStart : Wire) (engineRegister register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register)
    (hengine : engineRegister.Nodup) :
    (shiftWires (pointAddArithmeticOffset workStart) engineRegister ++
      register).Nodup := by
  rw [List.nodup_append_comm]
  exact pointAddField_shifted_nodup
    workStart register engineRegister hregister hengine

private theorem copyReg_pointAdd_to_shifted_wellFormed
    (workStart : Wire) (register engineRegister : List Wire)
    (hregister : IsPointAddFieldRegister workStart register)
    (hengine : engineRegister.Nodup) :
    CircuitWellFormed
      (Arithmetic.copyReg register
        (shiftWires (pointAddArithmeticOffset workStart) engineRegister)) :=
  Arithmetic.copyReg_wellFormed _ _
    (pointAddField_shifted_nodup
      workStart register engineRegister hregister hengine)

private theorem copyReg_shifted_to_pointAdd_wellFormed
    (workStart : Wire) (engineRegister register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register)
    (hengine : engineRegister.Nodup) :
    CircuitWellFormed
      (Arithmetic.copyReg
        (shiftWires (pointAddArithmeticOffset workStart) engineRegister)
        register) :=
  Arithmetic.copyReg_wellFormed _ _
    (shifted_pointAddField_nodup
      workStart engineRegister register hregister hengine)

private theorem secpMulLayout_valid :
    Secp256k1Instance.secpMulLayout.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Secp256k1Instance.secpMulLayout,
      Secp256k1Instance.reg, Secp256k1Instance.regBlock,
      Secp256k1Instance.fieldWidth]
  · simp [Secp256k1Instance.secpMulLayout,
      Secp256k1Instance.reg, Secp256k1Instance.regBlock,
      Secp256k1Instance.fieldWidth]
  · have hids :
        (([Secp256k1Instance.regBlock Secp256k1Instance.baseId,
            Secp256k1Instance.regBlock Secp256k1Instance.exponentId,
            Secp256k1Instance.regBlock Secp256k1Instance.outId] ++
          Secp256k1Instance.mulWorkBlocks
            Secp256k1Instance.initialAccId
            Secp256k1Instance.historyStartId).map
          Secp256k1Instance.Block.id).Nodup := by
        apply Secp256k1Instance.append_mulWorkBlocks_ids_nodup
        · norm_num [Secp256k1Instance.baseId,
            Secp256k1Instance.exponentId,
            Secp256k1Instance.outId]
        · intro id hid
          simp only [List.map_cons, List.map_nil, List.mem_cons,
            List.not_mem_nil, or_false,
            Secp256k1Instance.regBlock_id] at hid
          rcases hid with rfl | rfl | rfl <;>
            norm_num [Secp256k1Instance.baseId,
              Secp256k1Instance.exponentId,
              Secp256k1Instance.outId,
              Secp256k1Instance.initialAccId]
        · norm_num [Secp256k1Instance.initialAccId,
            Secp256k1Instance.historyStartId]
    have hnd :=
      Secp256k1Instance.blocksWires_nodup
        ([Secp256k1Instance.regBlock Secp256k1Instance.baseId,
            Secp256k1Instance.regBlock Secp256k1Instance.exponentId,
            Secp256k1Instance.regBlock Secp256k1Instance.outId] ++
          Secp256k1Instance.mulWorkBlocks
            Secp256k1Instance.initialAccId
            Secp256k1Instance.historyStartId)
        hids
    simpa [Secp256k1Instance.secpMulLayout,
      RegisterLayout.allWires,
      Secp256k1Instance.mulWork_eq_blocksWires,
      Secp256k1Instance.blocksWires] using hnd

private theorem secpAddProgram_wellFormed :
    CircuitWellFormed Secp256k1Instance.secpAddProgram := by
  unfold Secp256k1Instance.secpAddProgram
    Secp256k1Instance.addProgram
  exact modAdd_wellFormed _ _ _ _ _ _ _ _ _ _ _
    Secp256k1Instance.secpAddWiring.addOK
    Secp256k1Instance.secpAddWiring.redOK
    Secp256k1Instance.secpAddWiring.selectOK

private theorem fieldSubCore_HPFree :
    Classical.HPFree fieldSubCore := by
  unfold fieldSubCore
  exact modSub_HPFree _ _ _ _ _ _ _ _ _ _ _

private theorem fieldSubCore_wellFormed :
    CircuitWellFormed fieldSubCore := by
  unfold fieldSubCore
  apply modSub_wellFormed
  · exact Secp256k1Instance.secpAddWiring.addOK
  · exact Secp256k1Instance.secpAddWiring.redOK
  · apply ModExp.selectOK_of_nodup
    have hall := Secp256k1Instance.blocksWires_nodup
      [Secp256k1Instance.regBlock 7,
        Secp256k1Instance.regBlock 5,
        Secp256k1Instance.regBlock 3,
        Secp256k1Instance.regBlock 2]
      (by norm_num)
    have hshape :
        ((Secp256k1Instance.reg 7).wires ++
          ((Secp256k1Instance.reg 5).wires ++
            (Secp256k1Instance.reg 3).wires ++
            (Secp256k1Instance.reg 2).wires)).Nodup := by
      simpa [Secp256k1Instance.blocksWires,
        List.append_assoc] using hall
    obtain ⟨_, hbody, hcross⟩ :=
      List.nodup_append.mp hshape
    apply List.nodup_cons.mpr
    refine ⟨?_, hbody⟩
    intro hmem
    exact hcross _
      (Secp256k1Instance.carryOut_mem_of_nonempty
        (Secp256k1Instance.bitWire 6)
        (Secp256k1Instance.reg 7).wires
        (by
          simp [Secp256k1Instance.reg,
            Secp256k1Instance.regBlock,
            Secp256k1Instance.Block.wires,
            Secp256k1Instance.fieldWidth]))
      _ hmem rfl

private theorem fieldSubCore_usesOnly :
    CircuitUsesOnly
      Secp256k1Instance.secpAddLayout.allWires
      fieldSubCore := by
  simpa [fieldSubCore, Secp256k1Instance.secpAddLayout,
    RegisterLayout.allWires, Secp256k1Instance.addWork,
    Secp256k1Instance.addScratchBlocks,
    Secp256k1Instance.blocksWires,
    Secp256k1Instance.bitBlock_wires,
    List.append_assoc] using
    (modSub_usesOnly
      (Secp256k1Instance.reg 0).wires
      (Secp256k1Instance.reg 1).wires
      (Secp256k1Instance.reg 2).wires
      (Secp256k1Instance.reg 3).wires
      (Secp256k1Instance.reg 4).wires
      (Secp256k1Instance.reg 5).wires
      (Secp256k1Instance.bitWire 6)
      (Secp256k1Instance.reg 7).wires
      (Secp256k1Instance.bitWire 8)
      (Secp256k1Instance.reg 9).wires p)

private theorem secpMulProgram_wellFormed :
    CircuitWellFormed Secp256k1Instance.secpMulProgram :=
  Secp256k1Instance.secp_modMul_contract.wellFormed
    secpMulLayout_valid

private theorem secpProgram_wellFormed :
    CircuitWellFormed Secp256k1Instance.secpProgram :=
  Secp256k1Instance.secp_modExp_contract.wellFormed
    Secp256k1Instance.secpPlan_layout_valid

private theorem fieldAdd_HPFree
    (offset : Wire) (lhs rhs out : List Wire) :
    Classical.HPFree (fieldAdd offset lhs rhs out) := by
  have hcore :
      Classical.HPFree
        (shiftCircuit offset Secp256k1Instance.secpAddProgram) :=
    shiftCircuit_HPFree _ _
      Secp256k1Instance.secp_modAdd_contract.hpFree
  simp [fieldAdd, hcore, Arithmetic.hpFree_reverse hcore]

private theorem fieldAdd_wellFormed
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitWellFormed
      (fieldAdd (pointAddArithmeticOffset workStart) lhs rhs out) := by
  let offset := pointAddArithmeticOffset workStart
  let a := engineAddLhs offset
  let b := engineAddRhs offset
  let r := engineAddOut offset
  let core := shiftCircuit offset Secp256k1Instance.secpAddProgram
  have haNodup :
      (lhs ++ a).Nodup := by
    simpa [a, offset, engineAddLhs,
      Secp256k1Instance.secpAddLayout,
      Secp256k1Instance.baseId] using
      (pointAddField_shifted_nodup workStart lhs
        (Secp256k1Instance.reg Secp256k1Instance.baseId).wires
        hlhs
        (Secp256k1Instance.regBlock
          Secp256k1Instance.baseId).wires_nodup)
  have hbNodup :
      (rhs ++ b).Nodup := by
    simpa [b, offset, engineAddRhs,
      Secp256k1Instance.secpAddLayout,
      Secp256k1Instance.exponentId] using
      (pointAddField_shifted_nodup workStart rhs
        (Secp256k1Instance.reg Secp256k1Instance.exponentId).wires
        hrhs
        (Secp256k1Instance.regBlock
          Secp256k1Instance.exponentId).wires_nodup)
  have hrNodup :
      (r ++ out).Nodup := by
    simpa [r, offset, engineAddOut,
      Secp256k1Instance.secpAddLayout,
      Secp256k1Instance.outId] using
      (shifted_pointAddField_nodup workStart
        (Secp256k1Instance.reg Secp256k1Instance.outId).wires
        out hout
        (Secp256k1Instance.regBlock
          Secp256k1Instance.outId).wires_nodup)
  have hcopyA :
      CircuitWellFormed (Arithmetic.copyReg lhs a) :=
    Arithmetic.copyReg_wellFormed _ _ haNodup
  have hcopyB :
      CircuitWellFormed (Arithmetic.copyReg rhs b) :=
    Arithmetic.copyReg_wellFormed _ _ hbNodup
  have hcopyOut :
      CircuitWellFormed (Arithmetic.copyReg r out) :=
    Arithmetic.copyReg_wellFormed _ _ hrNodup
  have hcore : CircuitWellFormed core :=
    shiftCircuit_wellFormed _ _ secpAddProgram_wellFormed
  simp [fieldAdd, a, b, r, core, offset, hcopyA, hcopyB,
    hcopyOut, hcore, Arithmetic.wellFormed_reverse hcore]

private theorem fieldSub_HPFree
    (offset : Wire) (lhs rhs out : List Wire) :
    Classical.HPFree (fieldSub offset lhs rhs out) := by
  have hcore :
      Classical.HPFree (shiftCircuit offset fieldSubCore) :=
    shiftCircuit_HPFree _ _ fieldSubCore_HPFree
  simp [fieldSub, hcore, Arithmetic.hpFree_reverse hcore]

private theorem fieldSub_wellFormed
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitWellFormed
      (fieldSub (pointAddArithmeticOffset workStart) lhs rhs out) := by
  let offset := pointAddArithmeticOffset workStart
  let a := engineSubLhs offset
  let b := engineSubRhs offset
  let r := engineSubOut offset
  let core := shiftCircuit offset fieldSubCore
  have hcopyA : CircuitWellFormed (Arithmetic.copyReg lhs a) := by
    simpa [a, offset, engineSubLhs] using
      (copyReg_pointAdd_to_shifted_wellFormed workStart lhs
        (Secp256k1Instance.reg 0).wires hlhs
        (Secp256k1Instance.regBlock 0).wires_nodup)
  have hcopyB : CircuitWellFormed (Arithmetic.copyReg rhs b) := by
    simpa [b, offset, engineSubRhs] using
      (copyReg_pointAdd_to_shifted_wellFormed workStart rhs
        (Secp256k1Instance.reg 1).wires hrhs
        (Secp256k1Instance.regBlock 1).wires_nodup)
  have hcopyOut : CircuitWellFormed (Arithmetic.copyReg r out) := by
    simpa [r, offset, engineSubOut] using
      (copyReg_shifted_to_pointAdd_wellFormed workStart
        (Secp256k1Instance.reg 2).wires out hout
        (Secp256k1Instance.regBlock 2).wires_nodup)
  have hcore : CircuitWellFormed core :=
    shiftCircuit_wellFormed _ _ fieldSubCore_wellFormed
  simp [fieldSub, a, b, r, core, offset, hcopyA, hcopyB,
    hcopyOut, hcore, Arithmetic.wellFormed_reverse hcore]

private theorem fieldSubConst_HPFree
    (offset : Wire) (lhs : List Wire) (c : Nat) (out : List Wire) :
    Classical.HPFree (fieldSubConst offset lhs c out) := by
  have hcore :
      Classical.HPFree (shiftCircuit offset fieldSubCore) :=
    shiftCircuit_HPFree _ _ fieldSubCore_HPFree
  simp [fieldSubConst, hcore, Arithmetic.hpFree_reverse hcore,
    loadConst_HPFree]

private theorem fieldSubConst_wellFormed
    (workStart : Wire) (lhs : List Wire) (c : Nat) (out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitWellFormed
      (fieldSubConst
        (pointAddArithmeticOffset workStart) lhs c out) := by
  let offset := pointAddArithmeticOffset workStart
  let a := engineSubLhs offset
  let b := engineSubRhs offset
  let r := engineSubOut offset
  let core := shiftCircuit offset fieldSubCore
  have hcopyA : CircuitWellFormed (Arithmetic.copyReg lhs a) := by
    simpa [a, offset, engineSubLhs] using
      (copyReg_pointAdd_to_shifted_wellFormed workStart lhs
        (Secp256k1Instance.reg 0).wires hlhs
        (Secp256k1Instance.regBlock 0).wires_nodup)
  have hloadB : CircuitWellFormed (loadConst b c) :=
    loadConst_wellFormed _ _
  have hcopyOut : CircuitWellFormed (Arithmetic.copyReg r out) := by
    simpa [r, offset, engineSubOut] using
      (copyReg_shifted_to_pointAdd_wellFormed workStart
        (Secp256k1Instance.reg 2).wires out hout
        (Secp256k1Instance.regBlock 2).wires_nodup)
  have hcore : CircuitWellFormed core :=
    shiftCircuit_wellFormed _ _ fieldSubCore_wellFormed
  simp [fieldSubConst, a, b, r, core, offset, hcopyA, hloadB,
    hcopyOut, hcore, Arithmetic.wellFormed_reverse hcore]

private theorem fieldMul_HPFree
    (offset : Wire) (lhs rhs out : List Wire) :
    Classical.HPFree (fieldMul offset lhs rhs out) := by
  have hcore :
      Classical.HPFree
        (shiftCircuit offset Secp256k1Instance.secpMulProgram) :=
    shiftCircuit_HPFree _ _
      Secp256k1Instance.secp_modMul_contract.hpFree
  simp [fieldMul, hcore, Arithmetic.hpFree_reverse hcore]

private theorem fieldMul_wellFormed
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitWellFormed
      (fieldMul (pointAddArithmeticOffset workStart) lhs rhs out) := by
  let offset := pointAddArithmeticOffset workStart
  let a := engineMulLhs offset
  let b := engineMulRhs offset
  let r := engineMulOut offset
  let core := shiftCircuit offset Secp256k1Instance.secpMulProgram
  have hcopyA : CircuitWellFormed (Arithmetic.copyReg lhs a) := by
    simpa [a, offset, engineMulLhs,
      Secp256k1Instance.secpMulLayout,
      Secp256k1Instance.baseId] using
      (copyReg_pointAdd_to_shifted_wellFormed workStart lhs
        (Secp256k1Instance.reg Secp256k1Instance.baseId).wires
        hlhs
        (Secp256k1Instance.regBlock
          Secp256k1Instance.baseId).wires_nodup)
  have hcopyB : CircuitWellFormed (Arithmetic.copyReg rhs b) := by
    simpa [b, offset, engineMulRhs,
      Secp256k1Instance.secpMulLayout,
      Secp256k1Instance.exponentId] using
      (copyReg_pointAdd_to_shifted_wellFormed workStart rhs
        (Secp256k1Instance.reg Secp256k1Instance.exponentId).wires
        hrhs
        (Secp256k1Instance.regBlock
          Secp256k1Instance.exponentId).wires_nodup)
  have hcopyOut : CircuitWellFormed (Arithmetic.copyReg r out) := by
    simpa [r, offset, engineMulOut,
      Secp256k1Instance.secpMulLayout,
      Secp256k1Instance.outId] using
      (copyReg_shifted_to_pointAdd_wellFormed workStart
        (Secp256k1Instance.reg Secp256k1Instance.outId).wires
        out hout
        (Secp256k1Instance.regBlock
          Secp256k1Instance.outId).wires_nodup)
  have hcore : CircuitWellFormed core :=
    shiftCircuit_wellFormed _ _ secpMulProgram_wellFormed
  simp [fieldMul, a, b, r, core, offset, hcopyA, hcopyB,
    hcopyOut, hcore, Arithmetic.wellFormed_reverse hcore]

private theorem fieldInv_HPFree
    (offset : Wire) (input out : List Wire) :
    Classical.HPFree (fieldInv offset input out) := by
  have hcore :
      Classical.HPFree
        (shiftCircuit offset Secp256k1Instance.secpProgram) :=
    shiftCircuit_HPFree _ _
      Secp256k1Instance.secp_modExp_contract.hpFree
  simp [fieldInv, hcore, Arithmetic.hpFree_reverse hcore,
    loadConst_HPFree]

private theorem fieldInv_wellFormed
    (workStart : Wire) (input out : List Wire)
    (hinput : IsPointAddFieldRegister workStart input)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitWellFormed
      (fieldInv (pointAddArithmeticOffset workStart) input out) := by
  let offset := pointAddArithmeticOffset workStart
  let base := engineInvBase offset
  let exponent := engineInvExponent offset
  let result := engineInvOut offset
  let core := shiftCircuit offset Secp256k1Instance.secpProgram
  have hbaseNodup : Secp256k1Instance.secpLayout.lhs.Nodup := by
    change
      (Secp256k1Instance.reg Secp256k1Instance.baseId).wires.Nodup
    exact
      (Secp256k1Instance.regBlock
        Secp256k1Instance.baseId).wires_nodup
  have hexponentNodup :
      Secp256k1Instance.secpLayout.rhs.Nodup := by
    change
      (Secp256k1Instance.reg Secp256k1Instance.exponentId).wires.Nodup
    exact
      (Secp256k1Instance.regBlock
        Secp256k1Instance.exponentId).wires_nodup
  have hresultNodup : Secp256k1Instance.secpLayout.out.Nodup := by
    change
      (Secp256k1Instance.reg Secp256k1Instance.outId).wires.Nodup
    exact
      (Secp256k1Instance.regBlock
        Secp256k1Instance.outId).wires_nodup
  have hcopyBase :
      CircuitWellFormed (Arithmetic.copyReg input base) := by
    simpa [base, offset, engineInvBase] using
      (copyReg_pointAdd_to_shifted_wellFormed workStart input
        Secp256k1Instance.secpLayout.lhs hinput hbaseNodup)
  have hloadExponent :
      CircuitWellFormed (loadConst exponent (p - 2)) :=
    loadConst_wellFormed _ _
  have hcopyResult :
      CircuitWellFormed (Arithmetic.copyReg result out) := by
    simpa [result, offset, engineInvOut] using
      (copyReg_shifted_to_pointAdd_wellFormed workStart
        Secp256k1Instance.secpLayout.out out hout hresultNodup)
  have hcore : CircuitWellFormed core :=
    shiftCircuit_wellFormed _ _ secpProgram_wellFormed
  simp [fieldInv, base, exponent, result, core, offset,
    hcopyBase, hloadExponent, hcopyResult, hcore,
    Arithmetic.wellFormed_reverse hcore]

private theorem binaryFieldWrapper_usesOnly
    (lhs rhs out a b r engineWires : List Wire)
    (core : Circuit)
    (ha : ∀ w ∈ a, w ∈ engineWires)
    (hb : ∀ w ∈ b, w ∈ engineWires)
    (hr : ∀ w ∈ r, w ∈ engineWires)
    (hcore : CircuitUsesOnly engineWires core) :
    CircuitUsesOnly
      (lhs ++ rhs ++ out ++ engineWires)
      (circuit! {
        Arithmetic.copyReg lhs a;
        Arithmetic.copyReg rhs b;
        core;
        Arithmetic.copyReg r out;
        core.reverse;
        Arithmetic.copyReg rhs b;
        Arithmetic.copyReg lhs a
      }) := by
  let support := lhs ++ rhs ++ out ++ engineWires
  have hlhs : ∀ w ∈ lhs, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hrhs : ∀ w ∈ rhs, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hout : ∀ w ∈ out, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hengine : ∀ w ∈ engineWires, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hcopyA := Arithmetic.copyReg_usesOnly lhs a support
    hlhs (fun w hw => hengine w (ha w hw))
  have hcopyB := Arithmetic.copyReg_usesOnly rhs b support
    hrhs (fun w hw => hengine w (hb w hw))
  have hcopyOut := Arithmetic.copyReg_usesOnly r out support
    (fun w hw => hengine w (hr w hw)) hout
  have hcore' := usesOnly_mono hcore hengine
  have hall :=
    usesOnly_append
      (usesOnly_append
        (usesOnly_append
          (usesOnly_append
            (usesOnly_append
              (usesOnly_append hcopyA hcopyB) hcore') hcopyOut)
            (usesOnly_reverse hcore')) hcopyB) hcopyA
  simpa [support, List.append_assoc] using hall

private theorem unaryConstFieldWrapper_usesOnly
    (input out a b r engineWires : List Wire)
    (constant : Nat) (core : Circuit)
    (ha : ∀ w ∈ a, w ∈ engineWires)
    (hb : ∀ w ∈ b, w ∈ engineWires)
    (hr : ∀ w ∈ r, w ∈ engineWires)
    (hcore : CircuitUsesOnly engineWires core) :
    CircuitUsesOnly
      (input ++ out ++ engineWires)
      (circuit! {
        Arithmetic.copyReg input a;
        loadConst b constant;
        core;
        Arithmetic.copyReg r out;
        core.reverse;
        loadConst b constant;
        Arithmetic.copyReg input a
      }) := by
  let support := input ++ out ++ engineWires
  have hinput : ∀ w ∈ input, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hout : ∀ w ∈ out, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hengine : ∀ w ∈ engineWires, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hcopyA := Arithmetic.copyReg_usesOnly input a support
    hinput (fun w hw => hengine w (ha w hw))
  have hloadB := usesOnly_mono (loadConst_usesOnly b constant)
    (fun w hw => hengine w (hb w hw))
  have hcopyOut := Arithmetic.copyReg_usesOnly r out support
    (fun w hw => hengine w (hr w hw)) hout
  have hcore' := usesOnly_mono hcore hengine
  have hall :=
    usesOnly_append
      (usesOnly_append
        (usesOnly_append
          (usesOnly_append
            (usesOnly_append
              (usesOnly_append hcopyA hloadB) hcore') hcopyOut)
            (usesOnly_reverse hcore')) hloadB) hcopyA
  simpa [support, List.append_assoc] using hall

private theorem fieldAdd_usesOnly
    (offset : Wire) (lhs rhs out : List Wire) :
    CircuitUsesOnly
      (lhs ++ rhs ++ out ++
        shiftWires offset
          Secp256k1Instance.secpAddLayout.allWires)
      (fieldAdd offset lhs rhs out) := by
  let engineWires :=
    shiftWires offset Secp256k1Instance.secpAddLayout.allWires
  have ha : ∀ w ∈ engineAddLhs offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hb : ∀ w ∈ engineAddRhs offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hr : ∀ w ∈ engineAddOut offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hcore :
      CircuitUsesOnly engineWires
        (shiftCircuit offset Secp256k1Instance.secpAddProgram) :=
    shiftCircuit_usesOnly _ _ _
      Secp256k1Instance.secp_modAdd_contract.usesOnly
  simpa [fieldAdd, engineWires] using
    (binaryFieldWrapper_usesOnly lhs rhs out
      (engineAddLhs offset) (engineAddRhs offset)
      (engineAddOut offset) engineWires
      (shiftCircuit offset Secp256k1Instance.secpAddProgram)
      ha hb hr hcore)

private theorem fieldSub_usesOnly
    (offset : Wire) (lhs rhs out : List Wire) :
    CircuitUsesOnly
      (lhs ++ rhs ++ out ++
        shiftWires offset
          Secp256k1Instance.secpAddLayout.allWires)
      (fieldSub offset lhs rhs out) := by
  let engineWires :=
    shiftWires offset Secp256k1Instance.secpAddLayout.allWires
  have ha : ∀ w ∈ engineSubLhs offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    unfold Secp256k1Instance.secpAddLayout RegisterLayout.allWires
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (by
      simpa [Secp256k1Instance.baseId] using hw)))
  have hb : ∀ w ∈ engineSubRhs offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    unfold Secp256k1Instance.secpAddLayout RegisterLayout.allWires
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (by
      simpa [Secp256k1Instance.exponentId] using hw)))
  have hr : ∀ w ∈ engineSubOut offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    unfold Secp256k1Instance.secpAddLayout RegisterLayout.allWires
    simp only [List.mem_append]
    exact Or.inl (Or.inr (by
      simpa [Secp256k1Instance.outId] using hw))
  have hcore :
      CircuitUsesOnly engineWires
        (shiftCircuit offset fieldSubCore) :=
    shiftCircuit_usesOnly _ _ _ fieldSubCore_usesOnly
  simpa [fieldSub, engineWires] using
    (binaryFieldWrapper_usesOnly lhs rhs out
      (engineSubLhs offset) (engineSubRhs offset)
      (engineSubOut offset) engineWires
      (shiftCircuit offset fieldSubCore)
      ha hb hr hcore)

private theorem fieldSubConst_usesOnly
    (offset : Wire) (lhs : List Wire) (constant : Nat)
    (out : List Wire) :
    CircuitUsesOnly
      (lhs ++ out ++
        shiftWires offset
          Secp256k1Instance.secpAddLayout.allWires)
      (fieldSubConst offset lhs constant out) := by
  let engineWires :=
    shiftWires offset Secp256k1Instance.secpAddLayout.allWires
  have ha : ∀ w ∈ engineSubLhs offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    unfold Secp256k1Instance.secpAddLayout RegisterLayout.allWires
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (by
      simpa [Secp256k1Instance.baseId] using hw)))
  have hb : ∀ w ∈ engineSubRhs offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    unfold Secp256k1Instance.secpAddLayout RegisterLayout.allWires
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (by
      simpa [Secp256k1Instance.exponentId] using hw)))
  have hr : ∀ w ∈ engineSubOut offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    unfold Secp256k1Instance.secpAddLayout RegisterLayout.allWires
    simp only [List.mem_append]
    exact Or.inl (Or.inr (by
      simpa [Secp256k1Instance.outId] using hw))
  have hcore :
      CircuitUsesOnly engineWires
        (shiftCircuit offset fieldSubCore) :=
    shiftCircuit_usesOnly _ _ _ fieldSubCore_usesOnly
  simpa [fieldSubConst, engineWires] using
    (unaryConstFieldWrapper_usesOnly lhs out
      (engineSubLhs offset) (engineSubRhs offset)
      (engineSubOut offset) engineWires constant
      (shiftCircuit offset fieldSubCore)
      ha hb hr hcore)

private theorem fieldMul_usesOnly
    (offset : Wire) (lhs rhs out : List Wire) :
    CircuitUsesOnly
      (lhs ++ rhs ++ out ++
        shiftWires offset
          Secp256k1Instance.secpMulLayout.allWires)
      (fieldMul offset lhs rhs out) := by
  let engineWires :=
    shiftWires offset Secp256k1Instance.secpMulLayout.allWires
  have ha : ∀ w ∈ engineMulLhs offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hb : ∀ w ∈ engineMulRhs offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hr : ∀ w ∈ engineMulOut offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hcore :
      CircuitUsesOnly engineWires
        (shiftCircuit offset Secp256k1Instance.secpMulProgram) :=
    shiftCircuit_usesOnly _ _ _
      Secp256k1Instance.secp_modMul_contract.usesOnly
  simpa [fieldMul, engineWires] using
    (binaryFieldWrapper_usesOnly lhs rhs out
      (engineMulLhs offset) (engineMulRhs offset)
      (engineMulOut offset) engineWires
      (shiftCircuit offset Secp256k1Instance.secpMulProgram)
      ha hb hr hcore)

private theorem fieldInv_usesOnly
    (offset : Wire) (input out : List Wire) :
    CircuitUsesOnly
      (input ++ out ++
        shiftWires offset Secp256k1Instance.secpLayout.allWires)
      (fieldInv offset input out) := by
  let engineWires :=
    shiftWires offset Secp256k1Instance.secpLayout.allWires
  have ha : ∀ w ∈ engineInvBase offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hb :
      ∀ w ∈ engineInvExponent offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hr : ∀ w ∈ engineInvOut offset, w ∈ engineWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hcore :
      CircuitUsesOnly engineWires
        (shiftCircuit offset Secp256k1Instance.secpProgram) :=
    shiftCircuit_usesOnly _ _ _
      Secp256k1Instance.secp_modExp_contract.usesOnly
  simpa [fieldInv, engineWires] using
    (unaryConstFieldWrapper_usesOnly input out
      (engineInvBase offset) (engineInvExponent offset)
      (engineInvOut offset) engineWires (p - 2)
      (shiftCircuit offset Secp256k1Instance.secpProgram)
      ha hb hr hcore)

/-! -------------------------------------------------------------------------
    Generic affine addition
------------------------------------------------------------------------- -/

/--
Compute the generic affine coordinates for

    R = (x₁,y₁)
    C = (x₂,y₂)

with `x₁ ≠ x₂`.

Only five temporary field registers are used.

At the end:

    t2 = x₃
    t4 = y₃

while the other temporaries contain reversible history that is removed when
this circuit is run backwards.
-/
def genericPointCompute
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let offset := pointAddArithmeticOffset workStart

  let x := pointAddX workStart
  let y := pointAddY workStart

  let t0 := pointAddT0 workStart
  let t1 := pointAddT1 workStart
  let t2 := pointAddT2 workStart
  let t3 := pointAddT3 workStart
  let t4 := pointAddT4 workStart

  /- t0 = y₁ - y₂ -/
  let numerator :=
    fieldSubConst offset y yC.val t0

  /- t1 = x₁ - x₂ -/
  let denominator :=
    fieldSubConst offset x xC.val t1

  /- t2 = (x₁ - x₂)⁻¹ -/
  let inverse :=
    fieldInv offset t1 t2

  /- t3 = λ -/
  let slope :=
    fieldMul offset t0 t2 t3

  /- After λ has been obtained, numerator/denominator/inverse are no
     longer needed.  Uncomputing them frees t0,t1,t2 for reuse. -/

  /- t0 = λ² -/
  let slopeSq :=
    fieldMul offset t3 t3 t0

  /- t1 = λ² - x₁ -/
  let minusX :=
    fieldSub offset t0 x t1

  /- t2 = x₃ = λ² - x₁ - x₂ -/
  let xOut :=
    fieldSubConst offset t1 xC.val t2

  /- Once x₃ is available, λ² and λ²-x₁ can be uncomputed. -/

  /- t0 = x₁ - x₃ -/
  let xDifference :=
    fieldSub offset x t2 t0

  /- t1 = λ(x₁-x₃) -/
  let yProduct :=
    fieldMul offset t3 t0 t1

  /- t4 = y₃ -/
  let yOut :=
    fieldSub offset t1 y t4

  circuit! {
    numerator;
    denominator;
    inverse;
    slope;

    inverse.reverse;
    denominator.reverse;
    numerator.reverse;

    slopeSq;
    minusX;
    xOut;

    minusX.reverse;
    slopeSq.reverse;

    xDifference;
    yProduct;
    yOut
  }

/-! -------------------------------------------------------------------------
    Point doubling
------------------------------------------------------------------------- -/

/--
Cleanly compute `3*x²` into `out`.

`scratch0` and `scratch1` are restored before the operation returns.
-/
def threeXSquared
    (offset : Wire)
    (x scratch0 scratch1 out : List Wire) : Circuit :=
  let square :=
    fieldMul offset x x scratch0
  let twice :=
    fieldAdd offset scratch0 scratch0 scratch1
  let three :=
    fieldAdd offset scratch1 scratch0 out
  circuit! {
    square;
    twice;
    three;
    twice.reverse;
    square.reverse
  }

/--
Compute the affine doubling coordinates.

For secp256k1, the curve coefficient `a` is zero, hence

    λ = 3x² / 2y.

At the end:

    t2 = x₃
    t4 = y₃.
-/
def doublePointCompute
    (workStart : Wire) : Circuit :=
  let offset := pointAddArithmeticOffset workStart

  let x := pointAddX workStart
  let y := pointAddY workStart

  let t0 := pointAddT0 workStart
  let t1 := pointAddT1 workStart
  let t2 := pointAddT2 workStart
  let t3 := pointAddT3 workStart
  let t4 := pointAddT4 workStart

  /- t2 = 3x₁²; t0,t1 are returned to zero. -/
  let numerator :=
    threeXSquared offset x t0 t1 t2

  /- t0 = 2y₁ -/
  let denominator :=
    fieldAdd offset y y t0

  /- t1 = (2y₁)⁻¹ -/
  let inverse :=
    fieldInv offset t0 t1

  /- t3 = λ -/
  let slope :=
    fieldMul offset t2 t1 t3

  /- t0 = λ² -/
  let slopeSq :=
    fieldMul offset t3 t3 t0

  /- t1 = 2x₁ -/
  let twoX :=
    fieldAdd offset x x t1

  /- t2 = x₃ = λ² - 2x₁ -/
  let xOut :=
    fieldSub offset t0 t1 t2

  /- t0 = x₁ - x₃ -/
  let xDifference :=
    fieldSub offset x t2 t0

  /- t1 = λ(x₁-x₃) -/
  let yProduct :=
    fieldMul offset t3 t0 t1

  /- t4 = y₃ -/
  let yOut :=
    fieldSub offset t1 y t4

  circuit! {
    numerator;
    denominator;
    inverse;
    slope;

    inverse.reverse;
    denominator.reverse;
    numerator.reverse;

    slopeSq;
    twoX;
    xOut;

    twoX.reverse;
    slopeSq.reverse;

    xDifference;
    yProduct;
    yOut
  }

private theorem genericPointCompute_HPFree
    (workStart : Wire) (xC yC : Fp) :
    Classical.HPFree (genericPointCompute workStart xC yC) := by
  simp [genericPointCompute, fieldSubConst_HPFree, fieldInv_HPFree,
    fieldMul_HPFree, fieldSub_HPFree, Arithmetic.hpFree_reverse]

private theorem genericPointCompute_wellFormed
    (workStart : Wire) (xC yC : Fp) :
    CircuitWellFormed (genericPointCompute workStart xC yC) := by
  simp [genericPointCompute, fieldSubConst_wellFormed,
    fieldInv_wellFormed, fieldMul_wellFormed,
    fieldSub_wellFormed, IsPointAddFieldRegister,
    Arithmetic.wellFormed_reverse]

private theorem threeXSquared_HPFree
    (offset : Wire)
    (x scratch₀ scratch₁ out : List Wire) :
    Classical.HPFree
      (threeXSquared offset x scratch₀ scratch₁ out) := by
  simp [threeXSquared, fieldMul_HPFree, fieldAdd_HPFree,
    Arithmetic.hpFree_reverse]

private theorem threeXSquared_wellFormed
    (workStart : Wire)
    (x scratch₀ scratch₁ out : List Wire)
    (hx : IsPointAddFieldRegister workStart x)
    (hscratch₀ : IsPointAddFieldRegister workStart scratch₀)
    (hscratch₁ : IsPointAddFieldRegister workStart scratch₁)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitWellFormed
      (threeXSquared (pointAddArithmeticOffset workStart)
        x scratch₀ scratch₁ out) := by
  simp [threeXSquared, fieldMul_wellFormed,
    fieldAdd_wellFormed, hx, hscratch₀, hscratch₁, hout,
    Arithmetic.wellFormed_reverse]

private theorem doublePointCompute_HPFree
    (workStart : Wire) :
    Classical.HPFree (doublePointCompute workStart) := by
  simp [doublePointCompute, threeXSquared_HPFree,
    fieldAdd_HPFree, fieldInv_HPFree, fieldMul_HPFree,
    fieldSub_HPFree, Arithmetic.hpFree_reverse]

private theorem doublePointCompute_wellFormed
    (workStart : Wire) :
    CircuitWellFormed (doublePointCompute workStart) := by
  simp [doublePointCompute, threeXSquared_wellFormed,
    fieldAdd_wellFormed, fieldInv_wellFormed,
    fieldMul_wellFormed, fieldSub_wellFormed,
    IsPointAddFieldRegister, Arithmetic.wellFormed_reverse]

private theorem packFinitePoint_HPFree
    (x y point : List Wire) :
    Classical.HPFree (packFinitePoint x y point) := by
  simp [packFinitePoint, loadConst_HPFree]

set_option maxRecDepth 10000 in
private theorem packFinitePoint_wellFormed
    (workStart : Wire) :
    CircuitWellFormed
      (packFinitePoint
        (pointAddT2 workStart)
        (pointAddT4 workStart)
        (pointAddCandidate workStart)) := by
  have hxNodup :
      ((pointAddT2 workStart).take 256 ++
        PointRegister.x (pointAddCandidate workStart)).Nodup := by
    have h := range'_append_nodup_of_le
      (workStart + 4 * 257) 256
      (workStart + 3086 + 1) 256 (by omega)
    simpa [pointAddT2, pointAddCandidate, PointRegister.x,
      fieldWidth, Secp256k1Instance.fieldWidth, candidateOffset,
      flagOffset, yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      List.take_range'_of_length_ge, List.drop_range'] using h
  have hyNodup :
      ((pointAddT4 workStart).take 256 ++
        PointRegister.y (pointAddCandidate workStart)).Nodup := by
    have h := range'_append_nodup_of_le
      (workStart + 6 * 257) 256
      (workStart + 3086 + 257) 256 (by omega)
    simpa [pointAddT4, pointAddCandidate, PointRegister.y,
      fieldWidth, Secp256k1Instance.fieldWidth, candidateOffset,
      flagOffset, yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      List.take_range'_of_length_ge, List.drop_range'] using h
  have hxCopy :
      CircuitWellFormed
        (Arithmetic.copyReg
          ((pointAddT2 workStart).take 256)
          (PointRegister.x (pointAddCandidate workStart))) :=
    Arithmetic.copyReg_wellFormed _ _ hxNodup
  have hyCopy :
      CircuitWellFormed
        (Arithmetic.copyReg
          ((pointAddT4 workStart).take 256)
          (PointRegister.y (pointAddCandidate workStart))) :=
    Arithmetic.copyReg_wellFormed _ _ hyNodup
  simp [packFinitePoint, loadConst_wellFormed, hxCopy, hyCopy]

/-! -------------------------------------------------------------------------
    Exceptional-case flags
------------------------------------------------------------------------- -/

/--
Compute the branch flags for addition by the finite constant `(xC,yC)`.

For a valid input point exactly one of the following happens:

* `infinityFlag = 1`
      R = O

* `genericFlag = 1`
      R is finite and x_R ≠ x_C

* `doubleFlag = 1`
      R is finite, x_R = x_C, and y_R ≠ -y_C

* all three are zero
      R = -C, so the result is O.

The inverse-pair branch deliberately requires no output candidate:
the canonical encoding of O is all zero, and `selected` already starts zero.
-/
def pointAddFlags
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let constReg := pointAddConst workStart

  let infinityFlag := pointAddInfinityFlag workStart
  let xEqFlag := pointAddXEqFlag workStart
  let yNegFlag := pointAddYNegFlag workStart
  let genericFlag := pointAddGenericFlag workStart
  let pairFlag := pointAddPairFlag workStart
  let doubleFlag := pointAddDoubleFlag workStart

  circuit! {
    /- infinityFlag = (R = O) -/
    zeroFlag
      (PointRegister.tag pointReg)
      infinityFlag
      (pointAddZeroHistory workStart);

    /- xEqFlag = (x_R = x_C) -/
    loadConst constReg xC.val;
    equalFlag
      (PointRegister.x pointReg)
      constReg
      xEqFlag
      (pointAddXDifference workStart)
      (pointAddXHistory workStart);
    loadConst constReg xC.val;

    /- yNegFlag = (y_R = -y_C) -/
    loadConst constReg (-yC).val;
    equalFlag
      (PointRegister.y pointReg)
      constReg
      yNegFlag
      (pointAddYDifference workStart)
      (pointAddYHistory workStart);
    loadConst constReg (-yC).val;

    /- genericFlag = !infinityFlag && !xEqFlag -/
    gate! Gate.X infinityFlag;
    gate! Gate.X xEqFlag;
    gate! Gate.CCX infinityFlag xEqFlag genericFlag;
    gate! Gate.X xEqFlag;
    gate! Gate.X infinityFlag;

    /- pairFlag = xEqFlag && !yNegFlag -/
    gate! Gate.X yNegFlag;
    gate! Gate.CCX xEqFlag yNegFlag pairFlag;
    gate! Gate.X yNegFlag;

    /- doubleFlag = !infinityFlag && pairFlag -/
    gate! Gate.X infinityFlag;
    gate! Gate.CCX infinityFlag pairFlag doubleFlag;
    gate! Gate.X infinityFlag
  }

/-! -------------------------------------------------------------------------
    Candidate branches
------------------------------------------------------------------------- -/

/--
Compute the generic point candidate, conditionally XOR it into `selected`,
then clean the candidate and every field temporary.
-/
def genericPointBranch
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let compute :=
    genericPointCompute workStart xC yC

  let pack :=
    packFinitePoint
      (pointAddT2 workStart)
      (pointAddT4 workStart)
      (pointAddCandidate workStart)

  circuit! {
    compute;
    pack;

    controlledCopyReg
      (pointAddGenericFlag workStart)
      (pointAddCandidate workStart)
      (pointAddSelected workStart);

    pack.reverse;
    compute.reverse
  }

/--
Compute the doubling candidate, conditionally XOR it into `selected`,
then clean the candidate and every field temporary.
-/
def doublePointBranch
    (workStart : Wire) : Circuit :=
  let compute :=
    doublePointCompute workStart

  let pack :=
    packFinitePoint
      (pointAddT2 workStart)
      (pointAddT4 workStart)
      (pointAddCandidate workStart)

  circuit! {
    compute;
    pack;

    controlledCopyReg
      (pointAddDoubleFlag workStart)
      (pointAddCandidate workStart)
      (pointAddSelected workStart);

    pack.reverse;
    compute.reverse
  }

/--
If the input point is infinity, the answer is the classical constant `C`.

The candidate register is loaded with `C`, conditionally copied, and
immediately cleared.
-/
def infinityPointBranch
    (workStart : Wire)
    (C : Point) : Circuit :=
  let candidate := pointAddCandidate workStart
  let load := loadConst candidate (encode C).val
  circuit! {
    load;

    controlledCopyReg
      (pointAddInfinityFlag workStart)
      candidate
      (pointAddSelected workStart);

    load
  }

/-! -------------------------------------------------------------------------
    Complete finite-constant computation
------------------------------------------------------------------------- -/

/-! -------------------------------------------------------------------------
    PointAdd finite computation: proof-oriented decomposition
------------------------------------------------------------------------- -/

-- The setup stage:

-- 1. copy the public x-coordinate into the padded arithmetic x-register;
-- 2. copy the public y-coordinate into the padded arithmetic y-register;
-- 3. compute the branch flags.

-- It does not touch `selected`.

def pointAddCopyX
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  Arithmetic.copyReg
    (PointRegister.x pointReg)
    ((pointAddX workStart).take 256)

def pointAddCopyY
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  Arithmetic.copyReg
    (PointRegister.y pointReg)
    ((pointAddY workStart).take 256)

def pointAddCoordinateCopies
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  pointAddCopyX pointReg workStart ++
    pointAddCopyY pointReg workStart

def pointAddSetup
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) :
    Circuit :=
  pointAddCoordinateCopies pointReg workStart ++
    pointAddFlags pointReg workStart xC yC
/--
The branch stage.

The flags computed by `pointAddSetup` determine which, if any,
candidate is XORed into `selected`.

* genericFlag = 1  -> generic affine addition
* doubleFlag  = 1  -> doubling
* infinityFlag = 1 -> C
* all zero          -> O
-/
def pointAddBranches
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    Circuit :=
  circuit! {
    genericPointBranch workStart xC yC;
    doublePointBranch workStart;
    infinityPointBranch workStart (.some hC)
  }

/--
The portion of PointAdd scratch used by the three candidate branches.

`pointAddX` and `pointAddY` are deliberately not included: they contain
the copied input coordinates rather than zero.
-/
def pointAddBranchWork (workStart : Wire) : List Wire :=
  pointAddT0 workStart ++
  pointAddT1 workStart ++
  pointAddT2 workStart ++
  pointAddT3 workStart ++
  pointAddT4 workStart ++
  pointAddCandidate workStart ++
  pointAddSelected workStart ++
  pointAddArithmeticWork workStart

/-!
The active support of the generic and doubling Bennett branches.  The three
branch-control wires are deliberately absent.  Keeping this support explicit
lets the inactive-branch proofs show that the forward compute cannot change
its own control before the controlled copy is reached.
-/
private def pointAddBranchActiveSupport
    (workStart : Wire) : List Wire :=
  pointAddX workStart ++
    (pointAddY workStart ++
      (pointAddT0 workStart ++
        (pointAddT1 workStart ++
          (pointAddT2 workStart ++
            (pointAddT3 workStart ++
              (pointAddT4 workStart ++
                (pointAddCandidate workStart ++
                  (shiftWires (pointAddArithmeticOffset workStart)
                        Secp256k1Instance.secpAddLayout.allWires ++
                    (shiftWires (pointAddArithmeticOffset workStart)
                          Secp256k1Instance.secpMulLayout.allWires ++
                      shiftWires (pointAddArithmeticOffset workStart)
                        Secp256k1Instance.secpLayout.allWires)))))))))

private theorem pointAddFieldRegister_mem_activeSupport
    (workStart : Wire) (register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register) :
    ∀ w ∈ register, w ∈ pointAddBranchActiveSupport workStart := by
  rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro w hw
    simp [pointAddBranchActiveSupport, hw]

private theorem pointAddAddEngine_mem_activeSupport
    (workStart : Wire) :
    ∀ w ∈ shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpAddLayout.allWires,
      w ∈ pointAddBranchActiveSupport workStart := by
  intro w hw
  simp [pointAddBranchActiveSupport, hw]

private theorem pointAddMulEngine_mem_activeSupport
    (workStart : Wire) :
    ∀ w ∈ shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpMulLayout.allWires,
      w ∈ pointAddBranchActiveSupport workStart := by
  intro w hw
  simp [pointAddBranchActiveSupport, hw]

private theorem pointAddInvEngine_mem_activeSupport
    (workStart : Wire) :
    ∀ w ∈ shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpLayout.allWires,
      w ∈ pointAddBranchActiveSupport workStart := by
  intro w hw
  simp [pointAddBranchActiveSupport, hw]

private theorem fieldAdd_usesOnly_pointAdd
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (fieldAdd (pointAddArithmeticOffset workStart) lhs rhs out) := by
  apply usesOnly_mono (fieldAdd_usesOnly _ lhs rhs out)
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with ((hlhs' | hrhs') | hout') | hengine
  · exact pointAddFieldRegister_mem_activeSupport
      workStart lhs hlhs w hlhs'
  · exact pointAddFieldRegister_mem_activeSupport
      workStart rhs hrhs w hrhs'
  · exact pointAddFieldRegister_mem_activeSupport
      workStart out hout w hout'
  · exact pointAddAddEngine_mem_activeSupport workStart w hengine

private theorem fieldSub_usesOnly_pointAdd
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (fieldSub (pointAddArithmeticOffset workStart) lhs rhs out) := by
  apply usesOnly_mono (fieldSub_usesOnly _ lhs rhs out)
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with ((hlhs' | hrhs') | hout') | hengine
  · exact pointAddFieldRegister_mem_activeSupport
      workStart lhs hlhs w hlhs'
  · exact pointAddFieldRegister_mem_activeSupport
      workStart rhs hrhs w hrhs'
  · exact pointAddFieldRegister_mem_activeSupport
      workStart out hout w hout'
  · exact pointAddAddEngine_mem_activeSupport workStart w hengine

private theorem fieldSubConst_usesOnly_pointAdd
    (workStart : Wire) (lhs : List Wire) (constant : Nat)
    (out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (fieldSubConst (pointAddArithmeticOffset workStart)
        lhs constant out) := by
  apply usesOnly_mono (fieldSubConst_usesOnly _ lhs constant out)
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with (hlhs' | hout') | hengine
  · exact pointAddFieldRegister_mem_activeSupport
      workStart lhs hlhs w hlhs'
  · exact pointAddFieldRegister_mem_activeSupport
      workStart out hout w hout'
  · exact pointAddAddEngine_mem_activeSupport workStart w hengine

private theorem fieldMul_usesOnly_pointAdd
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (fieldMul (pointAddArithmeticOffset workStart) lhs rhs out) := by
  apply usesOnly_mono (fieldMul_usesOnly _ lhs rhs out)
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with ((hlhs' | hrhs') | hout') | hengine
  · exact pointAddFieldRegister_mem_activeSupport
      workStart lhs hlhs w hlhs'
  · exact pointAddFieldRegister_mem_activeSupport
      workStart rhs hrhs w hrhs'
  · exact pointAddFieldRegister_mem_activeSupport
      workStart out hout w hout'
  · exact pointAddMulEngine_mem_activeSupport workStart w hengine

private theorem fieldInv_usesOnly_pointAdd
    (workStart : Wire) (input out : List Wire)
    (hinput : IsPointAddFieldRegister workStart input)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (fieldInv (pointAddArithmeticOffset workStart) input out) := by
  apply usesOnly_mono (fieldInv_usesOnly _ input out)
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with (hinput' | hout') | hengine
  · exact pointAddFieldRegister_mem_activeSupport
      workStart input hinput w hinput'
  · exact pointAddFieldRegister_mem_activeSupport
      workStart out hout w hout'
  · exact pointAddInvEngine_mem_activeSupport workStart w hengine

private theorem circuitUsesOnly_append_iff
    {support : List Wire} {left right : Circuit} :
    CircuitUsesOnly support (left ++ right) ↔
      CircuitUsesOnly support left ∧
        CircuitUsesOnly support right := by
  constructor
  · intro h
    constructor
    · intro g hg
      exact h g (List.mem_append.mpr (Or.inl hg))
    · intro g hg
      exact h g (List.mem_append.mpr (Or.inr hg))
  · rintro ⟨hleft, hright⟩
    exact usesOnly_append hleft hright

private theorem circuitUsesOnly_reverse_iff
    {support : List Wire} {circuit : Circuit} :
    CircuitUsesOnly support circuit.reverse ↔
      CircuitUsesOnly support circuit := by
  constructor
  · intro h
    have hreverse := usesOnly_reverse h
    simpa using hreverse
  · exact usesOnly_reverse

private theorem packFinitePoint_usesOnly
    (x y point : List Wire) :
    CircuitUsesOnly (x ++ y ++ point)
      (packFinitePoint x y point) := by
  let support := x ++ y ++ point
  have hx : ∀ w ∈ x, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hy : ∀ w ∈ y, w ∈ support := by
    intro w hw
    simp [support, hw]
  have hpoint : ∀ w ∈ point, w ∈ support := by
    intro w hw
    simp [support, hw]
  have htag :
      ∀ w ∈ PointRegister.tag point, w ∈ support := by
    intro w hw
    exact hpoint w (List.mem_of_mem_take hw)
  have hxTake : ∀ w ∈ x.take 256, w ∈ support := by
    intro w hw
    exact hx w (List.mem_of_mem_take hw)
  have hyTake : ∀ w ∈ y.take 256, w ∈ support := by
    intro w hw
    exact hy w (List.mem_of_mem_take hw)
  have hpointX :
      ∀ w ∈ PointRegister.x point, w ∈ support := by
    intro w hw
    apply hpoint w
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have hpointY :
      ∀ w ∈ PointRegister.y point, w ∈ support := by
    intro w hw
    apply hpoint w
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have hload := usesOnly_mono
    (loadConst_usesOnly (PointRegister.tag point) 1) htag
  have hcopyX := Arithmetic.copyReg_usesOnly
    (x.take 256) (PointRegister.x point) support
    hxTake hpointX
  have hcopyY := Arithmetic.copyReg_usesOnly
    (y.take 256) (PointRegister.y point) support
    hyTake hpointY
  simpa [packFinitePoint, support] using
    usesOnly_append (usesOnly_append hload hcopyX) hcopyY

private theorem packFinitePoint_usesOnly_pointAdd
    (workStart : Wire) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (packFinitePoint
        (pointAddT2 workStart)
        (pointAddT4 workStart)
        (pointAddCandidate workStart)) := by
  apply usesOnly_mono (packFinitePoint_usesOnly
    (pointAddT2 workStart)
    (pointAddT4 workStart)
    (pointAddCandidate workStart))
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with (ht2 | ht4) | hcandidate
  · exact pointAddFieldRegister_mem_activeSupport
      workStart (pointAddT2 workStart)
      (by simp [IsPointAddFieldRegister]) w ht2
  · exact pointAddFieldRegister_mem_activeSupport
      workStart (pointAddT4 workStart)
      (by simp [IsPointAddFieldRegister]) w ht4
  · simp [pointAddBranchActiveSupport, hcandidate]

private theorem genericPointCompute_usesOnly
    (workStart : Wire) (xC yC : Fp) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (genericPointCompute workStart xC yC) := by
  simp [genericPointCompute, circuitUsesOnly_append_iff,
    circuitUsesOnly_reverse_iff,
    fieldSubConst_usesOnly_pointAdd,
    fieldInv_usesOnly_pointAdd,
    fieldMul_usesOnly_pointAdd,
    fieldSub_usesOnly_pointAdd,
    IsPointAddFieldRegister]

private theorem threeXSquared_usesOnly_pointAdd
    (workStart : Wire)
    (x scratch₀ scratch₁ out : List Wire)
    (hx : IsPointAddFieldRegister workStart x)
    (hscratch₀ : IsPointAddFieldRegister workStart scratch₀)
    (hscratch₁ : IsPointAddFieldRegister workStart scratch₁)
    (hout : IsPointAddFieldRegister workStart out) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (threeXSquared (pointAddArithmeticOffset workStart)
        x scratch₀ scratch₁ out) := by
  simp [threeXSquared, circuitUsesOnly_append_iff,
    circuitUsesOnly_reverse_iff, fieldMul_usesOnly_pointAdd,
    fieldAdd_usesOnly_pointAdd, hx, hscratch₀, hscratch₁, hout]

private theorem doublePointCompute_usesOnly
    (workStart : Wire) :
    CircuitUsesOnly (pointAddBranchActiveSupport workStart)
      (doublePointCompute workStart) := by
  simp [doublePointCompute, circuitUsesOnly_append_iff,
    circuitUsesOnly_reverse_iff, threeXSquared_usesOnly_pointAdd,
    fieldAdd_usesOnly_pointAdd, fieldInv_usesOnly_pointAdd,
    fieldMul_usesOnly_pointAdd, fieldSub_usesOnly_pointAdd,
    IsPointAddFieldRegister]

private theorem pointAddFieldRegister_belowFlagArea
    (workStart : Wire) (register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register) :
    ∀ w ∈ register, w < workStart + flagOffset := by
  intro w hw
  rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hbounds := List.mem_range'_1.mp hw
    apply hbounds.2.trans_le
    norm_num [pointAddX, pointAddY, pointAddT0, pointAddT1,
      pointAddT2, pointAddT3, pointAddT4, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

private theorem pointAddControl_not_mem_activeSupport
    (workStart index : Wire) (hindex : index < 6) :
    workStart + flagOffset + index ∉
      pointAddBranchActiveSupport workStart := by
  intro hmem
  have hcontrolLower :
      workStart + flagOffset ≤ workStart + flagOffset + index := by
    exact Nat.le_add_right (workStart + flagOffset) index
  have hcontrolUpper :
      workStart + flagOffset + index <
        workStart + candidateOffset := by
    simpa [candidateOffset, Nat.add_assoc] using
      Nat.add_lt_add_left hindex (workStart + flagOffset)
  simp only [pointAddBranchActiveSupport, List.mem_append] at hmem
  rcases hmem with hx | hy | ht0 | ht1 | ht2 | ht3 | ht4 |
      hcandidate | hadd | hmul | hinv
  · exact (Nat.not_lt_of_ge hcontrolLower)
      (pointAddFieldRegister_belowFlagArea workStart
        (pointAddX workStart)
        (by simp [IsPointAddFieldRegister]) _ hx)
  · exact (Nat.not_lt_of_ge hcontrolLower)
      (pointAddFieldRegister_belowFlagArea workStart
        (pointAddY workStart)
        (by simp [IsPointAddFieldRegister]) _ hy)
  · exact (Nat.not_lt_of_ge hcontrolLower)
      (pointAddFieldRegister_belowFlagArea workStart
        (pointAddT0 workStart)
        (by simp [IsPointAddFieldRegister]) _ ht0)
  · exact (Nat.not_lt_of_ge hcontrolLower)
      (pointAddFieldRegister_belowFlagArea workStart
        (pointAddT1 workStart)
        (by simp [IsPointAddFieldRegister]) _ ht1)
  · exact (Nat.not_lt_of_ge hcontrolLower)
      (pointAddFieldRegister_belowFlagArea workStart
        (pointAddT2 workStart)
        (by simp [IsPointAddFieldRegister]) _ ht2)
  · exact (Nat.not_lt_of_ge hcontrolLower)
      (pointAddFieldRegister_belowFlagArea workStart
        (pointAddT3 workStart)
        (by simp [IsPointAddFieldRegister]) _ ht3)
  · exact (Nat.not_lt_of_ge hcontrolLower)
      (pointAddFieldRegister_belowFlagArea workStart
        (pointAddT4 workStart)
        (by simp [IsPointAddFieldRegister]) _ ht4)
  · have hbounds := List.mem_range'_1.mp hcandidate
    exact (Nat.not_le_of_gt hcontrolUpper) hbounds.1
  · have hlower := shiftWires_lower
        (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpAddLayout.allWires _ hadd
    have hcandidateBeforeArithmetic :
        workStart + candidateOffset ≤
          pointAddArithmeticOffset workStart := by
      rw [pointAddArithmeticOffset, localWorkSize_eq]
      norm_num [candidateOffset, flagOffset, yHistoryOffset,
        yDifferenceOffset, xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth]
    exact (Nat.not_le_of_gt hcontrolUpper)
      (hcandidateBeforeArithmetic.trans hlower)
  · have hlower := shiftWires_lower
        (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpMulLayout.allWires _ hmul
    have hcandidateBeforeArithmetic :
        workStart + candidateOffset ≤
          pointAddArithmeticOffset workStart := by
      rw [pointAddArithmeticOffset, localWorkSize_eq]
      norm_num [candidateOffset, flagOffset, yHistoryOffset,
        yDifferenceOffset, xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth]
    exact (Nat.not_le_of_gt hcontrolUpper)
      (hcandidateBeforeArithmetic.trans hlower)
  · have hlower := shiftWires_lower
        (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpLayout.allWires _ hinv
    have hcandidateBeforeArithmetic :
        workStart + candidateOffset ≤
          pointAddArithmeticOffset workStart := by
      rw [pointAddArithmeticOffset, localWorkSize_eq]
      norm_num [candidateOffset, flagOffset, yHistoryOffset,
        yDifferenceOffset, xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth]
    exact (Nat.not_le_of_gt hcontrolUpper)
      (hcandidateBeforeArithmetic.trans hlower)

private theorem pointAddInfinityFlag_not_mem_activeSupport
    (workStart : Wire) :
    pointAddInfinityFlag workStart ∉
      pointAddBranchActiveSupport workStart := by
  simpa [pointAddInfinityFlag] using
    pointAddControl_not_mem_activeSupport workStart 0 (by norm_num)

private theorem pointAddGenericFlag_not_mem_activeSupport
    (workStart : Wire) :
    pointAddGenericFlag workStart ∉
      pointAddBranchActiveSupport workStart := by
  simpa [pointAddGenericFlag, Nat.add_assoc] using
    pointAddControl_not_mem_activeSupport workStart 3 (by norm_num)

private theorem pointAddDoubleFlag_not_mem_activeSupport
    (workStart : Wire) :
    pointAddDoubleFlag workStart ∉
      pointAddBranchActiveSupport workStart := by
  simpa [pointAddDoubleFlag, Nat.add_assoc] using
    pointAddControl_not_mem_activeSupport workStart 5 (by norm_num)

private theorem run_inactive_bennett_branch
    (active : Circuit) (control : Wire)
    (src dst support : List Wire) (st : BasisState)
    (hfree : Classical.HPFree active)
    (hwellFormed : CircuitWellFormed active)
    (huses : CircuitUsesOnly support active)
    (hcontrolOutside : control ∉ support)
    (hcontrol : st control = false) :
    Classical.run
        (circuit! {
          active;
          controlledCopyReg control src dst;
          active.reverse
        }) st =
      st := by
  have hcontrolAfter :
      Classical.run active st control = false := by
    rw [huses.preservesOutside st control hcontrolOutside]
    exact hcontrol
  simp only [Classical.run_append]
  rw [run_controlledCopyReg_false control src dst
    (Classical.run active st) hcontrolAfter]
  exact Arithmetic.run_reverse_cancel active st hfree hwellFormed

private theorem genericPointBranch_false
    (workStart : Wire) (xC yC : Fp) (st : BasisState)
    (hcontrol : st (pointAddGenericFlag workStart) = false) :
    Classical.run (genericPointBranch workStart xC yC) st = st := by
  let active :=
    genericPointCompute workStart xC yC ++
      packFinitePoint
        (pointAddT2 workStart)
        (pointAddT4 workStart)
        (pointAddCandidate workStart)
  have hfree : Classical.HPFree active := by
    simp [active, genericPointCompute_HPFree, packFinitePoint_HPFree]
  have hwellFormed : CircuitWellFormed active := by
    simp [active, genericPointCompute_wellFormed,
      packFinitePoint_wellFormed]
  have huses :
      CircuitUsesOnly (pointAddBranchActiveSupport workStart) active :=
    usesOnly_append
      (genericPointCompute_usesOnly workStart xC yC)
      (packFinitePoint_usesOnly_pointAdd workStart)
  have hcancel := run_inactive_bennett_branch
    active (pointAddGenericFlag workStart)
    (pointAddCandidate workStart)
    (pointAddSelected workStart)
    (pointAddBranchActiveSupport workStart) st
    hfree hwellFormed huses
    (pointAddGenericFlag_not_mem_activeSupport workStart)
    hcontrol
  simpa [genericPointBranch, active, List.append_assoc] using hcancel

private theorem doublePointBranch_false
    (workStart : Wire) (st : BasisState)
    (hcontrol : st (pointAddDoubleFlag workStart) = false) :
    Classical.run (doublePointBranch workStart) st = st := by
  let active :=
    doublePointCompute workStart ++
      packFinitePoint
        (pointAddT2 workStart)
        (pointAddT4 workStart)
        (pointAddCandidate workStart)
  have hfree : Classical.HPFree active := by
    simp [active, doublePointCompute_HPFree, packFinitePoint_HPFree]
  have hwellFormed : CircuitWellFormed active := by
    simp [active, doublePointCompute_wellFormed,
      packFinitePoint_wellFormed]
  have huses :
      CircuitUsesOnly (pointAddBranchActiveSupport workStart) active :=
    usesOnly_append
      (doublePointCompute_usesOnly workStart)
      (packFinitePoint_usesOnly_pointAdd workStart)
  have hcancel := run_inactive_bennett_branch
    active (pointAddDoubleFlag workStart)
    (pointAddCandidate workStart)
    (pointAddSelected workStart)
    (pointAddBranchActiveSupport workStart) st
    hfree hwellFormed huses
    (pointAddDoubleFlag_not_mem_activeSupport workStart)
    hcontrol
  simpa [doublePointBranch, active, List.append_assoc] using hcancel

private theorem infinityPointBranch_true_value
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hcontrol : st (pointAddInfinityFlag workStart) = true)
    (hclean : Clean (pointAddBranchWork workStart) st) :
    regValue (pointAddSelected workStart)
        (Classical.run
          (infinityPointBranch workStart (.some hC)) st) =
      encodeNat (.some hC) := by
  let candidate := pointAddCandidate workStart
  let selected := pointAddSelected workStart
  let constant := (encode (.some hC)).val
  have hcandidateClean : Clean candidate st := by
    apply Arithmetic.Clean.mono hclean
    intro w hw
    simp [candidate, pointAddBranchWork, hw]
  have hselectedClean : Clean selected st := by
    apply Arithmetic.Clean.mono hclean
    intro w hw
    simp [selected, pointAddBranchWork, hw]
  have hcandidateNodup : candidate.Nodup := by
    dsimp [candidate, pointAddCandidate]
    exact List.nodup_range'
  have hcandidateSelectedNodup :
      (candidate ++ selected).Nodup := by
    simpa [candidate, selected, pointAddCandidate,
      pointAddSelected] using
      (range'_append_nodup_of_le
        (workStart + candidateOffset) pointWidth
        (workStart + selectedOffset) pointWidth
        (by
          unfold selectedOffset
          omega))
  have hcontrolNotCandidate :
      pointAddInfinityFlag workStart ∉ candidate := by
    intro hw
    exact pointAddInfinityFlag_not_mem_activeSupport workStart (by
      simp [candidate, pointAddBranchActiveSupport, hw])
  have hcontrolNotSelected :
      pointAddInfinityFlag workStart ∉ selected := by
    intro hw
    have hbounds := List.mem_range'_1.mp hw
    norm_num [pointAddInfinityFlag, selected, pointAddSelected,
      selectedOffset, candidateOffset, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset,
      fieldAreaSize, fieldWidth, Secp256k1Instance.fieldWidth,
      pointWidth] at hbounds
  have hcontrolNotCandidateSelected :
      pointAddInfinityFlag workStart ∉ candidate ++ selected := by
    intro hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hcontrolNotCandidate hw
    · exact hcontrolNotSelected hw
  have hcontrolledNodup :
      (pointAddInfinityFlag workStart ::
        candidate ++ selected).Nodup :=
    List.nodup_cons.mpr
      ⟨hcontrolNotCandidateSelected, hcandidateSelectedNodup⟩
  have hcross := (List.nodup_append.mp
    hcandidateSelectedNodup).2.2
  have hselectedNotCandidate :
      ∀ w ∈ selected, w ∉ candidate := by
    intro w hselected hcandidate
    exact hcross w hcandidate w hselected rfl
  have hbound : constant < 2 ^ candidate.length := by
    change (encode (.some hC)).val < 2 ^ candidate.length
    rw [encode_val]
    rw [show candidate.length = pointWidth by
      simp [candidate, pointAddCandidate]]
    exact encodeNat_lt (.some hC)
  let loaded := Classical.run (loadConst candidate constant) st
  have hcandidateValue :
      regValue candidate loaded = encodeNat (.some hC) := by
    have hload := loadConst_correct candidate constant st
      hcandidateNodup hcandidateClean hbound
    calc
      regValue candidate loaded = constant := by
        simpa only [loaded] using hload
      _ = encodeNat (.some hC) := by
        simp only [constant, encode_val]
  have hselectedCleanLoaded : Clean selected loaded := by
    intro w hw
    change Classical.run (loadConst candidate constant) st w = false
    rw [loadConst_other w candidate constant st
      (hselectedNotCandidate w hw)]
    exact hselectedClean w hw
  have hcontrolLoaded :
      loaded (pointAddInfinityFlag workStart) = true := by
    change Classical.run (loadConst candidate constant) st
      (pointAddInfinityFlag workStart) = true
    rw [loadConst_other
      (pointAddInfinityFlag workStart) candidate constant st
      hcontrolNotCandidate]
    exact hcontrol
  let copied :=
    Classical.run
      (controlledCopyReg
        (pointAddInfinityFlag workStart) candidate selected)
      loaded
  have hcontrolled :
      copied =
        Classical.run (Arithmetic.copyReg candidate selected) loaded := by
    exact run_controlledCopyReg_true
      (pointAddInfinityFlag workStart) candidate selected loaded
      hcontrolledNodup hcontrolLoaded
  have hlength : selected.length = candidate.length := by
    simp [selected, candidate, pointAddSelected, pointAddCandidate]
  have hcopiedValue :
      regValue selected copied = encodeNat (.some hC) := by
    calc
      regValue selected copied =
          regValue selected
            (Classical.run (Arithmetic.copyReg candidate selected)
              loaded) := by rw [hcontrolled]
      _ = regValue candidate loaded :=
        Arithmetic.copyReg_correct candidate selected loaded
          hlength hcandidateSelectedNodup hselectedCleanLoaded
      _ = encodeNat (.some hC) := hcandidateValue
  have hfinalValue :
      regValue selected
          (Classical.run (loadConst candidate constant) copied) =
        encodeNat (.some hC) := by
    rw [loadConst_regValue selected candidate constant copied
      hselectedNotCandidate]
    exact hcopiedValue
  simpa only [infinityPointBranch, candidate, selected, constant,
    loaded, copied, Classical.run_append] using hfinalValue

/--
The finite computation is exactly setup followed by the candidate branches.
-/
def pointAddFiniteCompute
    (pointReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    Circuit :=
  pointAddSetup pointReg workStart xC yC ++
    pointAddBranches workStart hC

/-! -------------------------------------------------------------------------
    HP-free structure
------------------------------------------------------------------------- -/

theorem pointAddFlags_HPFree
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) :
    Classical.HPFree (pointAddFlags pointReg workStart xC yC) := by
  simp [pointAddFlags, zeroFlag_HPFree, equalFlag_HPFree,
    loadConst_HPFree]

theorem pointAddCoordinateCopies_HPFree
    (pointReg : List Wire)
    (workStart : Wire) :
    Classical.HPFree (pointAddCoordinateCopies pointReg workStart) := by
  simp [pointAddCoordinateCopies, pointAddCopyX, pointAddCopyY,
    Arithmetic.copyReg_HPFree]

theorem pointAddSetup_HPFree
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) :
    Classical.HPFree (pointAddSetup pointReg workStart xC yC) := by
  simp [pointAddSetup, pointAddCoordinateCopies_HPFree,
    pointAddFlags_HPFree]

theorem genericPointBranch_HPFree
    (workStart : Wire)
    (xC yC : Fp) :
    Classical.HPFree (genericPointBranch workStart xC yC) := by
  simp [genericPointBranch, genericPointCompute_HPFree,
    packFinitePoint_HPFree, controlledCopyReg_HPFree,
    Arithmetic.hpFree_reverse]

theorem doublePointBranch_HPFree
    (workStart : Wire) :
    Classical.HPFree (doublePointBranch workStart) := by
  simp [doublePointBranch, doublePointCompute_HPFree,
    packFinitePoint_HPFree, controlledCopyReg_HPFree,
    Arithmetic.hpFree_reverse]

theorem infinityPointBranch_HPFree
    (workStart : Wire)
    (C : Point) :
    Classical.HPFree (infinityPointBranch workStart C) := by
  rw [infinityPointBranch]
  simp only [Classical.hpFree_append]
  exact
    ⟨⟨loadConst_HPFree _ _,
      controlledCopyReg_HPFree _ _ _⟩,
      loadConst_HPFree _ _⟩

theorem pointAddBranches_HPFree
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    Classical.HPFree (pointAddBranches workStart hC) := by
  simp [pointAddBranches, genericPointBranch_HPFree,
    doublePointBranch_HPFree, infinityPointBranch_HPFree]

theorem pointAddFiniteCompute_HPFree
    (pointReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    Classical.HPFree
      (pointAddFiniteCompute pointReg workStart hC) := by
  simp [pointAddFiniteCompute, pointAddSetup_HPFree,
    pointAddBranches_HPFree]

/-! -------------------------------------------------------------------------
    Public PointAdd operation
------------------------------------------------------------------------- -/

/--
Clean out-of-place addition by a classical point.

For `C = O`, addition is just a register copy.

For finite `C`, first compute `R + C` into the private `selected` register,
copy it to `outReg`, and reverse the complete computation.

Thus the intended action is

    |R⟩ |0_out⟩ |0_work⟩
      ↦
    |R⟩ |R+C⟩ |0_work⟩.
-/
def pointAdd
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C : Point) :
    Circuit :=
  match C with
  | .zero =>
      Arithmetic.copyReg pointReg outReg

  | @WeierstrassCurve.Affine.Point.some _ _ _ _xC _yC hC =>
      let compute :=
        pointAddFiniteCompute pointReg workStart hC
      circuit! {
        compute;

        Arithmetic.copyReg
          (pointAddSelected workStart)
          outReg;

        compute.reverse
      }

/-! -------------------------------------------------------------------------
    Correctness proof decomposition

There are three genuinely different proof obligations.

1. `pointAddFiniteCompute_correct`
   Prove the actual elliptic-curve arithmetic: after the forward computation,
   `selected` contains `affineAdd R C`.

2. `pointAddFiniteCompute_structural`
   Prove that the forward circuit is a valid classical reversible computation,
   is confined to the PointAdd input/workspace, and that `selected` is part of
   that workspace.

3. `bennett_copyReg_eq_writeReg`
   A generic reversible-computing lemma: if `compute` produces a value in a
   scratch register, copying that value to a clean output and reversing
   `compute` leaves exactly that output written into the original state.

The final theorem then contains essentially no elliptic-curve arithmetic.
------------------------------------------------------------------------- -/

/--
Exact register copying.

If `src` contains `value` and `dst` is a clean, disjoint register of the
same width, then CNOT-copying `src` to `dst` has exactly the same whole-state
effect as `writeReg dst value`.

This is useful both for the `C = O` case and inside the Bennett argument.
-/
theorem copyReg_eq_writeReg_of_value
    (src dst work : List Wire)
    (st : BasisState)
    (value : Nat)
    (hlen : dst.length = src.length)
    (hnodup : (src ++ dst ++ work).Nodup)
    (hclean : Clean dst st)
    (hvalue : regValue src st = value)
    (_hbound : value < 2 ^ dst.length) :
    Classical.run (Arithmetic.copyReg src dst) st =
      writeReg dst value st := by
  have aux :
      ∀ (src dst : List Wire) (st : BasisState),
        dst.length = src.length →
        (src ++ dst).Nodup →
        Clean dst st →
        Classical.run (Arithmetic.copyReg src dst) st =
          writeReg dst (regValue src st) st := by
    intro src
    induction src with
    | nil =>
        intro dst st hlen hnd hclean
        have hdst : dst = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using hlen
        subst dst
        rfl
    | cons s src ih =>
        intro dst st hlen hnd hclean
        cases dst with
        | nil =>
            simp at hlen
        | cons d dst =>
            have hlenTail : dst.length = src.length := by
              simpa using hlen

            obtain ⟨hsrcNd, hdstNd, hcross⟩ :=
              List.nodup_append.mp hnd
            obtain ⟨_, hsrcTailNd⟩ :=
              List.nodup_cons.mp hsrcNd
            obtain ⟨hdDst, hdstTailNd⟩ :=
              List.nodup_cons.mp hdstNd

            have htailNd : (src ++ dst).Nodup :=
              List.nodup_append.mpr
                ⟨hsrcTailNd, hdstTailNd,
                  fun a ha b hb =>
                    hcross a
                      (List.mem_cons_of_mem s ha)
                      b
                      (List.mem_cons_of_mem d hb)⟩

            have hdSrc : d ∉ src := by
              intro hd
              exact
                (hcross d
                  (List.mem_cons_of_mem s hd)
                  d
                  (List.mem_cons_self)) rfl

            let st₁ := Classical.applyGate (Gate.CX s d) st

            have hcleanTail : Clean dst st₁ := by
              intro w hw
              change
                st[d ↦ Bool.xor (st d) (st s)] w = false
              have hwd : w ≠ d := by
                intro h
                subst w
                exact hdDst hw
              rw [upd_other _ _ _ hwd]
              exact hclean w (List.mem_cons_of_mem d hw)

            have hsrcKeep :
                regValue src st₁ = regValue src st := by
              change
                regValue src
                    (st[d ↦ Bool.xor (st d) (st s)]) =
                  regValue src st
              exact
                regValue_upd_not_mem src st d
                  (Bool.xor (st d) (st s)) hdSrc

            have hbit :
                (regValue (s :: src) st).testBit 0 = st s := by
              rw [regValue_cons, Nat.testBit_zero]
              cases hs : st s <;>
                simp [ Nat.add_mod]

            have hdiv :
                regValue (s :: src) st / 2 =
                  regValue src st := by
              rw [regValue_cons]
              cases hs : st s <;> simp ; omega

            have hst₁ :
                st₁ =
                  st[d ↦
                    (regValue (s :: src) st).testBit 0] := by
              simp only [st₁, Classical.applyGate]
              rw [hclean d (List.mem_cons_self)]
              simp [hbit]

            have hih :=
              ih dst st₁ hlenTail htailNd hcleanTail

            rw [Arithmetic.copyReg, Classical.run_cons]
            change
              Classical.run (Arithmetic.copyReg src dst) st₁ =
                writeReg (d :: dst)
                  (regValue (s :: src) st) st
            rw [hih, hsrcKeep, writeReg, hdiv, ← hst₁]

  have hnd : (src ++ dst).Nodup :=
    (List.nodup_append.mp hnodup).1

  calc
    Classical.run (Arithmetic.copyReg src dst) st =
        writeReg dst (regValue src st) st :=
      aux src dst st hlen hnd hclean
    _ = writeReg dst value st := by rw [hvalue]


def pointAddFlagWork (workStart : Wire) : List Wire :=
  pointAddConst workStart ++
  pointAddZeroHistory workStart ++
  pointAddXDifference workStart ++
  pointAddXHistory workStart ++
  pointAddYDifference workStart ++
  pointAddYHistory workStart ++
  [
    pointAddInfinityFlag workStart,
    pointAddXEqFlag workStart,
    pointAddYNegFlag workStart,
    pointAddGenericFlag workStart,
    pointAddPairFlag workStart,
    pointAddDoubleFlag workStart
  ]

theorem pointAddCopyX_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run (pointAddCopyX pointReg workStart) st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        after := by
  dsimp

  have hlocalSizeEq : localWorkSize = 4112 := by
    norm_num [localWorkSize, selectedOffset, candidateOffset, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth, pointWidth]

  have hlocalSize : 257 ≤ localWorkSize := by omega

  have hdstEq :
      (pointAddX workStart).take 256 =
        List.range' workStart 256 := by
    simp [pointAddX, fieldWidth, Secp256k1Instance.fieldWidth,
      List.take_range'_of_length_ge]

  have hdstWork :
      ∀ w ∈ (pointAddX workStart).take 256,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [hdstEq] at hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    exact List.mem_range'_1.mpr ⟨hbounds.1, by omega⟩

  have hsrcMem :
      ∀ w ∈ PointRegister.x pointReg, w ∈ pointReg := by
    intro w hw
    change w ∈ (pointReg.drop 1).take 256 at hw
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)

  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup

  have hsrcNodup : (PointRegister.x pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 1)).trans
        (List.drop_sublist 1 pointReg))
    exact hpointNodup

  have hdstNodup : ((pointAddX workStart).take 256).Nodup := by
    rw [hdstEq]
    exact List.nodup_range'

  have hcopyNodup :
      (PointRegister.x pointReg ++
        (pointAddX workStart).take 256).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hsrcNodup, hdstNodup, ?_⟩
    intro a ha b hb
    exact hpublicWork a
      (List.mem_append_left outReg (hsrcMem a ha))
      b (hdstWork b hb)

  have hdstClean :
      Clean ((pointAddX workStart).take 256) st :=
    Arithmetic.Clean.mono hclean hdstWork

  have hcopyValue :
      regValue ((pointAddX workStart).take 256)
          (Classical.run (pointAddCopyX pointReg workStart) st) =
        regValue (PointRegister.x pointReg) st := by
    simpa only [pointAddCopyX] using
      (Arithmetic.copyReg_correct
        (PointRegister.x pointReg)
        ((pointAddX workStart).take 256)
        st
        (by
          rw [hdstEq]
          simpa using
            (PointRegister.x_length pointReg hpointLength).symm)
        hcopyNodup hdstClean)

  have hother (w : Wire)
      (hw : w ∉ (pointAddX workStart).take 256) :
      Classical.run (pointAddCopyX pointReg workStart) st w = st w := by
    simpa only [pointAddCopyX] using
      (Arithmetic.copyReg_other w
        (PointRegister.x pointReg)
        ((pointAddX workStart).take 256) st hw)

  have hpointAgree :
      AgreesOn pointReg st
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    apply hother
    intro hdst
    exact
      (hpublicWork w (List.mem_append_left outReg hw)
        w (hdstWork w hdst)) rfl

  have hhighNotDst :
      workStart + 256 ∉ (pointAddX workStart).take 256 := by
    rw [hdstEq]
    simp [List.mem_range'_1]

  have hhighWork : workStart + 256 ∈ pointAddWork workStart := by
    rw [pointAddWork]
    apply List.mem_append_left
    exact List.mem_range'_1.mpr ⟨by omega, by omega⟩

  have hhighClean :
      Clean [workStart + 256]
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    rw [hother (workStart + 256) hhighNotDst]
    exact hclean (workStart + 256) hhighWork

  have hpointAddXShape :
      pointAddX workStart =
        PointRegister.padCoordinate
          ((pointAddX workStart).take 256)
          (workStart + 256) := by
    rw [PointRegister.padCoordinate, hdstEq]
    change
      List.range' workStart 257 =
        List.range' workStart 256 ++ [workStart + 256]
    simpa using
      (List.range'_concat (s := workStart) (n := 256) (step := 1))

  have hxValue :
      regValue (pointAddX workStart)
          (Classical.run (pointAddCopyX pointReg workStart) st) =
        regValue (PointRegister.x pointReg) st := by
    rw [hpointAddXShape]
    exact
      (PointRegister.regValue_padCoordinate_of_clean
        ((pointAddX workStart).take 256)
        (workStart + 256)
        (Classical.run (pointAddCopyX pointReg workStart) st)
        hhighClean).trans hcopyValue

  have rangeBounds
      (offset len : Nat)
      {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmin : 257 ≤ offset)
      (hmax : offset + len ≤ 4112) :
      workStart + 257 ≤ w ∧ w < workStart + 4112 := by
    constructor
    · exact (Nat.add_le_add_left hmin workStart).trans hw.1
    · apply hw.2.trans_le
      simpa [Nat.add_assoc] using
        (Nat.add_le_add_left hmax workStart)

  have wireBounds
      (offset : Nat)
      {w : Wire}
      (hw : w = workStart + offset)
      (hmin : 257 ≤ offset)
      (hmax : offset < 4112) :
      workStart + 257 ≤ w ∧ w < workStart + 4112 := by
    subst w
    exact
      ⟨Nat.add_le_add_left hmin workStart,
        Nat.add_lt_add_left hmax workStart⟩

  have hremainingFacts :
      ∀ w ∈
          (pointAddY workStart ++
            pointAddFlagWork workStart ++
            pointAddBranchWork workStart),
        workStart + 257 ≤ w ∧ w ∈ pointAddWork workStart := by
    intro w hw
    rcases List.mem_append.mp hw with hyFlag | hbranch
    · rcases List.mem_append.mp hyFlag with hy | hflag
      · have hyRaw :
            workStart + 257 ≤ w ∧ w < workStart + 257 + 257 := by
          simpa [pointAddY, fieldWidth,
            Secp256k1Instance.fieldWidth] using
            (List.mem_range'_1.mp hy)
        have hbounds :=
          rangeBounds 257 257 hyRaw (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
      · have hbounds :
            workStart + 257 ≤ w ∧ w < workStart + 4112 := by
          simp only [pointAddFlagWork, pointAddConst,
            pointAddZeroHistory, pointAddXDifference,
            pointAddXHistory, pointAddYDifference,
            pointAddYHistory, pointAddInfinityFlag,
            pointAddXEqFlag, pointAddYNegFlag,
            pointAddGenericFlag, pointAddPairFlag,
            pointAddDoubleFlag, List.mem_append,
            List.mem_cons,
            List.mem_range'_1] at hflag
          norm_num [localWorkSize, selectedOffset, candidateOffset,
            flagOffset, yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth, pointWidth] at hflag
          rcases hflag with
              (((((h0 | h1) | h2) | h3) | h4) | h5) |
                (h6 | h7 | h8 | h9 | h10 | h11)
          · exact rangeBounds 1799 256 h0 (by omega) (by omega)
          · exact wireBounds 2055 h1 (by omega) (by omega)
          · exact rangeBounds 2056 256 h2 (by omega) (by omega)
          · exact rangeBounds 2312 256 h3 (by omega) (by omega)
          · exact rangeBounds 2568 256 h4 (by omega) (by omega)
          · exact rangeBounds 2824 256 h5 (by omega) (by omega)
          · exact wireBounds 3080 h6 (by omega) (by omega)
          · exact wireBounds 3081 h7 (by omega) (by omega)
          · exact wireBounds 3082 h8 (by omega) (by omega)
          · exact wireBounds 3083 h9 (by omega) (by omega)
          · exact wireBounds 3084 h10 (by omega) (by omega)
          · exact wireBounds 3085 h11 (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
    · rcases List.mem_append.mp hbranch with hlocal | harithmetic
      · have hbounds :
            workStart + 257 ≤ w ∧ w < workStart + 4112 := by
          simp only [pointAddT0, pointAddT1,
            pointAddT2, pointAddT3, pointAddT4,
            pointAddCandidate, pointAddSelected,
            List.mem_append, List.mem_range'_1] at hlocal
          norm_num [localWorkSize, selectedOffset, candidateOffset,
            flagOffset, yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth, pointWidth] at hlocal
          rcases hlocal with
              (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
          · exact rangeBounds 514 257 h0 (by omega) (by omega)
          · exact rangeBounds 771 257 h1 (by omega) (by omega)
          · exact rangeBounds 1028 257 h2 (by omega) (by omega)
          · exact rangeBounds 1285 257 h3 (by omega) (by omega)
          · exact rangeBounds 1542 257 h4 (by omega) (by omega)
          · exact rangeBounds 3086 513 h5 (by omega) (by omega)
          · exact rangeBounds 3599 513 h6 (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
      · have harithmeticLower :=
          pointAddArithmeticWork_lower workStart w harithmetic
        refine ⟨?_, ?_⟩
        · exact (by
            rw [pointAddArithmeticOffset, hlocalSizeEq] at harithmeticLower
            exact (Nat.add_le_add_left
              (by omega : 257 ≤ 4112) workStart).trans
              harithmeticLower)
        · rw [pointAddWork]
          exact List.mem_append_right _ harithmetic

  have hremainingClean :
      Clean
        (pointAddY workStart ++
          pointAddFlagWork workStart ++
          pointAddBranchWork workStart)
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    have hwFacts := hremainingFacts w hw
    have hwGe : workStart + 257 ≤ w := hwFacts.1
    have hwNotDst : w ∉ (pointAddX workStart).take 256 := by
      intro hdst
      rw [hdstEq] at hdst
      have hbounds : workStart ≤ w ∧ w < workStart + 256 :=
        List.mem_range'_1.mp hdst
      have hwLt : w < workStart + 257 :=
        hbounds.2.trans_le
          (Nat.add_le_add_left (by omega : 256 ≤ 257) workStart)
      exact (Nat.not_lt_of_ge hwGe) hwLt
    rw [hother w hwNotDst]
    exact hclean w hwFacts.2

  exact ⟨hpointAgree, hxValue, hremainingClean⟩

theorem pointAddCopyY_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        st) :
    let after :=
      Classical.run (pointAddCopyY pointReg workStart) st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp

  have hlocalSizeEq : localWorkSize = 4112 := by
    norm_num [localWorkSize, selectedOffset, candidateOffset, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth, pointWidth]

  have hdstEq :
      (pointAddY workStart).take 256 =
        List.range' (workStart + 257) 256 := by
    simp [pointAddY, fieldWidth, Secp256k1Instance.fieldWidth,
      List.take_range'_of_length_ge]

  have hdstWork :
      ∀ w ∈ (pointAddY workStart).take 256,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [hdstEq] at hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    refine ⟨by omega, ?_⟩
    rw [hlocalSizeEq]
    omega

  have hdstY :
      ∀ w ∈ (pointAddY workStart).take 256,
        w ∈ pointAddY workStart := by
    intro w hw
    exact List.mem_of_mem_take hw

  have hsrcMem :
      ∀ w ∈ PointRegister.y pointReg, w ∈ pointReg := by
    intro w hw
    change w ∈ (pointReg.drop 257).take 256 at hw
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)

  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup

  have hsrcNodup : (PointRegister.y pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 257)).trans
        (List.drop_sublist 257 pointReg))
    exact hpointNodup

  have hdstNodup : ((pointAddY workStart).take 256).Nodup := by
    rw [hdstEq]
    exact List.nodup_range'

  have hcopyNodup :
      (PointRegister.y pointReg ++
        (pointAddY workStart).take 256).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hsrcNodup, hdstNodup, ?_⟩
    intro a ha b hb
    exact hpublicWork a
      (List.mem_append_left outReg (hsrcMem a ha))
      b (hdstWork b hb)

  have hdstClean :
      Clean ((pointAddY workStart).take 256) st := by
    apply Arithmetic.Clean.mono hclean
    intro w hw
    exact List.mem_append_left _
      (List.mem_append_left _ (hdstY w hw))

  have hcopyValue :
      regValue ((pointAddY workStart).take 256)
          (Classical.run (pointAddCopyY pointReg workStart) st) =
        regValue (PointRegister.y pointReg) st := by
    simpa only [pointAddCopyY] using
      (Arithmetic.copyReg_correct
        (PointRegister.y pointReg)
        ((pointAddY workStart).take 256)
        st
        (by
          rw [hdstEq]
          simpa using
            (PointRegister.y_length pointReg hpointLength).symm)
        hcopyNodup hdstClean)

  have hother (w : Wire)
      (hw : w ∉ (pointAddY workStart).take 256) :
      Classical.run (pointAddCopyY pointReg workStart) st w = st w := by
    simpa only [pointAddCopyY] using
      (Arithmetic.copyReg_other w
        (PointRegister.y pointReg)
        ((pointAddY workStart).take 256) st hw)

  have hpointAgree :
      AgreesOn pointReg st
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hw
    apply hother
    intro hdst
    exact
      (hpublicWork w (List.mem_append_left outReg hw)
        w (hdstWork w hdst)) rfl

  have hxAgree :
      AgreesOn (pointAddX workStart) st
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hx
    apply hother
    intro hdst
    have hxBounds : workStart ≤ w ∧ w < workStart + 257 := by
      simpa [pointAddX, fieldWidth,
        Secp256k1Instance.fieldWidth] using
        (List.mem_range'_1.mp hx)
    rw [hdstEq] at hdst
    have hdstBounds := List.mem_range'_1.mp hdst
    exact (Nat.not_lt_of_ge hdstBounds.1) hxBounds.2

  have hxValue :
      regValue (pointAddX workStart)
          (Classical.run (pointAddCopyY pointReg workStart) st) =
        regValue (pointAddX workStart) st :=
    Arithmetic.AgreesOn.regValue hxAgree

  have hhighNotDst :
      workStart + 513 ∉ (pointAddY workStart).take 256 := by
    rw [hdstEq]
    simp [List.mem_range'_1]

  have hhighY : workStart + 513 ∈ pointAddY workStart := by
    simp [pointAddY, fieldWidth, Secp256k1Instance.fieldWidth,
      List.mem_range'_1]

  have hhighClean :
      Clean [workStart + 513]
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    rw [hother (workStart + 513) hhighNotDst]
    exact hclean (workStart + 513)
      (List.mem_append_left _
        (List.mem_append_left _ hhighY))

  have hpointAddYShape :
      pointAddY workStart =
        PointRegister.padCoordinate
          ((pointAddY workStart).take 256)
          (workStart + 513) := by
    rw [PointRegister.padCoordinate, hdstEq]
    change
      List.range' (workStart + 257) 257 =
        List.range' (workStart + 257) 256 ++
          [workStart + 513]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (List.range'_concat
        (s := workStart + 257) (n := 256) (step := 1))

  have hyValue :
      regValue (pointAddY workStart)
          (Classical.run (pointAddCopyY pointReg workStart) st) =
        regValue (PointRegister.y pointReg) st := by
    rw [hpointAddYShape]
    exact
      (PointRegister.regValue_padCoordinate_of_clean
        ((pointAddY workStart).take 256)
        (workStart + 513)
        (Classical.run (pointAddCopyY pointReg workStart) st)
        hhighClean).trans hcopyValue

  have rangeLower
      (offset len : Nat)
      {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmin : 514 ≤ offset) :
      workStart + 514 ≤ w :=
    (Nat.add_le_add_left hmin workStart).trans hw.1

  have wireLower
      (offset : Nat)
      {w : Wire}
      (hw : w = workStart + offset)
      (hmin : 514 ≤ offset) :
      workStart + 514 ≤ w := by
    subst w
    exact Nat.add_le_add_left hmin workStart

  have hflagLower :
      ∀ w ∈ pointAddFlagWork workStart,
        workStart + 514 ≤ w := by
    intro w hflag
    simp only [pointAddFlagWork, pointAddConst,
      pointAddZeroHistory, pointAddXDifference,
      pointAddXHistory, pointAddYDifference,
      pointAddYHistory, pointAddInfinityFlag,
      pointAddXEqFlag, pointAddYNegFlag,
      pointAddGenericFlag, pointAddPairFlag,
      pointAddDoubleFlag, List.mem_append,
      List.mem_cons, List.mem_range'_1] at hflag
    norm_num [flagOffset, yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
      constOffset, fieldAreaSize, fieldWidth,
      Secp256k1Instance.fieldWidth] at hflag
    rcases hflag with
        (((((h0 | h1) | h2) | h3) | h4) | h5) |
          (h6 | h7 | h8 | h9 | h10 | h11)
    · exact rangeLower 1799 256 h0 (by omega)
    · exact wireLower 2055 h1 (by omega)
    · exact rangeLower 2056 256 h2 (by omega)
    · exact rangeLower 2312 256 h3 (by omega)
    · exact rangeLower 2568 256 h4 (by omega)
    · exact rangeLower 2824 256 h5 (by omega)
    · exact wireLower 3080 h6 (by omega)
    · exact wireLower 3081 h7 (by omega)
    · exact wireLower 3082 h8 (by omega)
    · exact wireLower 3083 h9 (by omega)
    · exact wireLower 3084 h10 (by omega)
    · exact wireLower 3085 h11 (by omega)

  have hbranchLower :
      ∀ w ∈ pointAddBranchWork workStart,
        workStart + 514 ≤ w := by
    intro w hbranch
    rcases List.mem_append.mp hbranch with hlocal | harithmetic
    · simp only [pointAddT0, pointAddT1,
        pointAddT2, pointAddT3, pointAddT4,
        pointAddCandidate, pointAddSelected,
        List.mem_append, List.mem_range'_1] at hlocal
      norm_num [selectedOffset, candidateOffset,
        flagOffset, yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
        constOffset, fieldAreaSize, fieldWidth,
        Secp256k1Instance.fieldWidth, pointWidth] at hlocal
      rcases hlocal with
          (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
      · exact rangeLower 514 257 h0 (by omega)
      · exact rangeLower 771 257 h1 (by omega)
      · exact rangeLower 1028 257 h2 (by omega)
      · exact rangeLower 1285 257 h3 (by omega)
      · exact rangeLower 1542 257 h4 (by omega)
      · exact rangeLower 3086 513 h5 (by omega)
      · exact rangeLower 3599 513 h6 (by omega)
    · have harithmeticLower :=
        pointAddArithmeticWork_lower workStart w harithmetic
      rw [pointAddArithmeticOffset, hlocalSizeEq] at harithmeticLower
      exact
        (Nat.add_le_add_left (by omega : 514 ≤ 4112) workStart).trans
          harithmeticLower

  have hnotDstOfLower (w : Wire)
      (hlower : workStart + 514 ≤ w) :
      w ∉ (pointAddY workStart).take 256 := by
    intro hdst
    rw [hdstEq] at hdst
    have hdstBounds :
        workStart + 257 ≤ w ∧ w < workStart + 257 + 256 :=
      List.mem_range'_1.mp hdst
    have hdstUpper : w < workStart + 514 := by
      exact hdstBounds.2.trans_le
        (Nat.add_le_add_left (by omega : 257 + 256 ≤ 514) workStart)
    exact (Nat.not_lt_of_ge hlower) hdstUpper

  have hflagClean :
      Clean (pointAddFlagWork workStart)
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hw
    rw [hother w (hnotDstOfLower w (hflagLower w hw))]
    exact hclean w
      (List.mem_append_left _ (List.mem_append_right _ hw))

  have hbranchClean :
      Clean (pointAddBranchWork workStart)
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hw
    rw [hother w (hnotDstOfLower w (hbranchLower w hw))]
    exact hclean w (List.mem_append_right _ hw)

  exact ⟨hpointAgree, hxValue, hyValue, hflagClean, hbranchClean⟩

theorem pointAddCoordinateCopies_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddCoordinateCopies pointReg workStart)
        st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp
  rw [pointAddCoordinateCopies, Classical.run_append]

  let mid :=
    Classical.run (pointAddCopyX pointReg workStart) st

  have hx :=
    pointAddCopyX_correct
      pointReg outReg workStart st
      hpointLength hnodup hclean

  change
    AgreesOn pointReg st mid ∧
      regValue (pointAddX workStart) mid =
        regValue (PointRegister.x pointReg) st ∧
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        mid
    at hx

  rcases hx with ⟨hpointX, hxValue, hcleanAfterX⟩

  have hy :=
    pointAddCopyY_correct
      pointReg outReg workStart mid
      hpointLength hnodup hcleanAfterX

  let after :=
    Classical.run (pointAddCopyY pointReg workStart) mid

  change
    AgreesOn pointReg mid after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) mid ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) mid ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after
    at hy

  rcases hy with
    ⟨hpointY, hxKeep, hyValue, hflagClean, hbranchClean⟩

  have hpointFinal : AgreesOn pointReg st after := by
    intro w hw
    calc
      after w = mid w := hpointY w hw
      _ = st w := hpointX w hw

  have hyPublic :
      regValue (PointRegister.y pointReg) mid =
        regValue (PointRegister.y pointReg) st := by
    exact Arithmetic.AgreesOn.regValue
      (fun w hw => hpointX w (by
        rw [← PointRegister.tag_x_y pointReg hpointLength]
        simp [hw]))

  change
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after

  refine ⟨hpointFinal, ?_, ?_, hflagClean, hbranchClean⟩
  · exact hxKeep.trans hxValue
  · exact hyValue.trans hyPublic

private theorem pointAddFlags_usesOnly
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) :
    CircuitUsesOnly
      (pointReg ++ pointAddFlagWork workStart)
      (pointAddFlags pointReg workStart xC yC) := by
  simp only [pointAddFlags]
  have htag :
      ∀ w ∈ PointRegister.tag pointReg,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    exact List.mem_append_left _ (List.mem_of_mem_take hw)
  have hx :
      ∀ w ∈ PointRegister.x pointReg,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply List.mem_append_left
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have hy :
      ∀ w ∈ PointRegister.y pointReg,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply List.mem_append_left
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have hflag :
      ∀ w ∈ pointAddFlagWork workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    exact List.mem_append_right _ hw
  have hconst :
      ∀ w ∈ pointAddConst workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hzero :
      ∀ w ∈ pointAddZeroHistory workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hxdifference :
      ∀ w ∈ pointAddXDifference workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hxhistory :
      ∀ w ∈ pointAddXHistory workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hydifference :
      ∀ w ∈ pointAddYDifference workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hyhistory :
      ∀ w ∈ pointAddYHistory workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]

  have hzeroFlag :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (zeroFlag
          (PointRegister.tag pointReg)
          (pointAddInfinityFlag workStart)
          (pointAddZeroHistory workStart)) := by
    apply usesOnly_mono (zeroFlag_usesOnly _ _ _)
    intro w hw
    simp only [zeroFlagWires, List.mem_append,
      List.mem_cons] at hw
    rcases hw with htagMem | hflagMem | hhistoryMem
    · exact htag w htagMem
    · subst w
      apply hflag
      simp [pointAddFlagWork]
    · exact hzero w hhistoryMem

  have hequalX :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (equalFlag
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)) := by
    apply usesOnly_mono (equalFlag_usesOnly _ _ _ _ _)
    intro w hw
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hw
    rcases hw with ((hxMem | hconstMem) | hdiffMem) |
        hflagMem | hhistoryMem
    · exact hx w hxMem
    · exact hconst w hconstMem
    · exact hxdifference w hdiffMem
    · subst w
      apply hflag
      simp [pointAddFlagWork]
    · exact hxhistory w hhistoryMem

  have hequalY :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (equalFlag
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)) := by
    apply usesOnly_mono (equalFlag_usesOnly _ _ _ _ _)
    intro w hw
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hw
    rcases hw with ((hyMem | hconstMem) | hdiffMem) |
        hflagMem | hhistoryMem
    · exact hy w hyMem
    · exact hconst w hconstMem
    · exact hydifference w hdiffMem
    · subst w
      apply hflag
      simp [pointAddFlagWork]
    · exact hyhistory w hhistoryMem

  have hloadX :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (loadConst (pointAddConst workStart) xC.val) :=
    usesOnly_mono (loadConst_usesOnly _ _) hconst

  have hloadY :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (loadConst (pointAddConst workStart) (-yC).val) :=
    usesOnly_mono (loadConst_usesOnly _ _) hconst

  have hgates :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        ([Gate.X (pointAddInfinityFlag workStart),
          Gate.X (pointAddXEqFlag workStart),
          Gate.CCX
            (pointAddInfinityFlag workStart)
            (pointAddXEqFlag workStart)
            (pointAddGenericFlag workStart),
          Gate.X (pointAddXEqFlag workStart),
          Gate.X (pointAddInfinityFlag workStart),
          Gate.X (pointAddYNegFlag workStart),
          Gate.CCX
            (pointAddXEqFlag workStart)
            (pointAddYNegFlag workStart)
            (pointAddPairFlag workStart),
          Gate.X (pointAddYNegFlag workStart),
          Gate.X (pointAddInfinityFlag workStart),
          Gate.CCX
            (pointAddInfinityFlag workStart)
            (pointAddPairFlag workStart)
            (pointAddDoubleFlag workStart),
          Gate.X (pointAddInfinityFlag workStart)] : Circuit) := by
    simp [CircuitUsesOnly, Gate.UsesOnly,
      pointAddFlagWork]

  have hprefix1 := usesOnly_append hzeroFlag hloadX
  have hprefix2 := usesOnly_append hprefix1 hequalX
  have hprefix3 := usesOnly_append hprefix2 hloadX
  have hprefix4 := usesOnly_append hprefix3 hloadY
  have hprefix5 := usesOnly_append hprefix4 hequalY
  have hprefix6 := usesOnly_append hprefix5 hloadY
  exact usesOnly_append hprefix6 hgates

private theorem pointAddXEqualWork_nodup
    (workStart : Wire) :
    ((pointAddConst workStart ++
        pointAddXDifference workStart) ++
      pointAddXEqFlag workStart ::
        pointAddXHistory workStart).Nodup := by
  simp [pointAddConst, pointAddXDifference,
    pointAddXEqFlag, pointAddXHistory,
    List.nodup_append, List.nodup_range',
    constOffset, xDifferenceOffset, xHistoryOffset,
    zeroHistoryOffset, flagOffset, yHistoryOffset,
    yDifferenceOffset, fieldAreaSize, fieldWidth,
    Secp256k1Instance.fieldWidth]
  constructor
  · intro a haLower haUpper
    constructor
    · intro h
      subst a
      omega
    · intro b hbLower hbUpper h
      subst b
      omega
  · intro a haLower haUpper b hb
    rcases hb with hb | hb | hb
    · intro h
      subst b
      omega
    · subst b
      intro h
      subst a
      omega
    · intro h
      subst b
      omega

private theorem pointAddYEqualWork_nodup
    (workStart : Wire) :
    ((pointAddConst workStart ++
        pointAddYDifference workStart) ++
      pointAddYNegFlag workStart ::
        pointAddYHistory workStart).Nodup := by
  simp [pointAddConst, pointAddYDifference,
    pointAddYNegFlag, pointAddYHistory,
    List.nodup_append, List.nodup_range',
    constOffset, yDifferenceOffset, yHistoryOffset,
    xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
    flagOffset, fieldAreaSize, fieldWidth,
    Secp256k1Instance.fieldWidth]
  constructor
  · intro a haLower haUpper
    constructor
    · intro h
      subst a
      omega
    · intro b hbLower hbUpper h
      subst b
      omega
  · intro a haLower haUpper b hb
    rcases hb with hb | hb | hb
    · intro h
      subst b
      omega
    · subst b
      intro h
      subst a
      omega
    · intro h
      subst b
      omega

private theorem pointAddZeroFlagWork_nodup
    (workStart : Wire) :
    (pointAddInfinityFlag workStart ::
      pointAddZeroHistory workStart).Nodup := by
  simp [pointAddInfinityFlag, pointAddZeroHistory,
    flagOffset, yHistoryOffset, yDifferenceOffset,
    xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
    constOffset, fieldAreaSize, fieldWidth,
    Secp256k1Instance.fieldWidth]

private theorem run_loadConst_twice
    (ws : List Wire) (c : Nat) (st : BasisState)
    (hnd : ws.Nodup) :
    Classical.run (loadConst ws c)
        (Classical.run (loadConst ws c) st) = st := by
  induction ws generalizing c st with
  | nil =>
      simp [loadConst]
  | cons w ws ih =>
      obtain ⟨hw, hws⟩ := List.nodup_cons.mp hnd
      rw [loadConst]
      by_cases hc : c % 2 = 1
      · rw [if_pos hc]
        simp only [Classical.run_append,
          Classical.run_cons, Classical.run_nil]
        have hcomm (s : BasisState) :
            Classical.applyGate (Gate.X w)
                (Classical.run (loadConst ws (c / 2)) s) =
              Classical.run (loadConst ws (c / 2))
                (Classical.applyGate (Gate.X w) s) := by
          funext v
          by_cases hvw : v = w
          · subst v
            simp only [Classical.applyGate]
            rw [loadConst_other w ws (c / 2) s hw,
              loadConst_other w ws (c / 2)
                (s[w ↦ !s w]) hw]
            simp [upd]
          · by_cases hv : v ∈ ws
            · have hcongr :=
                CircuitUsesOnly.run_congr
                  (loadConst_usesOnly ws (c / 2))
                  (st₁ := s)
                  (st₂ := Classical.applyGate (Gate.X w) s)
                  (by
                    intro a ha
                    simp only [Classical.applyGate]
                    exact (upd_other s w (!s w)
                      (fun e => hw (e ▸ ha))).symm)
                  v hv
              simp only [Classical.applyGate]
              rw [upd_other _ _ _ hvw]
              exact hcongr
            · simp only [Classical.applyGate]
              rw [upd_other _ _ _ hvw,
                loadConst_other v ws (c / 2) s hv,
                loadConst_other v ws (c / 2)
                  (s[w ↦ !s w]) hv]
              rw [upd_other _ _ _ hvw]
        rw [hcomm]
        rw [ih (c / 2) _ hws]
        funext v
        by_cases hv : v = w <;>
          simp [Classical.applyGate, upd, hv]
      · rw [if_neg hc]
        simpa using ih (c / 2) st hws

private theorem binaryBennettWrapper_correct
    (lhs rhs out a b result active : List Wire)
    (core : Circuit) (st : BasisState)
    (haActive : ∀ w ∈ a, w ∈ active)
    (hbActive : ∀ w ∈ b, w ∈ active)
    (hresultActive : ∀ w ∈ result, w ∈ active)
    (huses : CircuitUsesOnly active core)
    (hfree : Classical.HPFree core)
    (hwellFormed : CircuitWellFormed core)
    (hactiveOut : ModExp.Schedule.WireDisjoint active out)
    (hlhsOut : ModExp.Schedule.WireDisjoint lhs out)
    (hrhsOut : ModExp.Schedule.WireDisjoint rhs out)
    (hlen : out.length = result.length)
    (hresultOutNodup : (result ++ out).Nodup)
    (hcopyANodup : (lhs ++ a).Nodup)
    (hcopyBNodup : (rhs ++ b).Nodup)
    (hcleanOut : Clean out st) :
    let initialized := Classical.run
      (Arithmetic.copyReg lhs a ++ Arithmetic.copyReg rhs b) st
    let after := Classical.run
      (Arithmetic.copyReg lhs a ++
        Arithmetic.copyReg rhs b ++
        core ++
        Arithmetic.copyReg result out ++
        core.reverse ++
        Arithmetic.copyReg rhs b ++
        Arithmetic.copyReg lhs a) st
    regValue out after =
        regValue result (Classical.run core initialized) ∧
      ∀ w, w ∉ out → after w = st w := by
  let loadA := Arithmetic.copyReg lhs a
  let loadB := Arithmetic.copyReg rhs b
  let initCircuit := loadA ++ loadB
  let cleanup := loadB ++ loadA
  let initialized := Classical.run initCircuit st
  let middle :=
    core ++ Arithmetic.copyReg result out ++ core.reverse
  let middleAfter := Classical.run middle initialized
  let after := Classical.run cleanup middleAfter
  let support := lhs ++ (rhs ++ active)
  have hloadAUses : CircuitUsesOnly support loadA :=
    Arithmetic.copyReg_usesOnly lhs a support
      (by intro w hw; simp [support, hw])
      (by intro w hw; simp [support, haActive w hw])
  have hloadBUses : CircuitUsesOnly support loadB :=
    Arithmetic.copyReg_usesOnly rhs b support
      (by intro w hw; simp [support, hw])
      (by intro w hw; simp [support, hbActive w hw])
  have hinitializeUses : CircuitUsesOnly support initCircuit := by
    exact usesOnly_append hloadAUses hloadBUses
  have hcleanupUses : CircuitUsesOnly support cleanup := by
    exact usesOnly_append hloadBUses hloadAUses
  have hmiddleUses : CircuitUsesOnly (active ++ out) middle := by
    have hcoreUses : CircuitUsesOnly (active ++ out) core :=
      usesOnly_mono huses (by
        intro w hw
        exact List.mem_append_left _ hw)
    have hcopyUses :
        CircuitUsesOnly (active ++ out)
          (Arithmetic.copyReg result out) :=
      Arithmetic.copyReg_usesOnly result out (active ++ out)
        (by
          intro w hw
          exact List.mem_append_left _ (hresultActive w hw))
        (by
          intro w hw
          exact List.mem_append_right _ hw)
    exact usesOnly_append
      (usesOnly_append hcoreUses hcopyUses)
      (usesOnly_reverse hcoreUses)
  have houtNotActive (w : Wire) (hw : w ∈ out) : w ∉ active := by
    intro hwa
    exact hactiveOut w hwa w hw rfl
  have houtNotA (w : Wire) (hw : w ∈ out) : w ∉ a := by
    intro hwa
    exact houtNotActive w hw (haActive w hwa)
  have houtNotB (w : Wire) (hw : w ∈ out) : w ∉ b := by
    intro hwb
    exact houtNotActive w hw (hbActive w hwb)
  have hcleanOutInitialized : Clean out initialized := by
    intro w hw
    dsimp [initialized, initCircuit]
    rw [Classical.run_append]
    rw [Arithmetic.copyReg_other w rhs b
      (Classical.run loadA st) (houtNotB w hw)]
    rw [Arithmetic.copyReg_other w lhs a st (houtNotA w hw)]
    exact hcleanOut w hw
  have hbennett := ModExp.bennett_cleanup_copyOut
    core active result out initialized huses hfree hwellFormed
    hactiveOut hlen hresultOutNodup hcleanOutInitialized
  dsimp only at hbennett
  have hmiddleAfter :
      middleAfter = Classical.run
        (core ++ Arithmetic.copyReg result out ++ core.reverse)
        initialized := rfl
  have hmiddleActive : AgreesOn active initialized middleAfter := by
    simpa [middleAfter, middle, List.append_assoc] using hbennett.1
  have hmiddleValue :
      regValue out middleAfter =
        regValue result (Classical.run core initialized) := by
    simpa [middleAfter, middle, List.append_assoc] using hbennett.2
  have hcancelInitialize :
      Classical.run cleanup initialized = st := by
    dsimp [cleanup, initialized, initCircuit]
    rw [Classical.run_append, Classical.run_append]
    rw [run_copyReg_twice rhs b
      (Classical.run loadA st) hcopyBNodup]
    exact run_copyReg_twice lhs a st hcopyANodup
  have hmiddleSupport : ∀ w ∈ support,
      middleAfter w = initialized w := by
    intro w hw
    simp only [support, List.mem_append] at hw
    rcases hw with hlhs | hrhs | hactive
    · by_cases hwa : w ∈ active
      · exact hmiddleActive w hwa
      · apply hmiddleUses.preservesOutside initialized w
        simp only [List.mem_append, not_or]
        exact ⟨hwa, fun hwo => hlhsOut w hlhs w hwo rfl⟩
    · by_cases hwa : w ∈ active
      · exact hmiddleActive w hwa
      · apply hmiddleUses.preservesOutside initialized w
        simp only [List.mem_append, not_or]
        exact ⟨hwa, fun hwo => hrhsOut w hrhs w hwo rfl⟩
    · exact hmiddleActive w hactive
  have hcleanupCongr : ∀ w ∈ support,
      Classical.run cleanup middleAfter w =
        Classical.run cleanup initialized w :=
    CircuitUsesOnly.run_congr hcleanupUses hmiddleSupport
  have houtNotSupport (w : Wire) (hw : w ∈ out) : w ∉ support := by
    intro hws
    simp only [support, List.mem_append] at hws
    rcases hws with hlhs | hrhs | hactive
    · exact hlhsOut w hlhs w hw rfl
    · exact hrhsOut w hrhs w hw rfl
    · exact hactiveOut w hactive w hw rfl
  have houtAfter : regValue out after = regValue out middleAfter := by
    apply AgreesOn.regValue
    intro w hw
    exact hcleanupUses.preservesOutside middleAfter w
      (houtNotSupport w hw)
  have hpreserve : ∀ w, w ∉ out → after w = st w := by
    intro w hwOut
    by_cases hwSupport : w ∈ support
    · calc
        after w = Classical.run cleanup initialized w :=
          hcleanupCongr w hwSupport
        _ = st w := congrFun hcancelInitialize w
    · have hwActive : w ∉ active := by
        intro hw
        exact hwSupport (by simp [support, hw])
      calc
        after w = middleAfter w :=
          hcleanupUses.preservesOutside middleAfter w hwSupport
        _ = initialized w :=
          hmiddleUses.preservesOutside initialized w (by
            simp [hwActive, hwOut])
        _ = st w :=
          hinitializeUses.preservesOutside st w hwSupport
  have hprogramRun :
      Classical.run
          (Arithmetic.copyReg lhs a ++
            Arithmetic.copyReg rhs b ++
            core ++
            Arithmetic.copyReg result out ++
            core.reverse ++
            Arithmetic.copyReg rhs b ++
            Arithmetic.copyReg lhs a) st =
        after := by
    simp [after, middleAfter, middle, initialized, initCircuit,
      cleanup, loadA, loadB, Classical.run_append]
  dsimp only
  rw [hprogramRun]
  exact ⟨houtAfter.trans hmiddleValue, hpreserve⟩

private theorem unaryConstBennettWrapper_correct
    (input out a b result active : List Wire)
    (constant : Nat) (core : Circuit) (st : BasisState)
    (haActive : ∀ w ∈ a, w ∈ active)
    (hbActive : ∀ w ∈ b, w ∈ active)
    (hresultActive : ∀ w ∈ result, w ∈ active)
    (huses : CircuitUsesOnly active core)
    (hfree : Classical.HPFree core)
    (hwellFormed : CircuitWellFormed core)
    (hactiveOut : ModExp.Schedule.WireDisjoint active out)
    (hinputOut : ModExp.Schedule.WireDisjoint input out)
    (hlen : out.length = result.length)
    (hresultOutNodup : (result ++ out).Nodup)
    (hcopyANodup : (input ++ a).Nodup)
    (hbNodup : b.Nodup)
    (hcleanOut : Clean out st) :
    let initialized := Classical.run
      (Arithmetic.copyReg input a ++ loadConst b constant) st
    let after := Classical.run
      (Arithmetic.copyReg input a ++
        loadConst b constant ++
        core ++
        Arithmetic.copyReg result out ++
        core.reverse ++
        loadConst b constant ++
        Arithmetic.copyReg input a) st
    regValue out after =
        regValue result (Classical.run core initialized) ∧
      ∀ w, w ∉ out → after w = st w := by
  let loadA := Arithmetic.copyReg input a
  let loadB := loadConst b constant
  let initCircuit := loadA ++ loadB
  let cleanup := loadB ++ loadA
  let initialized := Classical.run initCircuit st
  let middle :=
    core ++ Arithmetic.copyReg result out ++ core.reverse
  let middleAfter := Classical.run middle initialized
  let after := Classical.run cleanup middleAfter
  let support := input ++ active
  have hloadAUses : CircuitUsesOnly support loadA :=
    Arithmetic.copyReg_usesOnly input a support
      (by intro w hw; simp [support, hw])
      (by intro w hw; simp [support, haActive w hw])
  have hloadBUses : CircuitUsesOnly support loadB :=
    usesOnly_mono (loadConst_usesOnly b constant) (by
      intro w hw
      simp [support, hbActive w hw])
  have hinitializeUses : CircuitUsesOnly support initCircuit := by
    exact usesOnly_append hloadAUses hloadBUses
  have hcleanupUses : CircuitUsesOnly support cleanup := by
    exact usesOnly_append hloadBUses hloadAUses
  have hmiddleUses : CircuitUsesOnly (active ++ out) middle := by
    have hcoreUses : CircuitUsesOnly (active ++ out) core :=
      usesOnly_mono huses (by
        intro w hw
        exact List.mem_append_left _ hw)
    have hcopyUses :
        CircuitUsesOnly (active ++ out)
          (Arithmetic.copyReg result out) :=
      Arithmetic.copyReg_usesOnly result out (active ++ out)
        (by
          intro w hw
          exact List.mem_append_left _ (hresultActive w hw))
        (by
          intro w hw
          exact List.mem_append_right _ hw)
    exact usesOnly_append
      (usesOnly_append hcoreUses hcopyUses)
      (usesOnly_reverse hcoreUses)
  have houtNotActive (w : Wire) (hw : w ∈ out) : w ∉ active := by
    intro hwa
    exact hactiveOut w hwa w hw rfl
  have houtNotA (w : Wire) (hw : w ∈ out) : w ∉ a := by
    intro hwa
    exact houtNotActive w hw (haActive w hwa)
  have houtNotB (w : Wire) (hw : w ∈ out) : w ∉ b := by
    intro hwb
    exact houtNotActive w hw (hbActive w hwb)
  have hcleanOutInitialized : Clean out initialized := by
    intro w hw
    dsimp [initialized, initCircuit]
    rw [Classical.run_append]
    rw [loadConst_other w b constant
      (Classical.run loadA st) (houtNotB w hw)]
    rw [Arithmetic.copyReg_other w input a st (houtNotA w hw)]
    exact hcleanOut w hw
  have hbennett := ModExp.bennett_cleanup_copyOut
    core active result out initialized huses hfree hwellFormed
    hactiveOut hlen hresultOutNodup hcleanOutInitialized
  dsimp only at hbennett
  have hmiddleActive : AgreesOn active initialized middleAfter := by
    simpa [middleAfter, middle, List.append_assoc] using hbennett.1
  have hmiddleValue :
      regValue out middleAfter =
        regValue result (Classical.run core initialized) := by
    simpa [middleAfter, middle, List.append_assoc] using hbennett.2
  have hcancelInitialize :
      Classical.run cleanup initialized = st := by
    dsimp [cleanup, initialized, initCircuit]
    rw [Classical.run_append, Classical.run_append]
    rw [run_loadConst_twice b constant
      (Classical.run loadA st) hbNodup]
    exact run_copyReg_twice input a st hcopyANodup
  have hmiddleSupport : ∀ w ∈ support,
      middleAfter w = initialized w := by
    intro w hw
    simp only [support, List.mem_append] at hw
    rcases hw with hinput | hactive
    · by_cases hwa : w ∈ active
      · exact hmiddleActive w hwa
      · apply hmiddleUses.preservesOutside initialized w
        simp only [List.mem_append, not_or]
        exact ⟨hwa, fun hwo => hinputOut w hinput w hwo rfl⟩
    · exact hmiddleActive w hactive
  have hcleanupCongr : ∀ w ∈ support,
      Classical.run cleanup middleAfter w =
        Classical.run cleanup initialized w :=
    CircuitUsesOnly.run_congr hcleanupUses hmiddleSupport
  have houtNotSupport (w : Wire) (hw : w ∈ out) : w ∉ support := by
    intro hws
    simp only [support, List.mem_append] at hws
    rcases hws with hinput | hactive
    · exact hinputOut w hinput w hw rfl
    · exact hactiveOut w hactive w hw rfl
  have houtAfter : regValue out after = regValue out middleAfter := by
    apply AgreesOn.regValue
    intro w hw
    exact hcleanupUses.preservesOutside middleAfter w
      (houtNotSupport w hw)
  have hpreserve : ∀ w, w ∉ out → after w = st w := by
    intro w hwOut
    by_cases hwSupport : w ∈ support
    · calc
        after w = Classical.run cleanup initialized w :=
          hcleanupCongr w hwSupport
        _ = st w := congrFun hcancelInitialize w
    · have hwActive : w ∉ active := by
        intro hw
        exact hwSupport (by simp [support, hw])
      calc
        after w = middleAfter w :=
          hcleanupUses.preservesOutside middleAfter w hwSupport
        _ = initialized w :=
          hmiddleUses.preservesOutside initialized w (by
            simp [hwActive, hwOut])
        _ = st w :=
          hinitializeUses.preservesOutside st w hwSupport
  have hprogramRun :
      Classical.run
          (Arithmetic.copyReg input a ++
            loadConst b constant ++
            core ++
            Arithmetic.copyReg result out ++
            core.reverse ++
            loadConst b constant ++
            Arithmetic.copyReg input a) st =
        after := by
    simp [after, middleAfter, middle, initialized, initCircuit,
      cleanup, loadA, loadB, Classical.run_append]
  dsimp only
  rw [hprogramRun]
  exact ⟨houtAfter.trans hmiddleValue, hpreserve⟩

private theorem shiftedBinaryCore_correct
    (core : Circuit) (layout : RegisterLayout)
    (modulus : Nat) (op : Nat → Nat → Nat) (cost : Nat)
    (spec : CleanBinaryContract core layout modulus op cost)
    (hlayout : layout.Valid)
    (offset : Wire) (lhs rhs : List Wire) (st : BasisState)
    (hlhsLength : lhs.length = layout.lhs.length)
    (hrhsLength : rhs.length = layout.rhs.length)
    (hcopyANodup :
      (lhs ++ shiftWires offset layout.lhs).Nodup)
    (hcopyBNodup :
      (rhs ++ shiftWires offset layout.rhs).Nodup)
    (hengineRhs : ModExp.Schedule.WireDisjoint
      (shiftWires offset layout.allWires) rhs)
    (hcleanEngine : Clean
      (shiftWires offset layout.allWires) st)
    (hlhsBound : regValue lhs st < modulus)
    (hrhsBound : regValue rhs st < modulus) :
    let initialized := Classical.run
      (Arithmetic.copyReg lhs (shiftWires offset layout.lhs) ++
        Arithmetic.copyReg rhs (shiftWires offset layout.rhs)) st
    regValue (shiftWires offset layout.out)
        (Classical.run (shiftCircuit offset core) initialized) =
      op (regValue lhs st) (regValue rhs st) % modulus := by
  let a := shiftWires offset layout.lhs
  let b := shiftWires offset layout.rhs
  let loadA := Arithmetic.copyReg lhs a
  let loadB := Arithmetic.copyReg rhs b
  let loadedA := Classical.run loadA st
  let initialized := Classical.run loadB loadedA
  have hshape :
      (layout.lhs ++
        (layout.rhs ++ (layout.out ++ layout.work))).Nodup := by
    simpa [RegisterLayout.allWires, List.append_assoc] using hlayout.2.2
  obtain ⟨hlhsNodup, htailLhs, hlhsCross⟩ :=
    List.nodup_append.mp hshape
  obtain ⟨hrhsNodup, htailRhs, hrhsCross⟩ :=
    List.nodup_append.mp htailLhs
  obtain ⟨houtNodup, hworkNodup, houtCross⟩ :=
    List.nodup_append.mp htailRhs
  have haSubset : ∀ w ∈ a,
      w ∈ shiftWires offset layout.allWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hbSubset : ∀ w ∈ b,
      w ∈ shiftWires offset layout.allWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hshiftCross
      {xs ys : List Wire}
      (hcross : ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y) :
      ∀ x ∈ shiftWires offset xs,
        x ∉ shiftWires offset ys := by
    intro x hx hxy
    simp only [shiftWires, List.mem_map] at hx hxy
    obtain ⟨sourceX, hsourceX, rfl⟩ := hx
    obtain ⟨sourceY, hsourceY, heq⟩ := hxy
    exact hcross sourceX hsourceX sourceY hsourceY
      (Nat.add_left_cancel heq.symm)
  have haNotB : ∀ w ∈ a, w ∉ b := by
    apply hshiftCross
    intro x hx y hy
    exact hlhsCross x hx y (by simp [hy])
  have hbNotA : ∀ w ∈ b, w ∉ a := by
    intro w hw hwa
    exact haNotB w hwa hw
  have hcoreFreshNotA : ∀ w ∈
      shiftWires offset (layout.out ++ layout.work), w ∉ a := by
    intro w hw hwa
    have hcross := hshiftCross (xs := layout.lhs)
      (ys := layout.out ++ layout.work) (by
        intro x hx y hy
        exact hlhsCross x hx y
          (List.mem_append_right _ hy))
    exact hcross w hwa hw
  have hcoreFreshNotB : ∀ w ∈
      shiftWires offset (layout.out ++ layout.work), w ∉ b := by
    intro w hw hwb
    have hcross := hshiftCross (xs := layout.rhs)
      (ys := layout.out ++ layout.work) hrhsCross
    exact hcross w hwb hw
  have hcleanA : Clean a st := by
    intro w hw
    exact hcleanEngine w (haSubset w hw)
  have hvalueAloaded : regValue a loadedA = regValue lhs st := by
    exact Arithmetic.copyReg_correct lhs a st
      (by simpa [a, shiftWires] using hlhsLength.symm)
      (by simpa [a] using hcopyANodup) hcleanA
  have hcleanBLoadedA : Clean b loadedA := by
    intro w hw
    change Classical.run loadA st w = false
    rw [Arithmetic.copyReg_other w lhs a st (hbNotA w hw)]
    exact hcleanEngine w (hbSubset w hw)
  have hrhsLoadedA : regValue rhs loadedA = regValue rhs st := by
    apply regValue_congr
    intro w hw
    change Classical.run loadA st w = st w
    apply Arithmetic.copyReg_other
    intro hwa
    exact hengineRhs w (haSubset w hwa) w hw rfl
  have hvalueBInitialized :
      regValue b initialized = regValue rhs st := by
    rw [show regValue rhs st = regValue rhs loadedA from hrhsLoadedA.symm]
    exact Arithmetic.copyReg_correct rhs b loadedA
      (by simpa [b, shiftWires] using hrhsLength.symm)
      (by simpa [b] using hcopyBNodup) hcleanBLoadedA
  have hvalueAInitialized :
      regValue a initialized = regValue lhs st := by
    calc
      regValue a initialized = regValue a loadedA := by
        apply regValue_congr
        intro w hw
        change Classical.run loadB loadedA w = loadedA w
        exact Arithmetic.copyReg_other w rhs b loadedA
          (haNotB w hw)
      _ = regValue lhs st := hvalueAloaded
  have hcleanCore :
      Clean (layout.out ++ layout.work)
        (shiftedView offset initialized) := by
    intro w hw
    change initialized (offset + w) = false
    have hshiftMem : offset + w ∈
        shiftWires offset (layout.out ++ layout.work) := by
      simp only [shiftWires, List.mem_map]
      exact ⟨w, hw, rfl⟩
    change Classical.run loadB loadedA (offset + w) = false
    rw [Arithmetic.copyReg_other (offset + w) rhs b loadedA
      (hcoreFreshNotB _ hshiftMem)]
    change Classical.run loadA st (offset + w) = false
    rw [Arithmetic.copyReg_other (offset + w) lhs a st
      (hcoreFreshNotA _ hshiftMem)]
    apply hcleanEngine
    exact shiftWires_mono offset (by
      intro v hv
      simp only [List.mem_append] at hv
      rcases hv with hv | hv
      · simp [RegisterLayout.allWires, hv]
      · simp [RegisterLayout.allWires, hv])
      (offset + w) hshiftMem
  have hinputA :
      regValue layout.lhs (shiftedView offset initialized) =
        regValue lhs st := by
    rw [← regValue_shiftWires]
    simpa [a] using hvalueAInitialized
  have hinputB :
      regValue layout.rhs (shiftedView offset initialized) =
        regValue rhs st := by
    rw [← regValue_shiftWires]
    simpa [b] using hvalueBInitialized
  have hcorrect := spec.correct
    (shiftedView offset initialized) hlayout
    (by simpa [hinputA] using hlhsBound)
    (by simpa [hinputB] using hrhsBound)
    hcleanCore
  dsimp only at hcorrect
  dsimp only
  rw [Classical.run_append]
  change regValue (shiftWires offset layout.out)
      (Classical.run (shiftCircuit offset core) initialized) = _
  calc
    regValue (shiftWires offset layout.out)
        (Classical.run (shiftCircuit offset core) initialized) =
        regValue layout.out
          (shiftedView offset
            (Classical.run (shiftCircuit offset core) initialized)) :=
      regValue_shiftWires offset layout.out _
    _ = regValue layout.out
          (Classical.run core (shiftedView offset initialized)) := by
      rw [shiftedView_runShiftCircuit]
    _ = op (regValue lhs st) (regValue rhs st) % modulus := by
      simpa [hinputA, hinputB] using hcorrect.2.2.1

private theorem shiftedUnaryConstCore_correct
    (core : Circuit) (layout : RegisterLayout)
    (modulus : Nat) (op : Nat → Nat → Nat) (cost : Nat)
    (spec : CleanBinaryContract core layout modulus op cost)
    (hlayout : layout.Valid)
    (offset : Wire) (input : List Wire) (constant : Nat)
    (st : BasisState)
    (hinputLength : input.length = layout.lhs.length)
    (hcopyANodup :
      (input ++ shiftWires offset layout.lhs).Nodup)
    (hcleanEngine : Clean
      (shiftWires offset layout.allWires) st)
    (hinputBound : regValue input st < modulus)
    (hconstantBound : constant < modulus)
    (hconstantFits : constant < 2 ^ layout.rhs.length) :
    let initialized := Classical.run
      (Arithmetic.copyReg input (shiftWires offset layout.lhs) ++
        loadConst (shiftWires offset layout.rhs) constant) st
    regValue (shiftWires offset layout.out)
        (Classical.run (shiftCircuit offset core) initialized) =
      op (regValue input st) constant % modulus := by
  let a := shiftWires offset layout.lhs
  let b := shiftWires offset layout.rhs
  let loadA := Arithmetic.copyReg input a
  let loadB := loadConst b constant
  let loadedA := Classical.run loadA st
  let initialized := Classical.run loadB loadedA
  have hshape :
      (layout.lhs ++
        (layout.rhs ++ (layout.out ++ layout.work))).Nodup := by
    simpa [RegisterLayout.allWires, List.append_assoc] using hlayout.2.2
  obtain ⟨hlhsNodup, htailLhs, hlhsCross⟩ :=
    List.nodup_append.mp hshape
  obtain ⟨hrhsNodup, htailRhs, hrhsCross⟩ :=
    List.nodup_append.mp htailLhs
  obtain ⟨houtNodup, hworkNodup, houtCross⟩ :=
    List.nodup_append.mp htailRhs
  have haSubset : ∀ w ∈ a,
      w ∈ shiftWires offset layout.allWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hbSubset : ∀ w ∈ b,
      w ∈ shiftWires offset layout.allWires := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hshiftCross
      {xs ys : List Wire}
      (hcross : ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y) :
      ∀ x ∈ shiftWires offset xs,
        x ∉ shiftWires offset ys := by
    intro x hx hxy
    simp only [shiftWires, List.mem_map] at hx hxy
    obtain ⟨sourceX, hsourceX, rfl⟩ := hx
    obtain ⟨sourceY, hsourceY, heq⟩ := hxy
    exact hcross sourceX hsourceX sourceY hsourceY
      (Nat.add_left_cancel heq.symm)
  have haNotB : ∀ w ∈ a, w ∉ b := by
    apply hshiftCross
    intro x hx y hy
    exact hlhsCross x hx y (by simp [hy])
  have hbNotA : ∀ w ∈ b, w ∉ a := by
    intro w hw hwa
    exact haNotB w hwa hw
  have hcoreFreshNotA : ∀ w ∈
      shiftWires offset (layout.out ++ layout.work), w ∉ a := by
    intro w hw hwa
    have hcross := hshiftCross (xs := layout.lhs)
      (ys := layout.out ++ layout.work) (by
        intro x hx y hy
        exact hlhsCross x hx y
          (List.mem_append_right _ hy))
    exact hcross w hwa hw
  have hcoreFreshNotB : ∀ w ∈
      shiftWires offset (layout.out ++ layout.work), w ∉ b := by
    intro w hw hwb
    have hcross := hshiftCross (xs := layout.rhs)
      (ys := layout.out ++ layout.work) hrhsCross
    exact hcross w hwb hw
  have hcleanA : Clean a st := by
    intro w hw
    exact hcleanEngine w (haSubset w hw)
  have hvalueAloaded : regValue a loadedA = regValue input st := by
    exact Arithmetic.copyReg_correct input a st
      (by simpa [a, shiftWires] using hinputLength.symm)
      (by simpa [a] using hcopyANodup) hcleanA
  have hcleanBLoadedA : Clean b loadedA := by
    intro w hw
    change Classical.run loadA st w = false
    rw [Arithmetic.copyReg_other w input a st (hbNotA w hw)]
    exact hcleanEngine w (hbSubset w hw)
  have hvalueBInitialized : regValue b initialized = constant := by
    exact loadConst_correct b constant loadedA
      (shiftWires_nodup offset layout.rhs hrhsNodup)
      hcleanBLoadedA (by simpa [b, shiftWires] using hconstantFits)
  have hvalueAInitialized :
      regValue a initialized = regValue input st := by
    calc
      regValue a initialized = regValue a loadedA := by
        exact loadConst_regValue a b constant loadedA haNotB
      _ = regValue input st := hvalueAloaded
  have hcleanCore :
      Clean (layout.out ++ layout.work)
        (shiftedView offset initialized) := by
    intro w hw
    change initialized (offset + w) = false
    have hshiftMem : offset + w ∈
        shiftWires offset (layout.out ++ layout.work) := by
      simp only [shiftWires, List.mem_map]
      exact ⟨w, hw, rfl⟩
    change Classical.run loadB loadedA (offset + w) = false
    rw [loadConst_other (offset + w) b constant loadedA
      (hcoreFreshNotB _ hshiftMem)]
    change Classical.run loadA st (offset + w) = false
    rw [Arithmetic.copyReg_other (offset + w) input a st
      (hcoreFreshNotA _ hshiftMem)]
    apply hcleanEngine
    exact shiftWires_mono offset (by
      intro v hv
      simp only [List.mem_append] at hv
      rcases hv with hv | hv
      · simp [RegisterLayout.allWires, hv]
      · simp [RegisterLayout.allWires, hv])
      (offset + w) hshiftMem
  have hinputA :
      regValue layout.lhs (shiftedView offset initialized) =
        regValue input st := by
    rw [← regValue_shiftWires]
    simpa [a] using hvalueAInitialized
  have hinputB :
      regValue layout.rhs (shiftedView offset initialized) =
        constant := by
    rw [← regValue_shiftWires]
    simpa [b] using hvalueBInitialized
  have hcorrect := spec.correct
    (shiftedView offset initialized) hlayout
    (by simpa [hinputA] using hinputBound)
    (by simpa [hinputB] using hconstantBound)
    hcleanCore
  dsimp only at hcorrect
  dsimp only
  rw [Classical.run_append]
  change regValue (shiftWires offset layout.out)
      (Classical.run (shiftCircuit offset core) initialized) = _
  calc
    regValue (shiftWires offset layout.out)
        (Classical.run (shiftCircuit offset core) initialized) =
        regValue layout.out
          (shiftedView offset
            (Classical.run (shiftCircuit offset core) initialized)) :=
      regValue_shiftWires offset layout.out _
    _ = regValue layout.out
          (Classical.run core (shiftedView offset initialized)) := by
      rw [shiftedView_runShiftCircuit]
    _ = op (regValue input st) constant % modulus := by
      simpa [hinputA, hinputB] using hcorrect.2.2.1

private theorem pointAddFieldRegister_length
    (workStart : Wire) (register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register) :
    register.length = fieldWidth := by
  rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [pointAddX, pointAddY, pointAddT0, pointAddT1,
      pointAddT2, pointAddT3, pointAddT4]

private theorem pointAddFieldRegister_disjoint
    (workStart : Wire) (left right : List Wire)
    (hleft : IsPointAddFieldRegister workStart left)
    (hright : IsPointAddFieldRegister workStart right)
    (hne : left ≠ right) :
    ModExp.Schedule.WireDisjoint left right := by
  intro x hx y hy
  rcases hleft with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hright with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [pointAddX, pointAddY, pointAddT0, pointAddT1,
      pointAddT2, pointAddT3, pointAddT4,
      List.mem_range'_1, fieldWidth,
      Secp256k1Instance.fieldWidth]
  all_goals
    intro heq
    subst y
    omega

private theorem pointAddEngine_field_disjoint
    (workStart : Wire) (engine register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register) :
    ModExp.Schedule.WireDisjoint
      (shiftWires (pointAddArithmeticOffset workStart) engine)
      register := by
  intro shifted hshifted fieldWire hfieldWire
  have hlower := shiftWires_lower
    (pointAddArithmeticOffset workStart) engine shifted hshifted
  have hupper := pointAddFieldRegister_belowArithmetic
    workStart register hregister fieldWire hfieldWire
  intro heq
  subst fieldWire
  exact (Nat.not_lt_of_ge hlower) hupper

private theorem secpAddLayout_valid :
    Secp256k1Instance.secpAddLayout.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Secp256k1Instance.secpAddLayout,
      Secp256k1Instance.reg, Secp256k1Instance.regBlock,
      Secp256k1Instance.fieldWidth]
  · simp [Secp256k1Instance.secpAddLayout,
      Secp256k1Instance.reg, Secp256k1Instance.regBlock,
      Secp256k1Instance.fieldWidth]
  · have hall := Secp256k1Instance.blocksWires_nodup
      [Secp256k1Instance.regBlock 0,
        Secp256k1Instance.regBlock 1,
        Secp256k1Instance.regBlock 2,
        Secp256k1Instance.regBlock 3,
        Secp256k1Instance.regBlock 4,
        Secp256k1Instance.regBlock 5,
        Secp256k1Instance.bitBlock 6,
        Secp256k1Instance.regBlock 7,
        Secp256k1Instance.bitBlock 8,
        Secp256k1Instance.regBlock 9]
      (by norm_num)
    simpa [Secp256k1Instance.secpAddLayout,
      RegisterLayout.allWires, Secp256k1Instance.baseId,
      Secp256k1Instance.exponentId, Secp256k1Instance.outId,
      Secp256k1Instance.initialAccId,
      Secp256k1Instance.addWork,
      Secp256k1Instance.addScratchBlocks,
      Secp256k1Instance.blocksWires,
      Secp256k1Instance.bitBlock_wires,
      List.append_assoc] using hall

private def fieldSubLayout : RegisterLayout :=
  modSubLayout
    (Secp256k1Instance.reg 0).wires
    (Secp256k1Instance.reg 1).wires
    (Secp256k1Instance.reg 2).wires
    (Secp256k1Instance.reg 3).wires
    (Secp256k1Instance.reg 4).wires
    (Secp256k1Instance.reg 5).wires
    (Secp256k1Instance.bitWire 6)
    (Secp256k1Instance.reg 7).wires
    (Secp256k1Instance.bitWire 8)
    (Secp256k1Instance.reg 9).wires

private theorem fieldSubLayout_valid : fieldSubLayout.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · simp [fieldSubLayout, modSubLayout,
      Secp256k1Instance.reg, Secp256k1Instance.regBlock,
      Secp256k1Instance.fieldWidth]
  · simp [fieldSubLayout, modSubLayout,
      Secp256k1Instance.reg, Secp256k1Instance.regBlock,
      Secp256k1Instance.fieldWidth]
  · have hall := Secp256k1Instance.blocksWires_nodup
      [Secp256k1Instance.regBlock 0,
        Secp256k1Instance.regBlock 1,
        Secp256k1Instance.regBlock 2,
        Secp256k1Instance.regBlock 3,
        Secp256k1Instance.regBlock 4,
        Secp256k1Instance.regBlock 5,
        Secp256k1Instance.bitBlock 6,
        Secp256k1Instance.regBlock 7,
        Secp256k1Instance.bitBlock 8,
        Secp256k1Instance.regBlock 9]
      (by norm_num)
    simpa [fieldSubLayout, modSubLayout,
      RegisterLayout.allWires,
      Secp256k1Instance.blocksWires,
      Secp256k1Instance.bitBlock_wires,
      List.append_assoc] using hall

private def fieldSubWiring :
    ModSubWiring
      (Secp256k1Instance.reg 0).wires
      (Secp256k1Instance.reg 1).wires
      (Secp256k1Instance.reg 2).wires
      (Secp256k1Instance.reg 3).wires
      (Secp256k1Instance.reg 4).wires
      (Secp256k1Instance.reg 5).wires
      (Secp256k1Instance.bitWire 6)
      (Secp256k1Instance.reg 7).wires
      (Secp256k1Instance.bitWire 8)
      (Secp256k1Instance.reg 9).wires p := by
  refine {
    rhsLen := by simp [Secp256k1Instance.reg,
      Secp256k1Instance.regBlock]
    rawLen := by simp [Secp256k1Instance.reg,
      Secp256k1Instance.regBlock]
    subLen := by simp [Secp256k1Instance.reg,
      Secp256k1Instance.regBlock]
    constLen := by simp [Secp256k1Instance.reg,
      Secp256k1Instance.regBlock]
    candidateLen := by simp [Secp256k1Instance.reg,
      Secp256k1Instance.regBlock]
    addLen := by simp [Secp256k1Instance.reg,
      Secp256k1Instance.regBlock]
    outLen := by simp [Secp256k1Instance.reg,
      Secp256k1Instance.regBlock]
    subOK := Secp256k1Instance.secpAddWiring.addOK
    addOK := Secp256k1Instance.secpAddWiring.redOK
    selectOK := ?_
    modulusPos := Secp256k1Instance.p_pos
    fit := ?_
  }
  · apply ModExp.selectOK_of_nodup
    have hall := Secp256k1Instance.blocksWires_nodup
      [Secp256k1Instance.regBlock 7,
        Secp256k1Instance.regBlock 5,
        Secp256k1Instance.regBlock 3,
        Secp256k1Instance.regBlock 2]
      (by norm_num)
    have hshape :
        ((Secp256k1Instance.reg 7).wires ++
          ((Secp256k1Instance.reg 5).wires ++
            (Secp256k1Instance.reg 3).wires ++
            (Secp256k1Instance.reg 2).wires)).Nodup := by
      simpa [Secp256k1Instance.blocksWires,
        List.append_assoc] using hall
    obtain ⟨_, hbody, hcross⟩ := List.nodup_append.mp hshape
    apply List.nodup_cons.mpr
    refine ⟨?_, hbody⟩
    intro hmem
    exact hcross _
      (Secp256k1Instance.carryOut_mem_of_nonempty
        (Secp256k1Instance.bitWire 6)
        (Secp256k1Instance.reg 7).wires
        (by
          simp [Secp256k1Instance.reg,
            Secp256k1Instance.regBlock,
            Secp256k1Instance.Block.wires,
            Secp256k1Instance.fieldWidth]))
      _ hmem rfl
  · rw [(Secp256k1Instance.reg 0).length_eq]
    have hfit := Secp256k1Instance.p_fits
    have hpos := Secp256k1Instance.p_pos
    omega

private theorem fieldSub_contract :
    ModSubContract fieldSubCore fieldSubLayout p
      (91 * (Secp256k1Instance.reg 0).wires.length) := by
  simpa [fieldSubCore, fieldSubLayout] using
    (modSub_contract
      (Secp256k1Instance.reg 0).wires
      (Secp256k1Instance.reg 1).wires
      (Secp256k1Instance.reg 2).wires
      (Secp256k1Instance.reg 3).wires
      (Secp256k1Instance.reg 4).wires
      (Secp256k1Instance.reg 5).wires
      (Secp256k1Instance.bitWire 6)
      (Secp256k1Instance.reg 7).wires
      (Secp256k1Instance.bitWire 8)
      (Secp256k1Instance.reg 9).wires p fieldSubWiring)

private theorem pointAddBinaryField_correct
    (core : Circuit) (layout : RegisterLayout)
    (modulus : Nat) (op : Nat → Nat → Nat) (cost : Nat)
    (spec : CleanBinaryContract core layout modulus op cost)
    (hlayout : layout.Valid)
    (hlayoutWidth : layout.lhs.length = fieldWidth)
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out)
    (houtLhs : out ≠ lhs) (houtRhs : out ≠ rhs)
    (st : BasisState)
    (hcleanOut : Clean out st)
    (hcleanEngine : Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        layout.allWires) st)
    (hlhsBound : regValue lhs st < modulus)
    (hrhsBound : regValue rhs st < modulus) :
    let offset := pointAddArithmeticOffset workStart
    let a := shiftWires offset layout.lhs
    let b := shiftWires offset layout.rhs
    let result := shiftWires offset layout.out
    let placedCore := shiftCircuit offset core
    let after := Classical.run
      (Arithmetic.copyReg lhs a ++
        Arithmetic.copyReg rhs b ++
        placedCore ++
        Arithmetic.copyReg result out ++
        placedCore.reverse ++
        Arithmetic.copyReg rhs b ++
        Arithmetic.copyReg lhs a) st
    regValue out after =
        op (regValue lhs st) (regValue rhs st) % modulus ∧
      ∀ w, w ∉ out → after w = st w := by
  let offset := pointAddArithmeticOffset workStart
  let a := shiftWires offset layout.lhs
  let b := shiftWires offset layout.rhs
  let result := shiftWires offset layout.out
  let active := shiftWires offset layout.allWires
  let placedCore := shiftCircuit offset core
  have hshape :
      (layout.lhs ++
        (layout.rhs ++ (layout.out ++ layout.work))).Nodup := by
    simpa [RegisterLayout.allWires, List.append_assoc] using hlayout.2.2
  obtain ⟨hlhsNodup, htailLhs, hlhsCross⟩ :=
    List.nodup_append.mp hshape
  obtain ⟨hrhsNodup, htailRhs, hrhsCross⟩ :=
    List.nodup_append.mp htailLhs
  obtain ⟨houtNodup, hworkNodup, houtCross⟩ :=
    List.nodup_append.mp htailRhs
  have haActive : ∀ w ∈ a, w ∈ active := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hbActive : ∀ w ∈ b, w ∈ active := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hresultActive : ∀ w ∈ result, w ∈ active := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hactiveOut : ModExp.Schedule.WireDisjoint active out := by
    simpa [active, offset] using
      pointAddEngine_field_disjoint workStart layout.allWires out hout
  have hlhsOut : ModExp.Schedule.WireDisjoint lhs out :=
    pointAddFieldRegister_disjoint workStart lhs out hlhs hout
      houtLhs.symm
  have hrhsOut : ModExp.Schedule.WireDisjoint rhs out :=
    pointAddFieldRegister_disjoint workStart rhs out hrhs hout
      houtRhs.symm
  have hcopyANodup : (lhs ++ a).Nodup := by
    simpa [a, offset] using pointAddField_shifted_nodup
      workStart lhs layout.lhs hlhs hlhsNodup
  have hcopyBNodup : (rhs ++ b).Nodup := by
    simpa [b, offset] using pointAddField_shifted_nodup
      workStart rhs layout.rhs hrhs hrhsNodup
  have hresultOutNodup : (result ++ out).Nodup := by
    simpa [result, offset] using shifted_pointAddField_nodup
      workStart layout.out out hout houtNodup
  have hresultLength : out.length = result.length := by
    rw [pointAddFieldRegister_length workStart out hout]
    simp only [result, shiftWires, List.length_map]
    exact hlayoutWidth.symm.trans hlayout.2.1
  have hstruct := binaryBennettWrapper_correct
    lhs rhs out a b result active placedCore st
    haActive hbActive hresultActive
    (by simpa [active, placedCore, offset] using
      shiftCircuit_usesOnly offset layout.allWires core spec.usesOnly)
    (by simpa [placedCore, offset] using
      shiftCircuit_HPFree offset core spec.hpFree)
    (by simpa [placedCore, offset] using
      shiftCircuit_wellFormed offset core (spec.wellFormed hlayout))
    hactiveOut hlhsOut hrhsOut hresultLength
    hresultOutNodup hcopyANodup hcopyBNodup hcleanOut
  dsimp only at hstruct
  have hsourceValue :
      regValue result
          (Classical.run placedCore
            (Classical.run
              (Arithmetic.copyReg lhs a ++
                Arithmetic.copyReg rhs b) st)) =
        op (regValue lhs st) (regValue rhs st) % modulus := by
    simpa [result, placedCore, a, b, active, offset] using
      shiftedBinaryCore_correct core layout modulus op cost spec hlayout
        offset lhs rhs st
        (by
          rw [pointAddFieldRegister_length workStart lhs hlhs]
          exact hlayoutWidth.symm)
        (by
          rw [pointAddFieldRegister_length workStart rhs hrhs]
          exact hlayoutWidth.symm.trans hlayout.1)
        (by simpa [a, offset] using hcopyANodup)
        (by simpa [b, offset] using hcopyBNodup)
        (by
          simpa [active, offset] using
            pointAddEngine_field_disjoint
              workStart layout.allWires rhs hrhs)
        (by simpa [active] using hcleanEngine)
        hlhsBound hrhsBound
  have hresultValue := hstruct.1.trans hsourceValue
  dsimp only
  constructor
  · simpa [offset, a, b, result, active, placedCore,
      List.append_assoc] using hresultValue
  · intro w hw
    simpa [offset, a, b, result, active, placedCore,
      List.append_assoc] using hstruct.2 w hw

private theorem pointAddUnaryConstField_correct
    (core : Circuit) (layout : RegisterLayout)
    (modulus : Nat) (op : Nat → Nat → Nat) (cost : Nat)
    (spec : CleanBinaryContract core layout modulus op cost)
    (hlayout : layout.Valid)
    (hlayoutWidth : layout.lhs.length = fieldWidth)
    (workStart : Wire) (input out : List Wire) (constant : Nat)
    (hinput : IsPointAddFieldRegister workStart input)
    (hout : IsPointAddFieldRegister workStart out)
    (houtInput : out ≠ input)
    (st : BasisState)
    (hcleanOut : Clean out st)
    (hcleanEngine : Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        layout.allWires) st)
    (hinputBound : regValue input st < modulus)
    (hconstantBound : constant < modulus)
    (hconstantFits : constant < 2 ^ layout.rhs.length) :
    let offset := pointAddArithmeticOffset workStart
    let a := shiftWires offset layout.lhs
    let b := shiftWires offset layout.rhs
    let result := shiftWires offset layout.out
    let placedCore := shiftCircuit offset core
    let after := Classical.run
      (Arithmetic.copyReg input a ++
        loadConst b constant ++
        placedCore ++
        Arithmetic.copyReg result out ++
        placedCore.reverse ++
        loadConst b constant ++
        Arithmetic.copyReg input a) st
    regValue out after =
        op (regValue input st) constant % modulus ∧
      ∀ w, w ∉ out → after w = st w := by
  let offset := pointAddArithmeticOffset workStart
  let a := shiftWires offset layout.lhs
  let b := shiftWires offset layout.rhs
  let result := shiftWires offset layout.out
  let active := shiftWires offset layout.allWires
  let placedCore := shiftCircuit offset core
  have hshape :
      (layout.lhs ++
        (layout.rhs ++ (layout.out ++ layout.work))).Nodup := by
    simpa [RegisterLayout.allWires, List.append_assoc] using hlayout.2.2
  obtain ⟨hlhsNodup, htailLhs, hlhsCross⟩ :=
    List.nodup_append.mp hshape
  obtain ⟨hrhsNodup, htailRhs, hrhsCross⟩ :=
    List.nodup_append.mp htailLhs
  obtain ⟨houtNodup, hworkNodup, houtCross⟩ :=
    List.nodup_append.mp htailRhs
  have haActive : ∀ w ∈ a, w ∈ active := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hbActive : ∀ w ∈ b, w ∈ active := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hresultActive : ∀ w ∈ result, w ∈ active := by
    apply shiftWires_mono
    intro w hw
    simp [RegisterLayout.allWires, hw]
  have hactiveOut : ModExp.Schedule.WireDisjoint active out := by
    simpa [active, offset] using
      pointAddEngine_field_disjoint workStart layout.allWires out hout
  have hinputOut : ModExp.Schedule.WireDisjoint input out :=
    pointAddFieldRegister_disjoint workStart input out hinput hout
      houtInput.symm
  have hcopyANodup : (input ++ a).Nodup := by
    simpa [a, offset] using pointAddField_shifted_nodup
      workStart input layout.lhs hinput hlhsNodup
  have hbNodup : b.Nodup :=
    shiftWires_nodup offset layout.rhs hrhsNodup
  have hresultOutNodup : (result ++ out).Nodup := by
    simpa [result, offset] using shifted_pointAddField_nodup
      workStart layout.out out hout houtNodup
  have hresultLength : out.length = result.length := by
    rw [pointAddFieldRegister_length workStart out hout]
    simp only [result, shiftWires, List.length_map]
    exact hlayoutWidth.symm.trans hlayout.2.1
  have hstruct := unaryConstBennettWrapper_correct
    input out a b result active constant placedCore st
    haActive hbActive hresultActive
    (by simpa [active, placedCore, offset] using
      shiftCircuit_usesOnly offset layout.allWires core spec.usesOnly)
    (by simpa [placedCore, offset] using
      shiftCircuit_HPFree offset core spec.hpFree)
    (by simpa [placedCore, offset] using
      shiftCircuit_wellFormed offset core (spec.wellFormed hlayout))
    hactiveOut hinputOut hresultLength hresultOutNodup
    hcopyANodup hbNodup hcleanOut
  dsimp only at hstruct
  have hsourceValue :
      regValue result
          (Classical.run placedCore
            (Classical.run
              (Arithmetic.copyReg input a ++
                loadConst b constant) st)) =
        op (regValue input st) constant % modulus := by
    simpa [result, placedCore, a, b, active, offset] using
      shiftedUnaryConstCore_correct core layout modulus op cost
        spec hlayout offset input constant st
        (by
          rw [pointAddFieldRegister_length workStart input hinput]
          exact hlayoutWidth.symm)
        (by simpa [a, offset] using hcopyANodup)
        (by simpa [active] using hcleanEngine)
        hinputBound hconstantBound hconstantFits
  have hresultValue := hstruct.1.trans hsourceValue
  dsimp only
  constructor
  · simpa [offset, a, b, result, active, placedCore,
      List.append_assoc] using hresultValue
  · intro w hw
    simpa [offset, a, b, result, active, placedCore,
      List.append_assoc] using hstruct.2 w hw

private theorem fieldAdd_correct
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out)
    (houtLhs : out ≠ lhs) (houtRhs : out ≠ rhs)
    (st : BasisState)
    (hcleanOut : Clean out st)
    (hcleanEngine : Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpAddLayout.allWires) st)
    (hlhsBound : regValue lhs st < p)
    (hrhsBound : regValue rhs st < p) :
    let after := Classical.run
      (fieldAdd (pointAddArithmeticOffset workStart) lhs rhs out) st
    regValue out after =
        (regValue lhs st + regValue rhs st) % p ∧
      ∀ w, w ∉ out → after w = st w := by
  have hresult := pointAddBinaryField_correct
    Secp256k1Instance.secpAddProgram
    Secp256k1Instance.secpAddLayout
    p Nat.add Secp256k1Instance.addCost
    Secp256k1Instance.secp_modAdd_contract
    secpAddLayout_valid
    (by
      simp [Secp256k1Instance.secpAddLayout,
        Secp256k1Instance.reg, Secp256k1Instance.regBlock,
        fieldWidth, Secp256k1Instance.fieldWidth,
        Secp256k1Instance.baseId])
    workStart lhs rhs out hlhs hrhs hout houtLhs houtRhs st
    hcleanOut hcleanEngine hlhsBound hrhsBound
  dsimp only at hresult ⊢
  simpa [fieldAdd, engineAddLhs, engineAddRhs, engineAddOut,
    List.append_assoc] using hresult

private theorem fieldMul_correct
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out)
    (houtLhs : out ≠ lhs) (houtRhs : out ≠ rhs)
    (st : BasisState)
    (hcleanOut : Clean out st)
    (hcleanEngine : Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpMulLayout.allWires) st)
    (hlhsBound : regValue lhs st < p)
    (hrhsBound : regValue rhs st < p) :
    let after := Classical.run
      (fieldMul (pointAddArithmeticOffset workStart) lhs rhs out) st
    regValue out after =
        regValue lhs st * regValue rhs st % p ∧
      ∀ w, w ∉ out → after w = st w := by
  have hresult := pointAddBinaryField_correct
    Secp256k1Instance.secpMulProgram
    Secp256k1Instance.secpMulLayout
    p Nat.mul Secp256k1Instance.mulCost
    Secp256k1Instance.secp_modMul_contract
    secpMulLayout_valid
    (by
      simp [Secp256k1Instance.secpMulLayout,
        Secp256k1Instance.reg, Secp256k1Instance.regBlock,
        fieldWidth, Secp256k1Instance.fieldWidth,
        Secp256k1Instance.baseId])
    workStart lhs rhs out hlhs hrhs hout houtLhs houtRhs st
    hcleanOut hcleanEngine hlhsBound hrhsBound
  dsimp only at hresult ⊢
  simpa [fieldMul, engineMulLhs, engineMulRhs, engineMulOut,
    List.append_assoc] using hresult

private theorem fieldSub_correct
    (workStart : Wire) (lhs rhs out : List Wire)
    (hlhs : IsPointAddFieldRegister workStart lhs)
    (hrhs : IsPointAddFieldRegister workStart rhs)
    (hout : IsPointAddFieldRegister workStart out)
    (houtLhs : out ≠ lhs) (houtRhs : out ≠ rhs)
    (st : BasisState)
    (hcleanOut : Clean out st)
    (hcleanEngine : Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        fieldSubLayout.allWires) st)
    (hlhsBound : regValue lhs st < p)
    (hrhsBound : regValue rhs st < p) :
    let after := Classical.run
      (fieldSub (pointAddArithmeticOffset workStart) lhs rhs out) st
    regValue out after =
        (regValue lhs st + p - regValue rhs st) % p ∧
      ∀ w, w ∉ out → after w = st w := by
  have hresult := pointAddBinaryField_correct
    fieldSubCore fieldSubLayout p
    (fun lhs rhs => lhs + p - rhs)
    (91 * (Secp256k1Instance.reg 0).wires.length)
    fieldSub_contract fieldSubLayout_valid
    (by
      simp [fieldSubLayout, modSubLayout,
        Secp256k1Instance.reg, Secp256k1Instance.regBlock,
        fieldWidth, Secp256k1Instance.fieldWidth])
    workStart lhs rhs out hlhs hrhs hout houtLhs houtRhs st
    hcleanOut hcleanEngine hlhsBound hrhsBound
  dsimp only at hresult ⊢
  simpa [fieldSub, engineSubLhs, engineSubRhs, engineSubOut,
    List.append_assoc] using hresult

set_option exponentiation.threshold 300 in
private theorem fieldSubConst_correct
    (workStart : Wire) (input out : List Wire) (constant : Nat)
    (hinput : IsPointAddFieldRegister workStart input)
    (hout : IsPointAddFieldRegister workStart out)
    (houtInput : out ≠ input)
    (st : BasisState)
    (hcleanOut : Clean out st)
    (hcleanEngine : Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        fieldSubLayout.allWires) st)
    (hinputBound : regValue input st < p)
    (hconstantBound : constant < p) :
    let after := Classical.run
      (fieldSubConst
        (pointAddArithmeticOffset workStart) input constant out) st
    regValue out after =
        (regValue input st + p - constant) % p ∧
      ∀ w, w ∉ out → after w = st w := by
  have hconstantFits : constant < 2 ^ fieldSubLayout.rhs.length := by
    have hpFit := Secp256k1Instance.p_fits
    have hpPos := Secp256k1Instance.p_pos
    have hpPow : p < 2 ^ Secp256k1Instance.fieldWidth := by
      omega
    simpa [fieldSubLayout, modSubLayout,
      Secp256k1Instance.reg, Secp256k1Instance.regBlock,
      Secp256k1Instance.fieldWidth] using hconstantBound.trans hpPow
  have hresult := pointAddUnaryConstField_correct
    fieldSubCore fieldSubLayout p
    (fun lhs rhs => lhs + p - rhs)
    (91 * (Secp256k1Instance.reg 0).wires.length)
    fieldSub_contract fieldSubLayout_valid
    (by
      simp [fieldSubLayout, modSubLayout,
        Secp256k1Instance.reg, Secp256k1Instance.regBlock,
        fieldWidth, Secp256k1Instance.fieldWidth])
    workStart input out constant hinput hout houtInput st
    hcleanOut hcleanEngine hinputBound hconstantBound hconstantFits
  dsimp only at hresult ⊢
  simpa [fieldSubConst, engineSubLhs, engineSubRhs, engineSubOut,
    List.append_assoc] using hresult

set_option exponentiation.threshold 300 in
private theorem fieldInv_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire) (input out : List Wire)
    (hinput : IsPointAddFieldRegister workStart input)
    (hout : IsPointAddFieldRegister workStart out)
    (houtInput : out ≠ input)
    (st : BasisState)
    (hcleanOut : Clean out st)
    (hcleanEngine : Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpLayout.allWires) st)
    (hinputBound : regValue input st < p)
    (hnonzero : ((regValue input st : Nat) : Fp) ≠ 0) :
    let after := Classical.run
      (fieldInv (pointAddArithmeticOffset workStart) input out) st
    regValue out after =
        (((regValue input st : Nat) : Fp)⁻¹).val ∧
      ∀ w, w ∉ out → after w = st w := by
  have hpTwo : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
  have hexponentBound : p - 2 < p := by omega
  have hpPow : p < 2 ^ Secp256k1Instance.fieldWidth := by
    have hfit := Secp256k1Instance.p_fits
    have hpos := Secp256k1Instance.p_pos
    omega
  have hexponentFits : p - 2 <
      2 ^ Secp256k1Instance.secpLayout.rhs.length := by
    exact hexponentBound.trans (by
      simpa [Secp256k1Instance.secpLayout, ModExp.Plan.layout,
        Secp256k1Instance.secpPlan,
        Secp256k1Instance.reg, Secp256k1Instance.regBlock,
        Secp256k1Instance.fieldWidth,
        Secp256k1Instance.exponentId] using hpPow)
  have hresult := pointAddUnaryConstField_correct
    Secp256k1Instance.secpProgram
    Secp256k1Instance.secpLayout p Nat.pow
    Secp256k1Instance.secpCost
    Secp256k1Instance.secp_modExp_contract
    Secp256k1Instance.secpPlan_layout_valid
    (by
      simp [Secp256k1Instance.secpLayout, ModExp.Plan.layout,
        Secp256k1Instance.secpPlan,
        Secp256k1Instance.reg, Secp256k1Instance.regBlock,
        fieldWidth, Secp256k1Instance.fieldWidth,
        Secp256k1Instance.baseId])
    workStart input out (p - 2) hinput hout houtInput st
    hcleanOut hcleanEngine hinputBound hexponentBound hexponentFits
  dsimp only at hresult ⊢
  have hpowLt :
      regValue input st ^ (p - 2) % p < p :=
    Nat.mod_lt _ Secp256k1Instance.p_pos
  have hcast :
      ((regValue input st ^ (p - 2) % p : Nat) : Fp) =
        ((regValue input st : Nat) : Fp)⁻¹ := by
    calc
      ((regValue input st ^ (p - 2) % p : Nat) : Fp) =
          ((regValue input st : Nat) : Fp) ^ (p - 2) := by
        simp
      _ = ((regValue input st : Nat) : Fp)⁻¹ :=
        fermat_inv _ hnonzero
  have hpowVal :
      regValue input st ^ (p - 2) % p =
        (((regValue input st : Nat) : Fp)⁻¹).val := by
    have hval := congrArg (fun z : Fp => z.val) hcast
    simpa only [ZMod.val_natCast_of_lt hpowLt] using hval
  exact ⟨hresult.1.trans hpowVal, hresult.2⟩

/-! -------------------------------------------------------------------------
    Sequential field-operation semantics

The affine programs reuse one arithmetic engine.  These facts extract the
three concrete engine footprints from the branch-cleanliness hypothesis and
package the small Bennett step used when an intermediate value is kept while
its preparation is uncomputed.
------------------------------------------------------------------------- -/

private theorem fieldSubLayout_allWires_eq :
    fieldSubLayout.allWires =
      Secp256k1Instance.secpAddLayout.allWires := by
  simp [fieldSubLayout, modSubLayout,
    Secp256k1Instance.secpAddLayout,
    RegisterLayout.allWires,
    Secp256k1Instance.addWork,
    Secp256k1Instance.addScratchBlocks,
    Secp256k1Instance.blocksWires,
    Secp256k1Instance.bitBlock_wires,
    Secp256k1Instance.baseId,
    Secp256k1Instance.exponentId,
    Secp256k1Instance.outId,
    Secp256k1Instance.initialAccId,
    List.append_assoc]

private theorem cleanAddEngine_of_branchWork
    (workStart : Wire) (st : BasisState)
    (hclean : Clean (pointAddBranchWork workStart) st) :
    Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpAddLayout.allWires) st := by
  intro w hw
  apply hclean w
  simp [pointAddBranchWork, pointAddArithmeticWork,
    List.mem_dedup, hw]

private theorem cleanMulEngine_of_branchWork
    (workStart : Wire) (st : BasisState)
    (hclean : Clean (pointAddBranchWork workStart) st) :
    Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpMulLayout.allWires) st := by
  intro w hw
  apply hclean w
  simp [pointAddBranchWork, pointAddArithmeticWork,
    List.mem_dedup, hw]

private theorem cleanInvEngine_of_branchWork
    (workStart : Wire) (st : BasisState)
    (hclean : Clean (pointAddBranchWork workStart) st) :
    Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpLayout.allWires) st := by
  intro w hw
  apply hclean w
  simp [pointAddBranchWork, pointAddArithmeticWork,
    List.mem_dedup, hw]

private theorem clean_fieldSubEngine_of_addEngine
    (workStart : Wire) (st : BasisState)
    (hclean : Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        Secp256k1Instance.secpAddLayout.allWires) st) :
    Clean
      (shiftWires (pointAddArithmeticOffset workStart)
        fieldSubLayout.allWires) st := by
  simpa [fieldSubLayout_allWires_eq] using hclean

private theorem clean_of_preserved_outside
    {register out : List Wire} {before after : BasisState}
    (hdisjoint : ModExp.Schedule.WireDisjoint register out)
    (hclean : Clean register before)
    (hpreserve : ∀ w, w ∉ out → after w = before w) :
    Clean register after := by
  intro w hw
  rw [hpreserve w (by
    intro hout
    exact hdisjoint w hw w hout rfl)]
  exact hclean w hw

private theorem regValue_of_preserved_outside
    {register out : List Wire} {before after : BasisState}
    (hdisjoint : ModExp.Schedule.WireDisjoint register out)
    (hpreserve : ∀ w, w ∉ out → after w = before w) :
    regValue register after = regValue register before := by
  apply regValue_congr
  intro w hw
  exact hpreserve w (by
    intro hout
    exact hdisjoint w hw w hout rfl)

private theorem bennett_uncompute_after_local_update
    (compute update : Circuit) (active out : List Wire)
    (st : BasisState)
    (huses : CircuitUsesOnly active compute)
    (hfree : Classical.HPFree compute)
    (hwellFormed : CircuitWellFormed compute)
    (hdisjoint : ModExp.Schedule.WireDisjoint active out)
    (hupdate : ∀ w, w ∉ out →
      Classical.run update (Classical.run compute st) w =
        Classical.run compute st w) :
    let after := Classical.run
      (compute ++ update ++ compute.reverse) st
    (∀ w, w ∉ out → after w = st w) ∧
      (∀ w ∈ out,
        after w =
          Classical.run update (Classical.run compute st) w) := by
  let mid := Classical.run compute st
  let updated := Classical.run update mid
  let after := Classical.run compute.reverse updated
  have hreverseUses : CircuitUsesOnly active compute.reverse :=
    usesOnly_reverse huses
  have hupdatedActive : ∀ w ∈ active, updated w = mid w := by
    intro w hw
    exact hupdate w (by
      intro hout
      exact hdisjoint w hw w hout rfl)
  have hcancel : Classical.run compute.reverse mid = st := by
    simpa [mid] using
      Arithmetic.run_reverse_cancel compute st hfree hwellFormed
  have hafterActive : ∀ w ∈ active, after w = st w := by
    intro w hw
    calc
      after w = Classical.run compute.reverse mid w := by
        exact CircuitUsesOnly.run_congr
          hreverseUses hupdatedActive w hw
      _ = st w := by rw [hcancel]
  have hafterOut : ∀ w ∈ out, after w = updated w := by
    intro w hw
    exact hreverseUses.preservesOutside updated w (by
      intro hactive
      exact hdisjoint w hactive w hw rfl)
  have hprogram :
      Classical.run (compute ++ update ++ compute.reverse) st = after := by
    simp [after, updated, mid, Classical.run_append]
  dsimp only
  rw [hprogram]
  constructor
  · intro w hw
    by_cases hactive : w ∈ active
    · exact hafterActive w hactive
    · calc
        after w = updated w :=
          hreverseUses.preservesOutside updated w hactive
        _ = mid w := hupdate w hw
        _ = st w := huses.preservesOutside st w hactive
  · exact hafterOut

private theorem fieldSubVal (left right : Fp) :
    (left.val + p - right.val) % p = (left - right).val := by
  have hle : right.val ≤ left.val + p :=
    le_trans right.val_le (Nat.le_add_left p left.val)
  have hcast :
      ((left.val + p - right.val : Nat) : Fp) = left - right := by
    rw [Nat.cast_sub hle]
    simp
  have hval := congrArg ZMod.val hcast
  simpa [ZMod.val_natCast] using hval

private theorem regValue_take_mod
    (count : Nat) (register : List Wire) (st : BasisState) :
    regValue (register.take count) st =
      regValue register st % 2 ^ count := by
  induction count generalizing register with
  | zero =>
      simp only [List.take_zero, regValue_nil, Nat.pow_zero, Nat.mod_one]
  | succ count ih =>
      cases register with
      | nil => simp
      | cons w register =>
          rw [List.take_succ_cons, regValue_cons, regValue_cons, ih,
            Nat.pow_succ, Nat.mul_comm (2 ^ count) 2]
          let bit : Nat := if st w = true then 1 else 0
          have hbit : bit < 2 := by
            dsimp [bit]
            split <;> omega
          have hpow : 0 < 2 ^ count := pow_pos (by omega) _
          have hmod : regValue register st % 2 ^ count < 2 ^ count :=
            Nat.mod_lt _ hpow
          change bit + 2 * (regValue register st % 2 ^ count) =
            (bit + 2 * regValue register st) % (2 * 2 ^ count)
          have hbitmod : bit % (2 * 2 ^ count) = bit :=
            Nat.mod_eq_of_lt (by omega)
          have hmul : 2 * regValue register st % (2 * 2 ^ count) =
              2 * (regValue register st % 2 ^ count) :=
            Nat.mul_mod_mul_left 2 _ _
          have hsum : bit + 2 * (regValue register st % 2 ^ count) <
              2 * 2 ^ count := by omega
          calc
            bit + 2 * (regValue register st % 2 ^ count) =
                (bit % (2 * 2 ^ count) +
                  2 * regValue register st % (2 * 2 ^ count)) %
                    (2 * 2 ^ count) := by
              rw [hbitmod, hmul, Nat.mod_eq_of_lt hsum]
            _ = (bit + 2 * regValue register st) %
                (2 * 2 ^ count) :=
              (Nat.add_mod bit (2 * regValue register st)
                (2 * 2 ^ count)).symm

private theorem pointAddFieldAt_ne
    (workStart left right : Nat) (hne : left ≠ right) :
    List.range' (workStart + left * fieldWidth) fieldWidth ≠
      List.range' (workStart + right * fieldWidth) fieldWidth := by
  intro heq
  have hstart := (List.range'_inj.mp heq).2.resolve_left (by
    norm_num [fieldWidth, Secp256k1Instance.fieldWidth])
  apply hne
  norm_num [fieldWidth, Secp256k1Instance.fieldWidth] at hstart ⊢
  omega

private theorem pointAddFieldAt_disjoint
    (workStart left right : Nat) (hne : left ≠ right) :
    ModExp.Schedule.WireDisjoint
      (List.range' (workStart + left * fieldWidth) fieldWidth)
      (List.range' (workStart + right * fieldWidth) fieldWidth) := by
  intro leftWire hleft rightWire hright heq
  have hleftBounds := List.mem_range'_1.mp hleft
  have hrightBounds := List.mem_range'_1.mp hright
  subst rightWire
  norm_num [fieldWidth, Secp256k1Instance.fieldWidth]
    at hleftBounds hrightBounds ⊢
  omega

private theorem pointAddCandidate_field_disjoint
    (workStart : Wire) (register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register) :
    ModExp.Schedule.WireDisjoint
      (pointAddCandidate workStart) register := by
  intro candidate hcandidate fieldWire hfieldWire heq
  have hcandidateBounds := List.mem_range'_1.mp hcandidate
  have hfieldUpper := pointAddFieldRegister_belowFlagArea
    workStart register hregister fieldWire hfieldWire
  have hlower : workStart + flagOffset ≤ candidate := by
    have hoffset : flagOffset ≤ candidateOffset := by
      rw [candidateOffset]
      omega
    exact (Nat.add_le_add_left hoffset workStart).trans
      hcandidateBounds.1
  exact (Nat.not_lt_of_ge hlower) (by
    rw [heq]
    exact hfieldUpper)

private theorem offset_lt_le_false
    (start w leftEnd rightStart : Nat)
    (hupper : w < start + leftEnd)
    (hlower : start + rightStart ≤ w)
    (hgap : leftEnd ≤ rightStart) : False := by
  omega

private theorem offset_ne
    (start left right : Nat)
    (hne : left ≠ right) :
    start + left ≠ start + right := by
  omega

theorem pointAddFlags_semantics
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hcleanFlags :
      Clean (pointAddFlagWork workStart) st)
    (hcleanBranch :
      Clean (pointAddBranchWork workStart) st) :
    let after :=
      Classical.run
        (pointAddFlags pointReg workStart xC yC)
        st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) st ∧
      regValue (pointAddY workStart) after =
        regValue (pointAddY workStart) st ∧
      after (pointAddInfinityFlag workStart) =
        decide (regValue (PointRegister.tag pointReg) st = 0) ∧
      after (pointAddGenericFlag workStart) =
        decide (
          regValue (PointRegister.tag pointReg) st ≠ 0 ∧
          regValue (PointRegister.x pointReg) st ≠ xC.val) ∧
      after (pointAddDoubleFlag workStart) =
        decide (
          regValue (PointRegister.tag pointReg) st ≠ 0 ∧
          regValue (PointRegister.x pointReg) st = xC.val ∧
          regValue (PointRegister.y pointReg) st ≠ (-yC).val) ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp

  have hlocalSizeEq : localWorkSize = 4112 := by
    norm_num [localWorkSize, selectedOffset, candidateOffset,
      flagOffset, yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
      constOffset, fieldAreaSize, fieldWidth,
      Secp256k1Instance.fieldWidth, pointWidth]

  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup

  have hpointWork :
      ∀ a ∈ pointReg, ∀ b ∈ pointAddWork workStart,
        a ≠ b := by
    intro a ha b hb hEq
    exact hpublicWork a
      (List.mem_append_left outReg ha) b hb hEq

  have hflagWorkSubset :
      ∀ w ∈ pointAddFlagWork workStart,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    rw [hlocalSizeEq]
    simp only [pointAddFlagWork, pointAddConst,
      pointAddZeroHistory, pointAddXDifference,
      pointAddXHistory, pointAddYDifference,
      pointAddYHistory, pointAddInfinityFlag,
      pointAddXEqFlag, pointAddYNegFlag,
      pointAddGenericFlag, pointAddPairFlag,
      pointAddDoubleFlag, List.mem_append,
      List.mem_cons, List.mem_range'_1] at hw
    norm_num [flagOffset, yHistoryOffset,
      yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset,
      constOffset, fieldAreaSize, fieldWidth,
      Secp256k1Instance.fieldWidth] at hw
    rcases hw with
        (((((h0 | h1) | h2) | h3) | h4) | h5) |
          (h6 | h7 | h8 | h9 | h10 | h11)
    · constructor <;> omega
    · subst w
      constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega

  have htagNodup :
      (PointRegister.tag pointReg).Nodup := by
    apply List.Nodup.sublist (List.take_sublist 1 pointReg)
    exact hpointNodup
  have hxNodup :
      (PointRegister.x pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 1)).trans
        (List.drop_sublist 1 pointReg))
    exact hpointNodup
  have hyNodup :
      (PointRegister.y pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 257)).trans
        (List.drop_sublist 257 pointReg))
    exact hpointNodup

  have hzeroNodup :
      (zeroFlagWires
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart)).Nodup := by
    rw [zeroFlagWires]
    apply List.nodup_append.mpr
    refine ⟨htagNodup,
      pointAddZeroFlagWork_nodup workStart, ?_⟩
    intro a ha b hb hEq
    have hbFlagWork : b ∈ pointAddFlagWork workStart := by
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hhistory
      · simp [pointAddFlagWork]
      · simp [pointAddFlagWork, hhistory]
    exact hpointWork a (List.mem_of_mem_take ha) b
      (hflagWorkSubset b hbFlagWork) hEq

  have hxEqualNodup :
      (equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart)).Nodup := by
    have hwork := pointAddXEqualWork_nodup workStart
    have hcombined :
        (PointRegister.x pointReg ++
          ((pointAddConst workStart ++
              pointAddXDifference workStart) ++
            pointAddXEqFlag workStart ::
              pointAddXHistory workStart)).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hxNodup, hwork, ?_⟩
      intro a ha b hb hEq
      have hbFlagWork : b ∈ pointAddFlagWork workStart := by
        simp only [List.mem_append, List.mem_cons] at hb
        rcases hb with (hconst | hdiff) | hflag | hhistory
        · simp [pointAddFlagWork, hconst]
        · simp [pointAddFlagWork, hdiff]
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork a
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)) b
        (hflagWorkSubset b hbFlagWork) hEq
    simpa only [equalFlagWires, List.append_assoc] using hcombined

  have hyEqualNodup :
      (equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart)).Nodup := by
    have hwork := pointAddYEqualWork_nodup workStart
    have hcombined :
        (PointRegister.y pointReg ++
          ((pointAddConst workStart ++
              pointAddYDifference workStart) ++
            pointAddYNegFlag workStart ::
              pointAddYHistory workStart)).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hyNodup, hwork, ?_⟩
      intro a ha b hb hEq
      have hbFlagWork : b ∈ pointAddFlagWork workStart := by
        simp only [List.mem_append, List.mem_cons] at hb
        rcases hb with (hconst | hdiff) | hflag | hhistory
        · simp [pointAddFlagWork, hconst]
        · simp [pointAddFlagWork, hdiff]
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork a
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)) b
        (hflagWorkSubset b hbFlagWork) hEq
    simpa only [equalFlagWires, List.append_assoc] using hcombined

  have hzeroClean :
      Clean
        (pointAddInfinityFlag workStart ::
          pointAddZeroHistory workStart) st := by
    intro w hw
    apply hcleanFlags w
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp [pointAddFlagWork]
    · simp [pointAddFlagWork, hw]

  let afterInfinity :=
    Classical.run
      (zeroFlag
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart))
      st

  have hzeroCorrect :
      AgreesOn (PointRegister.tag pointReg) st afterInfinity ∧
        afterInfinity (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) st = 0) ∧
        Clean (pointAddZeroHistory workStart) afterInfinity := by
    simpa [afterInfinity] using
      (zeroFlag_correct
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart)
        st
        (by
          simp [pointAddZeroHistory,
            PointRegister.tag_length pointReg hpointLength])
        hzeroNodup hzeroClean)

  have hzeroOtherOfFlag
      (w : Wire)
      (hwFlag : w ∈ pointAddFlagWork workStart)
      (hwInfinity : w ≠ pointAddInfinityFlag workStart)
      (hwHistory : w ∉ pointAddZeroHistory workStart) :
      afterInfinity w = st w := by
    apply
      (zeroFlag_usesOnly
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart)).preservesOutside
    simp only [zeroFlagWires, List.mem_append,
      List.mem_cons, not_or]
    refine ⟨?_, hwInfinity, hwHistory⟩
    intro htag
    exact hpointWork w (List.mem_of_mem_take htag) w
      (hflagWorkSubset w hwFlag) rfl

  have hconstCleanAfterInfinity :
      Clean (pointAddConst workStart) afterInfinity := by
    intro w hw
    have hwFlag : w ∈ pointAddFlagWork workStart := by
      simp [pointAddFlagWork, hw]
    rw [hzeroOtherOfFlag w hwFlag]
    · exact hcleanFlags w hwFlag
    · intro h
      subst w
      simp [pointAddConst, List.mem_range'_1,
        pointAddInfinityFlag, flagOffset,
        yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth] at hw ;
        omega
    · intro h
      simp [pointAddZeroHistory] at h
      subst w
      simp [pointAddConst, List.mem_range'_1,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth] at hw

  have hxScratchCleanAfterInfinity :
      Clean
        (pointAddXEqFlag workStart ::
          pointAddXDifference workStart ++
          pointAddXHistory workStart)
        afterInfinity := by
    intro w hw
    have hwFlag : w ∈ pointAddFlagWork workStart := by
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with hprefix | hhistory
      · rcases hprefix with hflag | hdiff
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hdiff]
      · simp [pointAddFlagWork, hhistory]
    rw [hzeroOtherOfFlag w hwFlag]
    · exact hcleanFlags w hwFlag
    · intro h
      subst w
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with hprefix | hhistory
      · rcases hprefix with hflag | hdiff
        · simp [pointAddXEqFlag, pointAddInfinityFlag] at hflag
        · simp [pointAddXDifference, List.mem_range'_1,
            pointAddInfinityFlag, flagOffset,
            yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset,
            zeroHistoryOffset, constOffset, fieldAreaSize,
            fieldWidth, Secp256k1Instance.fieldWidth] at hdiff ;
            omega
      · simp [pointAddXHistory, List.mem_range'_1,
          pointAddInfinityFlag, flagOffset,
          yHistoryOffset, yDifferenceOffset,
          xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] at hhistory ;
          omega
    · intro h
      simp [pointAddZeroHistory] at h
      subst w
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with hprefix | hhistory
      · rcases hprefix with hflag | hdiff
        · simp [pointAddXEqFlag, zeroHistoryOffset,
            flagOffset, yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset, constOffset,
            fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth] at hflag
        · simp [pointAddXDifference, List.mem_range'_1,
            xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth] at hdiff
      · simp [pointAddXHistory, List.mem_range'_1,
          xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] at hhistory

  have hconstLength :
      (pointAddConst workStart).length = 256 := by
    simp [pointAddConst]
  have hconstNodup :
      (pointAddConst workStart).Nodup := by
    rw [pointAddConst]
    exact List.nodup_range'

  let afterLoadX :=
    Classical.run
      (loadConst (pointAddConst workStart) xC.val)
      afterInfinity

  have hconstValueAfterLoadX :
      regValue (pointAddConst workStart) afterLoadX = xC.val := by
    apply loadConst_correct
    · exact hconstNodup
    · exact hconstCleanAfterInfinity
    · rw [hconstLength]
      exact xC.val_lt.trans (by norm_num [p])

  have hxScratchCleanAfterLoadX :
      Clean
        (pointAddXEqFlag workStart ::
          pointAddXDifference workStart ++
          pointAddXHistory workStart)
        afterLoadX := by
    intro w hw
    change
      Classical.run
          (loadConst (pointAddConst workStart) xC.val)
          afterInfinity w = false
    rw [loadConst_other w (pointAddConst workStart)
      xC.val afterInfinity]
    · exact hxScratchCleanAfterInfinity w hw
    · intro hconst
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with hprefix | hhistory
      · rcases hprefix with hflag | hdiff
        · subst w
          simp [pointAddConst, List.mem_range'_1,
            pointAddXEqFlag, flagOffset,
            yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset,
            zeroHistoryOffset, constOffset, fieldAreaSize,
            fieldWidth, Secp256k1Instance.fieldWidth] at hconst
        · have hconstBounds := List.mem_range'_1.mp hconst
          have hdiffBounds := List.mem_range'_1.mp hdiff
          norm_num [xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth] at hconstBounds hdiffBounds
          omega
      · have hconstBounds := List.mem_range'_1.mp hconst
        have hhistoryBounds := List.mem_range'_1.mp hhistory
        norm_num [xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth]
          at hconstBounds hhistoryBounds
        omega

  let afterXEq :=
    Classical.run
      (equalFlag
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart))
      afterLoadX

  have hxEqualCorrect :
      AgreesOn (PointRegister.x pointReg)
          afterLoadX afterXEq ∧
        AgreesOn (pointAddConst workStart)
          afterLoadX afterXEq ∧
        afterXEq (pointAddXEqFlag workStart) =
          decide (
            regValue (PointRegister.x pointReg) afterLoadX =
              regValue (pointAddConst workStart) afterLoadX) ∧
        Clean
          (pointAddXDifference workStart ++
            pointAddXHistory workStart)
          afterXEq := by
    simpa [afterXEq] using
      (equalFlag_correct
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart)
        afterLoadX
        (by
          simp [pointAddConst,
            PointRegister.x_length pointReg hpointLength])
        (by
          simp [pointAddXDifference,
            PointRegister.x_length pointReg hpointLength])
        (by
          simp [pointAddXHistory,
            PointRegister.x_length pointReg hpointLength])
        hxEqualNodup hxScratchCleanAfterLoadX)

  let afterUnloadX :=
    Classical.run
      (loadConst (pointAddConst workStart) xC.val)
      afterXEq

  have hconstCleanAfterUnloadX :
      Clean (pointAddConst workStart) afterUnloadX := by
    intro w hw
    have hcongr :=
      CircuitUsesOnly.run_congr
        (loadConst_usesOnly (pointAddConst workStart) xC.val)
        (st₁ := afterXEq)
        (st₂ := afterLoadX)
        (fun a ha => hxEqualCorrect.2.1 a ha)
        w hw
    change
      Classical.run
          (loadConst (pointAddConst workStart) xC.val)
          afterXEq w = false
    rw [hcongr]
    have htwice :=
      congrFun
        (run_loadConst_twice
          (pointAddConst workStart) xC.val
          afterInfinity hconstNodup) w
    change
      Classical.run
          (loadConst (pointAddConst workStart) xC.val)
          afterLoadX w = false
    rw [htwice]
    exact hconstCleanAfterInfinity w hw

  have hyScratchLocation
      (w : Wire)
      (hw :
        w ∈ pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart) :
      w = workStart + 3082 ∨
        (workStart + 2568 ≤ w ∧
          w < workStart + 2568 + 256) ∨
        (workStart + 2824 ≤ w ∧
          w < workStart + 2824 + 256) := by
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with hprefix | hhistory
    · rcases hprefix with hflag | hdiff
      · left
        simpa [pointAddYNegFlag, flagOffset,
          yHistoryOffset, yDifferenceOffset,
          xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] using hflag
      · right
        left
        simpa [pointAddYDifference, List.mem_range'_1,
          yDifferenceOffset, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] using
          List.mem_range'_1.mp hdiff
    · right
      right
      simpa [pointAddYHistory, List.mem_range'_1,
        yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth] using
        List.mem_range'_1.mp hhistory

  have hyScratchFlagWork
      (w : Wire)
      (hw :
        w ∈ pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart) :
      w ∈ pointAddFlagWork workStart := by
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with hprefix | hhistory
    · rcases hprefix with hflag | hdiff
      · simp [pointAddFlagWork, hflag]
      · simp [pointAddFlagWork, hdiff]
    · simp [pointAddFlagWork, hhistory]

  have hyScratchNotConst
      (w : Wire)
      (hw :
        w ∈ pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart) :
      w ∉ pointAddConst workStart := by
    intro hconst
    have hconstBounds := List.mem_range'_1.mp hconst
    have hloc := hyScratchLocation w hw
    norm_num [pointAddConst, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth] at hconstBounds
    have hconstUpper : w < workStart + 2055 := by
      simpa [Nat.add_assoc] using hconstBounds.2
    rcases hloc with hflagLoc | hrest
    · exact offset_lt_le_false workStart w 2055 3082
        hconstUpper hflagLoc.ge (by omega)
    · rcases hrest with hdiffLoc | hhistoryLoc
      · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
        exact offset_lt_le_false workStart w 2055 2568
          hconstUpper hdiffLower (by omega)
      · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
        exact offset_lt_le_false workStart w 2055 2824
          hconstUpper hhistoryLower (by omega)

  have hyScratchOutsideXEqual
      (w : Wire)
      (hw :
        w ∈ pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart) :
      w ∉ equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hx | hconst
        · exact hpointWork w
            (List.mem_of_mem_drop (List.mem_of_mem_take hx)) w
            (hflagWorkSubset w (hyScratchFlagWork w hw)) rfl
        · exact hyScratchNotConst w hw hconst
      · have hdiffBounds := List.mem_range'_1.mp hdiff
        have hloc := hyScratchLocation w hw
        norm_num [pointAddXDifference,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hdiffBounds
        have hxDiffUpper : w < workStart + 2312 := by
          simpa [Nat.add_assoc] using hdiffBounds.2
        rcases hloc with hflagLoc | hrest
        · exact offset_lt_le_false workStart w 2312 3082
            hxDiffUpper hflagLoc.ge (by omega)
        · rcases hrest with hdiffLoc | hhistoryLoc
          · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
            exact offset_lt_le_false workStart w 2312 2568
              hxDiffUpper hdiffLower (by omega)
          · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
            exact offset_lt_le_false workStart w 2312 2824
              hxDiffUpper hhistoryLower (by omega)
    · rcases htail with hflag | hhistory
      · have hxEq : w = workStart + 3081 := by
          simpa [pointAddXEqFlag, flagOffset,
            yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset,
            zeroHistoryOffset, constOffset, fieldAreaSize,
            fieldWidth, Secp256k1Instance.fieldWidth] using hflag
        have hloc := hyScratchLocation w hw
        rcases hloc with hflagLoc | hrest
        · exact
            (offset_ne workStart 3081 3082 (by omega))
              (hxEq.symm.trans hflagLoc)
        · rcases hrest with hdiffLoc | hhistoryLoc
          · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
            have hyDiffUpper : w < workStart + 2824 := by
              simpa [Nat.add_assoc] using hdiffUpper
            exact offset_lt_le_false workStart w 2824 3081
              hyDiffUpper hxEq.ge (by omega)
          · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
            have hyHistoryUpper : w < workStart + 3080 := by
              simpa [Nat.add_assoc] using hhistoryUpper
            exact offset_lt_le_false workStart w 3080 3081
              hyHistoryUpper hxEq.ge (by omega)
      · have hhistoryBounds := List.mem_range'_1.mp hhistory
        have hloc := hyScratchLocation w hw
        norm_num [pointAddXHistory, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hhistoryBounds
        have hxHistoryUpper : w < workStart + 2568 := by
          simpa [Nat.add_assoc] using hhistoryBounds.2
        rcases hloc with hflagLoc | hrest
        · exact offset_lt_le_false workStart w 2568 3082
            hxHistoryUpper hflagLoc.ge (by omega)
        · rcases hrest with hdiffLoc | hhistoryLoc
          · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
            exact offset_lt_le_false workStart w 2568 2568
              hxHistoryUpper hdiffLower (by omega)
          · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
            exact offset_lt_le_false workStart w 2568 2824
              hxHistoryUpper hhistoryLower (by omega)

  have hyScratchCleanAfterUnloadX :
      Clean
        (pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart)
        afterUnloadX := by
    intro w hw
    have hwFlag := hyScratchFlagWork w hw
    have hwConst := hyScratchNotConst w hw
    have hloc := hyScratchLocation w hw
    have hwInfinity :
        w ≠ pointAddInfinityFlag workStart := by
      intro h
      have hinfinity : w = workStart + 3080 := by
        simpa [pointAddInfinityFlag, flagOffset,
          yHistoryOffset, yDifferenceOffset,
          xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] using h
      rcases hloc with hflagLoc | hrest
      · exact
          (offset_ne workStart 3080 3082 (by omega))
            (hinfinity.symm.trans hflagLoc)
      · rcases hrest with hdiffLoc | hhistoryLoc
        · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
          have hyDiffUpper : w < workStart + 2824 := by
            simpa [Nat.add_assoc] using hdiffUpper
          exact offset_lt_le_false workStart w 2824 3080
            hyDiffUpper hinfinity.ge (by omega)
        · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
          have hyHistoryUpper : w < workStart + 3080 := by
            simpa [Nat.add_assoc] using hhistoryUpper
          exact offset_lt_le_false workStart w 3080 3080
            hyHistoryUpper hinfinity.ge (by omega)
    have hwZeroHistory :
        w ∉ pointAddZeroHistory workStart := by
      intro h
      have hzero : w = workStart + 2055 := by
        simpa [pointAddZeroHistory,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] using h
      rcases hloc with hflagLoc | hrest
      · exact
          (offset_ne workStart 2055 3082 (by omega))
            (hzero.symm.trans hflagLoc)
      · rcases hrest with hdiffLoc | hhistoryLoc
        · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
          have hzeroUpper : w < workStart + 2568 := by
            rw [hzero]
            exact Nat.add_lt_add_left (by omega) workStart
          exact offset_lt_le_false workStart w 2568 2568
            hzeroUpper hdiffLower (by omega)
        · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
          have hzeroUpper : w < workStart + 2824 := by
            rw [hzero]
            exact Nat.add_lt_add_left (by omega) workStart
          exact offset_lt_le_false workStart w 2824 2824
            hzeroUpper hhistoryLower (by omega)
    change afterUnloadX w = false
    calc
      afterUnloadX w = afterXEq w := by
        exact loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w := by
        exact
          (equalFlag_usesOnly
            (PointRegister.x pointReg)
            (pointAddConst workStart)
            (pointAddXEqFlag workStart)
            (pointAddXDifference workStart)
            (pointAddXHistory workStart)).preservesOutside
              afterLoadX w (hyScratchOutsideXEqual w hw)
      _ = afterInfinity w := by
        exact loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w :=
        hzeroOtherOfFlag w hwFlag hwInfinity hwZeroHistory
      _ = false := hcleanFlags w hwFlag

  let afterLoadY :=
    Classical.run
      (loadConst (pointAddConst workStart) (-yC).val)
      afterUnloadX

  have hconstValueAfterLoadY :
      regValue (pointAddConst workStart) afterLoadY =
        (-yC).val := by
    apply loadConst_correct
    · exact hconstNodup
    · exact hconstCleanAfterUnloadX
    · rw [hconstLength]
      exact (-yC).val_lt.trans (by norm_num [p])

  have hyScratchCleanAfterLoadY :
      Clean
        (pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart)
        afterLoadY := by
    intro w hw
    change
      Classical.run
          (loadConst (pointAddConst workStart) (-yC).val)
          afterUnloadX w = false
    rw [loadConst_other w (pointAddConst workStart)
      (-yC).val afterUnloadX (hyScratchNotConst w hw)]
    exact hyScratchCleanAfterUnloadX w hw

  let afterYNeg :=
    Classical.run
      (equalFlag
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart))
      afterLoadY

  have hyEqualCorrect :
      AgreesOn (PointRegister.y pointReg)
          afterLoadY afterYNeg ∧
        AgreesOn (pointAddConst workStart)
          afterLoadY afterYNeg ∧
        afterYNeg (pointAddYNegFlag workStart) =
          decide (
            regValue (PointRegister.y pointReg) afterLoadY =
              regValue (pointAddConst workStart) afterLoadY) ∧
        Clean
          (pointAddYDifference workStart ++
            pointAddYHistory workStart)
          afterYNeg := by
    simpa [afterYNeg] using
      (equalFlag_correct
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart)
        afterLoadY
        (by
          simp [pointAddConst,
            PointRegister.y_length pointReg hpointLength])
        (by
          simp [pointAddYDifference,
            PointRegister.y_length pointReg hpointLength])
        (by
          simp [pointAddYHistory,
            PointRegister.y_length pointReg hpointLength])
        hyEqualNodup hyScratchCleanAfterLoadY)

  let beforeGates :=
    Classical.run
      (loadConst (pointAddConst workStart) (-yC).val)
      afterYNeg

  have hconstCleanBeforeGates :
      Clean (pointAddConst workStart) beforeGates := by
    intro w hw
    have hcongr :=
      CircuitUsesOnly.run_congr
        (loadConst_usesOnly
          (pointAddConst workStart) (-yC).val)
        (st₁ := afterYNeg)
        (st₂ := afterLoadY)
        (fun a ha => hyEqualCorrect.2.1 a ha)
        w hw
    change
      Classical.run
          (loadConst (pointAddConst workStart) (-yC).val)
          afterYNeg w = false
    rw [hcongr]
    have htwice :=
      congrFun
        (run_loadConst_twice
          (pointAddConst workStart) (-yC).val
          afterUnloadX hconstNodup) w
    change
      Classical.run
          (loadConst (pointAddConst workStart) (-yC).val)
          afterLoadY w = false
    rw [htwice]
    exact hconstCleanAfterUnloadX w hw

  have hslicesNodup :=
    PointRegister.tag_x_y_nodup
      pointReg hpointLength hpointNodup
  obtain ⟨htagXNodup, _hyNd, htagXY_Y⟩ :=
    List.nodup_append.mp hslicesNodup
  obtain ⟨_htagNd, _hxNd, htagX⟩ :=
    List.nodup_append.mp htagXNodup

  have hpublicNotConst
      (w : Wire) (hw : w ∈ pointReg) :
      w ∉ pointAddConst workStart := by
    intro hconst
    have hconstFlag :
        w ∈ pointAddFlagWork workStart := by
      simp [pointAddFlagWork, hconst]
    exact hpointWork w hw w
      (hflagWorkSubset w hconstFlag) rfl

  have htagOutsideXEqual
      (w : Wire) (hw : w ∈ PointRegister.tag pointReg) :
      w ∉ equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hx | hconst
        · exact htagX w hw w hx rfl
        · exact hpublicNotConst w
            (List.mem_of_mem_take hw) hconst
      · have hdiffFlag :
            w ∈ pointAddFlagWork workStart := by
          simp [pointAddFlagWork, hdiff]
        exact hpointWork w (List.mem_of_mem_take hw) w
          (hflagWorkSubset w hdiffFlag) rfl
    · have htailFlag :
          w ∈ pointAddFlagWork workStart := by
        rcases htail with hflag | hhistory
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork w (List.mem_of_mem_take hw) w
        (hflagWorkSubset w htailFlag) rfl

  have htagOutsideYEqual
      (w : Wire) (hw : w ∈ PointRegister.tag pointReg) :
      w ∉ equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hy | hconst
        · exact htagXY_Y w
            (List.mem_append_left _ hw) w hy rfl
        · exact hpublicNotConst w
            (List.mem_of_mem_take hw) hconst
      · have hdiffFlag :
            w ∈ pointAddFlagWork workStart := by
          simp [pointAddFlagWork, hdiff]
        exact hpointWork w (List.mem_of_mem_take hw) w
          (hflagWorkSubset w hdiffFlag) rfl
    · have htailFlag :
          w ∈ pointAddFlagWork workStart := by
        rcases htail with hflag | hhistory
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork w (List.mem_of_mem_take hw) w
        (hflagWorkSubset w htailFlag) rfl

  have hxOutsideZero
      (w : Wire) (hw : w ∈ PointRegister.x pointReg) :
      w ∉ zeroFlagWires
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart) := by
    intro hin
    simp only [zeroFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with htag | hflag | hhistory
    · exact htagX w htag w hw rfl
    · have hflagWork :
          w ∈ pointAddFlagWork workStart := by
        simp [pointAddFlagWork, hflag]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w hflagWork) rfl
    · have hhistoryWork :
          w ∈ pointAddFlagWork workStart := by
        simp [pointAddFlagWork, hhistory]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w hhistoryWork) rfl

  have hyOutsideZero
      (w : Wire) (hw : w ∈ PointRegister.y pointReg) :
      w ∉ zeroFlagWires
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart) := by
    intro hin
    simp only [zeroFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with htag | hflag | hhistory
    · exact htagXY_Y w
        (List.mem_append_left _ htag) w hw rfl
    · have hflagWork :
          w ∈ pointAddFlagWork workStart := by
        simp [pointAddFlagWork, hflag]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w hflagWork) rfl
    · have hhistoryWork :
          w ∈ pointAddFlagWork workStart := by
        simp [pointAddFlagWork, hhistory]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w hhistoryWork) rfl

  have hxOutsideYEqual
      (w : Wire) (hw : w ∈ PointRegister.x pointReg) :
      w ∉ equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hy | hconst
        · exact htagXY_Y w
            (List.mem_append_right _ hw) w hy rfl
        · exact hpublicNotConst w
            (List.mem_of_mem_drop (List.mem_of_mem_take hw))
            hconst
      · have hdiffFlag :
            w ∈ pointAddFlagWork workStart := by
          simp [pointAddFlagWork, hdiff]
        exact hpointWork w
          (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
          (hflagWorkSubset w hdiffFlag) rfl
    · have htailFlag :
          w ∈ pointAddFlagWork workStart := by
        rcases htail with hflag | hhistory
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w htailFlag) rfl

  have hyOutsideXEqual
      (w : Wire) (hw : w ∈ PointRegister.y pointReg) :
      w ∉ equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hx | hconst
        · exact htagXY_Y w
            (List.mem_append_right _ hx) w hw rfl
        · exact hpublicNotConst w
            (List.mem_of_mem_drop (List.mem_of_mem_take hw))
            hconst
      · have hdiffFlag :
            w ∈ pointAddFlagWork workStart := by
          simp [pointAddFlagWork, hdiff]
        exact hpointWork w
          (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
          (hflagWorkSubset w hdiffFlag) rfl
    · have htailFlag :
          w ∈ pointAddFlagWork workStart := by
        rcases htail with hflag | hhistory
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w htailFlag) rfl

  have htagBeforeGates :
      AgreesOn (PointRegister.tag pointReg) st beforeGates := by
    intro w hw
    have hwPoint := List.mem_of_mem_take hw
    have hwConst := hpublicNotConst w hwPoint
    calc
      beforeGates w = afterYNeg w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterYNeg hwConst
      _ = afterLoadY w :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY w (htagOutsideYEqual w hw)
      _ = afterUnloadX w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterUnloadX hwConst
      _ = afterXEq w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w :=
        (equalFlag_usesOnly
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)).preservesOutside
            afterLoadX w (htagOutsideXEqual w hw)
      _ = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w := hzeroCorrect.1 w hw

  have hxBeforeGates :
      AgreesOn (PointRegister.x pointReg) st beforeGates := by
    intro w hw
    have hwPoint :=
      List.mem_of_mem_drop (List.mem_of_mem_take hw)
    have hwConst := hpublicNotConst w hwPoint
    calc
      beforeGates w = afterYNeg w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterYNeg hwConst
      _ = afterLoadY w :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY w (hxOutsideYEqual w hw)
      _ = afterUnloadX w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterUnloadX hwConst
      _ = afterXEq w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w := hxEqualCorrect.1 w hw
      _ = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w :=
        (zeroFlag_usesOnly
          (PointRegister.tag pointReg)
          (pointAddInfinityFlag workStart)
          (pointAddZeroHistory workStart)).preservesOutside
            st w (hxOutsideZero w hw)

  have hyBeforeGates :
      AgreesOn (PointRegister.y pointReg) st beforeGates := by
    intro w hw
    have hwPoint :=
      List.mem_of_mem_drop (List.mem_of_mem_take hw)
    have hwConst := hpublicNotConst w hwPoint
    calc
      beforeGates w = afterYNeg w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterYNeg hwConst
      _ = afterLoadY w := hyEqualCorrect.1 w hw
      _ = afterUnloadX w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterUnloadX hwConst
      _ = afterXEq w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w :=
        (equalFlag_usesOnly
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)).preservesOutside
            afterLoadX w (hyOutsideXEqual w hw)
      _ = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w :=
        (zeroFlag_usesOnly
          (PointRegister.tag pointReg)
          (pointAddInfinityFlag workStart)
          (pointAddZeroHistory workStart)).preservesOutside
            st w (hyOutsideZero w hw)

  have hhighFlagNotConst
      (w : Wire)
      (hlower : workStart + 3080 ≤ w) :
      w ∉ pointAddConst workStart := by
    intro hconst
    have hbounds := List.mem_range'_1.mp hconst
    norm_num [pointAddConst, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth] at hbounds
    have hupper : w < workStart + 2055 := by
      simpa [Nat.add_assoc] using hbounds.2
    exact offset_lt_le_false workStart w 2055 3080
      hupper hlower (by omega)

  have hhighFlagOutsideXEqual
      (w : Wire)
      (hwFlag : w ∈ pointAddFlagWork workStart)
      (hlower : workStart + 3080 ≤ w)
      (hnotXEq : w ≠ pointAddXEqFlag workStart) :
      w ∉ equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hx | hconst
        · exact hpointWork w
            (List.mem_of_mem_drop (List.mem_of_mem_take hx)) w
            (hflagWorkSubset w hwFlag) rfl
        · exact hhighFlagNotConst w hlower hconst
      · have hbounds := List.mem_range'_1.mp hdiff
        norm_num [pointAddXDifference,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hbounds
        have hupper : w < workStart + 2312 := by
          simpa [Nat.add_assoc] using hbounds.2
        exact offset_lt_le_false workStart w 2312 3080
          hupper hlower (by omega)
    · rcases htail with hflag | hhistory
      · exact hnotXEq hflag
      · have hbounds := List.mem_range'_1.mp hhistory
        norm_num [pointAddXHistory, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hbounds
        have hupper : w < workStart + 2568 := by
          simpa [Nat.add_assoc] using hbounds.2
        exact offset_lt_le_false workStart w 2568 3080
          hupper hlower (by omega)

  have hhighFlagOutsideYEqual
      (w : Wire)
      (hwFlag : w ∈ pointAddFlagWork workStart)
      (hlower : workStart + 3080 ≤ w)
      (hnotYNeg : w ≠ pointAddYNegFlag workStart) :
      w ∉ equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hy | hconst
        · exact hpointWork w
            (List.mem_of_mem_drop (List.mem_of_mem_take hy)) w
            (hflagWorkSubset w hwFlag) rfl
        · exact hhighFlagNotConst w hlower hconst
      · have hbounds := List.mem_range'_1.mp hdiff
        norm_num [pointAddYDifference,
          yDifferenceOffset, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hbounds
        have hupper : w < workStart + 2824 := by
          simpa [Nat.add_assoc] using hbounds.2
        exact offset_lt_le_false workStart w 2824 3080
          hupper hlower (by omega)
    · rcases htail with hflag | hhistory
      · exact hnotYNeg hflag
      · have hbounds := List.mem_range'_1.mp hhistory
        norm_num [pointAddYHistory, yHistoryOffset,
          yDifferenceOffset, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hbounds
        have hupper : w < workStart + 3080 := by
          simpa [Nat.add_assoc] using hbounds.2
        exact offset_lt_le_false workStart w 3080 3080
          hupper hlower (by omega)

  have hprefixOtherHighFlag
      (w : Wire)
      (hwFlag : w ∈ pointAddFlagWork workStart)
      (hlower : workStart + 3080 ≤ w)
      (hwInfinity : w ≠ pointAddInfinityFlag workStart)
      (hwXEq : w ≠ pointAddXEqFlag workStart)
      (hwYNeg : w ≠ pointAddYNegFlag workStart) :
      beforeGates w = st w := by
    have hwConst := hhighFlagNotConst w hlower
    have hwZeroHistory :
        w ∉ pointAddZeroHistory workStart := by
      intro hzero
      have hzeroEq : w = workStart + 2055 := by
        simpa [pointAddZeroHistory, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] using hzero
      have hupper : w < workStart + 3080 := by
        rw [hzeroEq]
        exact Nat.add_lt_add_left (by omega) workStart
      exact offset_lt_le_false workStart w 3080 3080
        hupper hlower (by omega)
    calc
      beforeGates w = afterYNeg w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterYNeg hwConst
      _ = afterLoadY w :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY w
              (hhighFlagOutsideYEqual w hwFlag hlower hwYNeg)
      _ = afterUnloadX w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterUnloadX hwConst
      _ = afterXEq w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w :=
        (equalFlag_usesOnly
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)).preservesOutside
            afterLoadX w
              (hhighFlagOutsideXEqual w hwFlag hlower hwXEq)
      _ = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w :=
        hzeroOtherOfFlag w hwFlag hwInfinity hwZeroHistory

  have hinfinityFlagMem :
      pointAddInfinityFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hinfinityFlagLower :
      workStart + 3080 ≤
        pointAddInfinityFlag workStart := by
    simp [pointAddInfinityFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hxEqFlagMem :
      pointAddXEqFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hxEqFlagLower :
      workStart + 3080 ≤ pointAddXEqFlag workStart := by
    simp [pointAddXEqFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hyNegFlagMem :
      pointAddYNegFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hyNegFlagLower :
      workStart + 3080 ≤ pointAddYNegFlag workStart := by
    simp [pointAddYNegFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hinfinityNeXEq :
      pointAddInfinityFlag workStart ≠
        pointAddXEqFlag workStart := by
    simp [pointAddInfinityFlag, pointAddXEqFlag]

  have hinfinityNeYNeg :
      pointAddInfinityFlag workStart ≠
        pointAddYNegFlag workStart := by
    simp [pointAddInfinityFlag, pointAddYNegFlag]

  have hxEqNeYNeg :
      pointAddXEqFlag workStart ≠
        pointAddYNegFlag workStart := by
    simp [pointAddXEqFlag, pointAddYNegFlag]

  have hinfinityBeforeGates :
      beforeGates (pointAddInfinityFlag workStart) =
        decide (regValue (PointRegister.tag pointReg) st = 0) := by
    have hnotConst :=
      hhighFlagNotConst
        (pointAddInfinityFlag workStart)
        hinfinityFlagLower
    calc
      beforeGates (pointAddInfinityFlag workStart) =
          afterYNeg (pointAddInfinityFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterYNeg hnotConst
      _ = afterLoadY (pointAddInfinityFlag workStart) :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY _
              (hhighFlagOutsideYEqual _ hinfinityFlagMem
                hinfinityFlagLower hinfinityNeYNeg)
      _ = afterUnloadX (pointAddInfinityFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterUnloadX hnotConst
      _ = afterXEq (pointAddInfinityFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          xC.val afterXEq hnotConst
      _ = afterLoadX (pointAddInfinityFlag workStart) :=
        (equalFlag_usesOnly
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)).preservesOutside
            afterLoadX _
              (hhighFlagOutsideXEqual _ hinfinityFlagMem
                hinfinityFlagLower hinfinityNeXEq)
      _ = afterInfinity (pointAddInfinityFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          xC.val afterInfinity hnotConst
      _ = decide
          (regValue (PointRegister.tag pointReg) st = 0) :=
        hzeroCorrect.2.1

  have hxAfterLoadX :
      regValue (PointRegister.x pointReg) afterLoadX =
        regValue (PointRegister.x pointReg) st := by
    apply Arithmetic.AgreesOn.regValue
    intro w hw
    have hwPoint :=
      List.mem_of_mem_drop (List.mem_of_mem_take hw)
    calc
      afterLoadX w = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity (hpublicNotConst w hwPoint)
      _ = st w :=
        (zeroFlag_usesOnly
          (PointRegister.tag pointReg)
          (pointAddInfinityFlag workStart)
          (pointAddZeroHistory workStart)).preservesOutside
            st w (hxOutsideZero w hw)

  have hxEqBeforeGates :
      beforeGates (pointAddXEqFlag workStart) =
        decide
          (regValue (PointRegister.x pointReg) st = xC.val) := by
    have hnotConst :=
      hhighFlagNotConst
        (pointAddXEqFlag workStart) hxEqFlagLower
    calc
      beforeGates (pointAddXEqFlag workStart) =
          afterYNeg (pointAddXEqFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterYNeg hnotConst
      _ = afterLoadY (pointAddXEqFlag workStart) :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY _
              (hhighFlagOutsideYEqual _ hxEqFlagMem
                hxEqFlagLower hxEqNeYNeg)
      _ = afterUnloadX (pointAddXEqFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterUnloadX hnotConst
      _ = afterXEq (pointAddXEqFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          xC.val afterXEq hnotConst
      _ = decide
          (regValue (PointRegister.x pointReg) afterLoadX =
            regValue (pointAddConst workStart) afterLoadX) :=
        hxEqualCorrect.2.2.1
      _ = decide
          (regValue (PointRegister.x pointReg) st = xC.val) := by
        rw [hxAfterLoadX, hconstValueAfterLoadX]

  have hyAfterLoadY :
      regValue (PointRegister.y pointReg) afterLoadY =
        regValue (PointRegister.y pointReg) st := by
    have hbeforeUnloadY :
        AgreesOn (PointRegister.y pointReg)
          afterYNeg beforeGates := by
      intro w hw
      exact loadConst_other w (pointAddConst workStart)
        (-yC).val afterYNeg
        (hpublicNotConst w
          (List.mem_of_mem_drop (List.mem_of_mem_take hw)))
    calc
      regValue (PointRegister.y pointReg) afterLoadY =
          regValue (PointRegister.y pointReg) afterYNeg :=
        (Arithmetic.AgreesOn.regValue hyEqualCorrect.1).symm
      _ = regValue (PointRegister.y pointReg) beforeGates :=
        (Arithmetic.AgreesOn.regValue hbeforeUnloadY).symm
      _ = regValue (PointRegister.y pointReg) st :=
        Arithmetic.AgreesOn.regValue hyBeforeGates

  have hyNegBeforeGates :
      beforeGates (pointAddYNegFlag workStart) =
        decide
          (regValue (PointRegister.y pointReg) st = (-yC).val) := by
    have hnotConst :=
      hhighFlagNotConst
        (pointAddYNegFlag workStart) hyNegFlagLower
    calc
      beforeGates (pointAddYNegFlag workStart) =
          afterYNeg (pointAddYNegFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterYNeg hnotConst
      _ = decide
          (regValue (PointRegister.y pointReg) afterLoadY =
            regValue (pointAddConst workStart) afterLoadY) :=
        hyEqualCorrect.2.2.1
      _ = decide
          (regValue (PointRegister.y pointReg) st = (-yC).val) := by
        rw [hyAfterLoadY, hconstValueAfterLoadY]

  have hgenericFlagMem :
      pointAddGenericFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hgenericFlagLower :
      workStart + 3080 ≤
        pointAddGenericFlag workStart := by
    simp [pointAddGenericFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hgenericBeforeGates :
      beforeGates (pointAddGenericFlag workStart) = false := by
    rw [hprefixOtherHighFlag
      (pointAddGenericFlag workStart)
      hgenericFlagMem hgenericFlagLower]
    · exact hcleanFlags _ hgenericFlagMem
    · simp [pointAddGenericFlag, pointAddInfinityFlag]
    · simp [pointAddGenericFlag, pointAddXEqFlag]
    · simp [pointAddGenericFlag, pointAddYNegFlag]

  have hpairFlagMem :
      pointAddPairFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hpairFlagLower :
      workStart + 3080 ≤ pointAddPairFlag workStart := by
    simp [pointAddPairFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hpairBeforeGates :
      beforeGates (pointAddPairFlag workStart) = false := by
    rw [hprefixOtherHighFlag
      (pointAddPairFlag workStart)
      hpairFlagMem hpairFlagLower]
    · exact hcleanFlags _ hpairFlagMem
    · simp [pointAddPairFlag, pointAddInfinityFlag]
    · simp [pointAddPairFlag, pointAddXEqFlag]
    · simp [pointAddPairFlag, pointAddYNegFlag]

  have hdoubleFlagMem :
      pointAddDoubleFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hdoubleFlagLower :
      workStart + 3080 ≤
        pointAddDoubleFlag workStart := by
    simp [pointAddDoubleFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hdoubleBeforeGates :
      beforeGates (pointAddDoubleFlag workStart) = false := by
    rw [hprefixOtherHighFlag
      (pointAddDoubleFlag workStart)
      hdoubleFlagMem hdoubleFlagLower]
    · exact hcleanFlags _ hdoubleFlagMem
    · simp [pointAddDoubleFlag, pointAddInfinityFlag]
    · simp [pointAddDoubleFlag, pointAddXEqFlag]
    · simp [pointAddDoubleFlag, pointAddYNegFlag]

  let manualGates : Circuit :=
    [Gate.X (pointAddInfinityFlag workStart),
      Gate.X (pointAddXEqFlag workStart),
      Gate.CCX
        (pointAddInfinityFlag workStart)
        (pointAddXEqFlag workStart)
        (pointAddGenericFlag workStart),
      Gate.X (pointAddXEqFlag workStart),
      Gate.X (pointAddInfinityFlag workStart),
      Gate.X (pointAddYNegFlag workStart),
      Gate.CCX
        (pointAddXEqFlag workStart)
        (pointAddYNegFlag workStart)
        (pointAddPairFlag workStart),
      Gate.X (pointAddYNegFlag workStart),
      Gate.X (pointAddInfinityFlag workStart),
      Gate.CCX
        (pointAddInfinityFlag workStart)
        (pointAddPairFlag workStart)
        (pointAddDoubleFlag workStart),
      Gate.X (pointAddInfinityFlag workStart)]

  let after := Classical.run manualGates beforeGates

  have hinfinityBeforeGates' :
      beforeGates (workStart + flagOffset) =
        decide (regValue (PointRegister.tag pointReg) st = 0) := by
    simpa only [pointAddInfinityFlag] using
      hinfinityBeforeGates
  have hxEqBeforeGates' :
      beforeGates (workStart + flagOffset + 1) =
        decide
          (regValue (PointRegister.x pointReg) st = xC.val) := by
    simpa only [pointAddXEqFlag] using hxEqBeforeGates
  have hyNegBeforeGates' :
      beforeGates (workStart + flagOffset + 2) =
        decide
          (regValue (PointRegister.y pointReg) st = (-yC).val) := by
    simpa only [pointAddYNegFlag] using hyNegBeforeGates
  have hgenericBeforeGates' :
      beforeGates (workStart + flagOffset + 3) = false := by
    simpa only [pointAddGenericFlag] using hgenericBeforeGates
  have hpairBeforeGates' :
      beforeGates (workStart + flagOffset + 4) = false := by
    simpa only [pointAddPairFlag] using hpairBeforeGates
  have hdoubleBeforeGates' :
      beforeGates (workStart + flagOffset + 5) = false := by
    simpa only [pointAddDoubleFlag] using hdoubleBeforeGates

  have hflagResults :
      after (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) st = 0) ∧
        after (pointAddGenericFlag workStart) =
          decide
            (regValue (PointRegister.tag pointReg) st ≠ 0 ∧
              regValue (PointRegister.x pointReg) st ≠ xC.val) ∧
        after (pointAddDoubleFlag workStart) =
          decide
            (regValue (PointRegister.tag pointReg) st ≠ 0 ∧
              regValue (PointRegister.x pointReg) st = xC.val ∧
              regValue (PointRegister.y pointReg) st ≠ (-yC).val) := by
    by_cases hinfinity :
        regValue (PointRegister.tag pointReg) st = 0 <;>
      by_cases hxEq :
        regValue (PointRegister.x pointReg) st = xC.val <;>
      by_cases hyNeg :
        regValue (PointRegister.y pointReg) st = (-yC).val <;>
      simp [after, manualGates, Classical.run,
        Classical.applyGate, upd,
        pointAddInfinityFlag, pointAddXEqFlag,
        pointAddYNegFlag, pointAddGenericFlag,
        pointAddPairFlag, pointAddDoubleFlag,
        hinfinityBeforeGates', hxEqBeforeGates',
        hyNegBeforeGates', hgenericBeforeGates',
        hpairBeforeGates', hdoubleBeforeGates',
        hinfinity, hxEq, hyNeg]

  have hrun :
      Classical.run
          (pointAddFlags pointReg workStart xC yC) st =
        after := by
    simp [pointAddFlags, after, manualGates,
      beforeGates, afterYNeg, afterLoadY,
      afterUnloadX, afterXEq, afterLoadX,
      afterInfinity, Classical.run_append]

  have hmanualUses :
      CircuitUsesOnly
        (pointAddFlagWork workStart) manualGates := by
    simp [manualGates, CircuitUsesOnly, Gate.UsesOnly,
      pointAddFlagWork]

  have hpointBeforeGates :
      AgreesOn pointReg st beforeGates := by
    intro w hw
    have hwSlices :
        w ∈
          PointRegister.tag pointReg ++
            PointRegister.x pointReg ++
            PointRegister.y pointReg := by
      rw [PointRegister.tag_x_y pointReg hpointLength]
      exact hw
    rcases List.mem_append.mp hwSlices with htagXMem | hy
    · rcases List.mem_append.mp htagXMem with htag | hx
      · exact htagBeforeGates w htag
      · exact hxBeforeGates w hx
    · exact hyBeforeGates w hy

  have hpointAfter : AgreesOn pointReg st after := by
    intro w hw
    calc
      after w = beforeGates w :=
        hmanualUses.preservesOutside beforeGates w (by
          intro hflag
          exact hpointWork w hw w
            (hflagWorkSubset w hflag) rfl)
      _ = st w := hpointBeforeGates w hw

  have rangeInFlagBounds
      (offset len : Nat) {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmin : 1799 ≤ offset)
      (hmax : offset + len ≤ 3086) :
      workStart + 1799 ≤ w ∧
        w < workStart + 3086 := by
    constructor
    · exact (Nat.add_le_add_left hmin workStart).trans hw.1
    · exact hw.2.trans_le (by
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left hmax workStart)

  have wireInFlagBounds
      (offset : Nat) {w : Wire}
      (hw : w = workStart + offset)
      (hmin : 1799 ≤ offset)
      (hmax : offset < 3086) :
      workStart + 1799 ≤ w ∧
        w < workStart + 3086 := by
    subst w
    exact ⟨Nat.add_le_add_left hmin workStart,
      Nat.add_lt_add_left hmax workStart⟩

  have hflagBounds :
      ∀ w ∈ pointAddFlagWork workStart,
        workStart + 1799 ≤ w ∧ w < workStart + 3086 := by
    intro w hw
    simp only [pointAddFlagWork, pointAddConst,
      pointAddZeroHistory, pointAddXDifference,
      pointAddXHistory, pointAddYDifference,
      pointAddYHistory, pointAddInfinityFlag,
      pointAddXEqFlag, pointAddYNegFlag,
      pointAddGenericFlag, pointAddPairFlag,
      pointAddDoubleFlag, List.mem_append,
      List.mem_cons, List.mem_range'_1] at hw
    norm_num [flagOffset, yHistoryOffset,
      yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset,
      constOffset, fieldAreaSize, fieldWidth,
      Secp256k1Instance.fieldWidth] at hw
    rcases hw with
        (((((h0 | h1) | h2) | h3) | h4) | h5) |
          (h6 | h7 | h8 | h9 | h10 | h11)
    · exact rangeInFlagBounds 1799 256 h0 (by omega) (by omega)
    · exact wireInFlagBounds 2055 h1 (by omega) (by omega)
    · exact rangeInFlagBounds 2056 256 h2 (by omega) (by omega)
    · exact rangeInFlagBounds 2312 256 h3 (by omega) (by omega)
    · exact rangeInFlagBounds 2568 256 h4 (by omega) (by omega)
    · exact rangeInFlagBounds 2824 256 h5 (by omega) (by omega)
    · exact wireInFlagBounds 3080 h6 (by omega) (by omega)
    · exact wireInFlagBounds 3081 h7 (by omega) (by omega)
    · exact wireInFlagBounds 3082 h8 (by omega) (by omega)
    · exact wireInFlagBounds 3083 h9 (by omega) (by omega)
    · exact wireInFlagBounds 3084 h10 (by omega) (by omega)
    · exact wireInFlagBounds 3085 h11 (by omega) (by omega)

  have hxWorkSubset :
      ∀ w ∈ pointAddX workStart,
        w ∈ pointAddWork workStart := by
    intro w hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    rw [hlocalSizeEq]
    norm_num [pointAddX, fieldWidth,
      Secp256k1Instance.fieldWidth] at hbounds
    omega

  have hyWorkSubset :
      ∀ w ∈ pointAddY workStart,
        w ∈ pointAddWork workStart := by
    intro w hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    rw [hlocalSizeEq]
    norm_num [pointAddY, fieldWidth,
      Secp256k1Instance.fieldWidth] at hbounds
    omega

  have hxOutsideFlagFootprint :
      ∀ w ∈ pointAddX workStart,
        w ∉ pointReg ++ pointAddFlagWork workStart := by
    intro w hw hin
    rcases List.mem_append.mp hin with hpoint | hflag
    · exact hpointWork w hpoint w (hxWorkSubset w hw) rfl
    · have hxBounds := List.mem_range'_1.mp hw
      have hflagLower := (hflagBounds w hflag).1
      norm_num [pointAddX, fieldWidth,
        Secp256k1Instance.fieldWidth] at hxBounds
      have hxUpper : w < workStart + 257 := by
        simpa [Nat.add_assoc] using hxBounds.2
      exact offset_lt_le_false workStart w 257 1799
        hxUpper hflagLower (by omega)

  have hyOutsideFlagFootprint :
      ∀ w ∈ pointAddY workStart,
        w ∉ pointReg ++ pointAddFlagWork workStart := by
    intro w hw hin
    rcases List.mem_append.mp hin with hpoint | hflag
    · exact hpointWork w hpoint w (hyWorkSubset w hw) rfl
    · have hyBounds := List.mem_range'_1.mp hw
      have hflagLower := (hflagBounds w hflag).1
      norm_num [pointAddY, fieldWidth,
        Secp256k1Instance.fieldWidth] at hyBounds
      have hyUpper : w < workStart + 514 := by
        simpa [Nat.add_assoc] using hyBounds.2
      exact offset_lt_le_false workStart w 514 1799
        hyUpper hflagLower (by omega)

  have hxAfter :
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) st := by
    rw [← hrun]
    apply Arithmetic.AgreesOn.regValue
    intro w hw
    exact
      (pointAddFlags_usesOnly pointReg workStart xC yC).preservesOutside
        st w (hxOutsideFlagFootprint w hw)

  have hyAfter :
      regValue (pointAddY workStart) after =
        regValue (pointAddY workStart) st := by
    rw [← hrun]
    apply Arithmetic.AgreesOn.regValue
    intro w hw
    exact
      (pointAddFlags_usesOnly pointReg workStart xC yC).preservesOutside
        st w (hyOutsideFlagFootprint w hw)

  have localRangeMem
      (offset len : Nat) {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmax : offset + len ≤ 4112) :
      w ∈ List.range' workStart localWorkSize := by
    apply List.mem_range'_1.mpr
    rw [hlocalSizeEq]
    constructor
    · exact (Nat.le_add_right workStart offset).trans hw.1
    · exact hw.2.trans_le (by
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left hmax workStart)

  have hbranchWorkSubset :
      ∀ w ∈ pointAddBranchWork workStart,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [pointAddBranchWork] at hw
    rcases List.mem_append.mp hw with hlocal | harithmetic
    · rw [pointAddWork]
      apply List.mem_append_left
      simp only [pointAddT0, pointAddT1,
        pointAddT2, pointAddT3, pointAddT4,
        pointAddCandidate, pointAddSelected,
        List.mem_append, List.mem_range'_1] at hlocal
      norm_num [selectedOffset, candidateOffset,
        flagOffset, yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth,
        pointWidth] at hlocal
      rcases hlocal with
          (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
      · exact localRangeMem 514 257 h0 (by omega)
      · exact localRangeMem 771 257 h1 (by omega)
      · exact localRangeMem 1028 257 h2 (by omega)
      · exact localRangeMem 1285 257 h3 (by omega)
      · exact localRangeMem 1542 257 h4 (by omega)
      · exact localRangeMem 3086 513 h5 (by omega)
      · exact localRangeMem 3599 513 h6 (by omega)
    · rw [pointAddWork]
      exact List.mem_append_right _ harithmetic

  have hbranchOutsideFlags :
      ∀ w ∈ pointAddBranchWork workStart,
        w ∉ pointAddFlagWork workStart := by
    intro w hw hflag
    have hflagRange := hflagBounds w hflag
    rw [pointAddBranchWork] at hw
    rcases List.mem_append.mp hw with hlocal | harithmetic
    · simp only [pointAddT0, pointAddT1,
        pointAddT2, pointAddT3, pointAddT4,
        pointAddCandidate, pointAddSelected,
        List.mem_append, List.mem_range'_1] at hlocal
      norm_num [selectedOffset, candidateOffset,
        flagOffset, yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth,
        pointWidth] at hlocal
      rcases hlocal with
          (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
      · exact offset_lt_le_false workStart w 771 1799
          (by simpa [Nat.add_assoc] using h0.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 1028 1799
          (by simpa [Nat.add_assoc] using h1.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 1285 1799
          (by simpa [Nat.add_assoc] using h2.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 1542 1799
          (by simpa [Nat.add_assoc] using h3.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 1799 1799
          (by simpa [Nat.add_assoc] using h4.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 3086 3086
          hflagRange.2 h5.1 (by omega)
      · exact offset_lt_le_false workStart w 3086 3599
          hflagRange.2 h6.1 (by omega)
    · have hengineLower :=
        pointAddArithmeticWork_lower workStart w harithmetic
      have harithmeticLower :
          workStart + 4112 ≤ w := by
        simpa [pointAddArithmeticOffset, hlocalSizeEq] using
          hengineLower
      exact offset_lt_le_false workStart
        w
        3086 4112 hflagRange.2 harithmeticLower (by omega)

  have hbranchOutsideFlagFootprint :
      ∀ w ∈ pointAddBranchWork workStart,
        w ∉ pointReg ++ pointAddFlagWork workStart := by
    intro w hw hin
    rcases List.mem_append.mp hin with hpoint | hflag
    · exact hpointWork w hpoint w
        (hbranchWorkSubset w hw) rfl
    · exact hbranchOutsideFlags w hw hflag

  have hbranchCleanAfter :
      Clean (pointAddBranchWork workStart) after := by
    intro w hw
    rw [← hrun]
    rw [(pointAddFlags_usesOnly
      pointReg workStart xC yC).preservesOutside
        st w (hbranchOutsideFlagFootprint w hw)]
    exact hcleanBranch w hw

  rw [hrun]
  exact
    ⟨hpointAfter, hxAfter, hyAfter,
      hflagResults.1, hflagResults.2.1,
      hflagResults.2.2, hbranchCleanAfter⟩

/--
If the input is O, setup detects exactly the infinity branch.

The branch workspace remains clean because setup only writes the coordinate
copies and flag/predicate workspace.
-/
theorem pointAddSetup_zero_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat (0 : Point))
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddSetup pointReg workStart xC yC)
        st
    after (pointAddInfinityFlag workStart) = true ∧
      after (pointAddGenericFlag workStart) = false ∧
      after (pointAddDoubleFlag workStart) = false ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp
  rw [pointAddSetup, Classical.run_append]

  let copied :=
    Classical.run
      (pointAddCoordinateCopies pointReg workStart)
      st

  have hcopy :
      AgreesOn pointReg st copied ∧
        regValue (pointAddX workStart) copied =
          regValue (PointRegister.x pointReg) st ∧
        regValue (pointAddY workStart) copied =
          regValue (PointRegister.y pointReg) st ∧
        Clean (pointAddFlagWork workStart) copied ∧
        Clean (pointAddBranchWork workStart) copied := by
    simpa [copied] using
      pointAddCoordinateCopies_correct
        pointReg outReg workStart st
        hpointLength hnodup hclean

  rcases hcopy with
    ⟨hpointAgree, _, _, hflagClean, hbranchClean⟩

  have hpointCopied :
      regValue pointReg copied = encodeNat (0 : Point) := by
    calc
      regValue pointReg copied = regValue pointReg st :=
        Arithmetic.AgreesOn.regValue hpointAgree
      _ = encodeNat (0 : Point) := hpoint

  have hslices :=
    PointRegister.slices_of_regValue_zero
      pointReg copied hpointLength hpointCopied

  rcases hslices with ⟨htag, _, _⟩

  let after :=
    Classical.run
      (pointAddFlags pointReg workStart xC yC)
      copied

  have hflags :
      AgreesOn pointReg copied after ∧
        regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied ∧
        regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied ∧
        after (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) copied = 0) ∧
        after (pointAddGenericFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied ≠ xC.val) ∧
        after (pointAddDoubleFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied = xC.val ∧
            regValue (PointRegister.y pointReg) copied ≠ (-yC).val) ∧
        Clean (pointAddBranchWork workStart) after := by
    simpa [after] using
      pointAddFlags_semantics
        pointReg outReg workStart copied
        hpointLength hnodup hflagClean hbranchClean

  rcases hflags with
    ⟨_, _, _, hinfinity, hgeneric, hdouble, hcleanAfter⟩

  change
    after (pointAddInfinityFlag workStart) = true ∧
      after (pointAddGenericFlag workStart) = false ∧
      after (pointAddDoubleFlag workStart) = false ∧
      Clean (pointAddBranchWork workStart) after

  refine ⟨?_, ?_, ?_, hcleanAfter⟩
  · simpa [htag] using hinfinity
  · simpa [htag] using hgeneric
  · simpa [htag] using hdouble

/--
For a finite input R=(xR,yR), setup:

* loads xR and yR into the padded field registers;
* establishes that R is not infinity;
* computes the generic and doubling conditions;
* leaves all branch scratch clean.

The two useful branch predicates are

    generic = (xR ≠ xC)

and

    double = (xR = xC ∧ yR ≠ -yC).
-/
theorem pointAddSetup_some_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat (.some hR))
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddSetup pointReg workStart xC yC)
        st
    regValue (pointAddX workStart) after = xR.val ∧
      regValue (pointAddY workStart) after = yR.val ∧
      after (pointAddInfinityFlag workStart) = false ∧
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) ∧
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) ∧
      Clean (pointAddBranchWork workStart) after := by
  letI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩

  dsimp
  rw [pointAddSetup, Classical.run_append]

  let copied :=
    Classical.run
      (pointAddCoordinateCopies pointReg workStart)
      st

  have hcopy :
      AgreesOn pointReg st copied ∧
        regValue (pointAddX workStart) copied =
          regValue (PointRegister.x pointReg) st ∧
        regValue (pointAddY workStart) copied =
          regValue (PointRegister.y pointReg) st ∧
        Clean (pointAddFlagWork workStart) copied ∧
        Clean (pointAddBranchWork workStart) copied := by
    simpa [copied] using
      pointAddCoordinateCopies_correct
        pointReg outReg workStart st
        hpointLength hnodup hclean

  rcases hcopy with
    ⟨hpointAgree, hxCopy, hyCopy, hflagClean, hbranchClean⟩

  have hslicesBefore :=
    PointRegister.slices_of_regValue_some
      pointReg st hR hpointLength hpoint

  rcases hslicesBefore with
    ⟨_, hxBefore, hyBefore⟩

  have hpointCopied :
      regValue pointReg copied = encodeNat (.some hR) := by
    calc
      regValue pointReg copied = regValue pointReg st :=
        Arithmetic.AgreesOn.regValue hpointAgree
      _ = encodeNat (.some hR) := hpoint

  have hslicesCopied :=
    PointRegister.slices_of_regValue_some
      pointReg copied hR hpointLength hpointCopied

  rcases hslicesCopied with
    ⟨htag, hxPublic, hyPublic⟩

  let after :=
    Classical.run
      (pointAddFlags pointReg workStart xC yC)
      copied

  have hflags :
      AgreesOn pointReg copied after ∧
        regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied ∧
        regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied ∧
        after (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) copied = 0) ∧
        after (pointAddGenericFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied ≠ xC.val) ∧
        after (pointAddDoubleFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied = xC.val ∧
            regValue (PointRegister.y pointReg) copied ≠ (-yC).val) ∧
        Clean (pointAddBranchWork workStart) after := by
    simpa [after] using
      pointAddFlags_semantics
        pointReg outReg workStart copied
        hpointLength hnodup hflagClean hbranchClean

  rcases hflags with
    ⟨_, hxKeep, hyKeep,
      hinfinity, hgeneric, hdouble, hcleanAfter⟩

  have hxFinal :
      regValue (pointAddX workStart) after = xR.val := by
    calc
      regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied := hxKeep
      _ = regValue (PointRegister.x pointReg) st := hxCopy
      _ = xR.val := hxBefore

  have hyFinal :
      regValue (pointAddY workStart) after = yR.val := by
    calc
      regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied := hyKeep
      _ = regValue (PointRegister.y pointReg) st := hyCopy
      _ = yR.val := hyBefore

  have hxVal :
      xR.val = xC.val ↔ xR = xC := by
    constructor
    · intro h
      exact ZMod.val_injective p h
    · intro h
      subst xC
      rfl

  have hyVal :
      yR.val = (-yC).val ↔ yR = -yC := by
    constructor
    · intro h
      exact ZMod.val_injective p h
    · intro h
      subst yR
      rfl

  have hinfinity' :
      after (pointAddInfinityFlag workStart) = false := by
    simpa [htag] using hinfinity

  have hgeneric' :
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) := by
    simpa [htag, hxPublic, hxVal] using hgeneric

  have hdouble' :
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) := by
    simpa [htag, hxPublic, hyPublic, hxVal, hyVal] using hdouble

  change
    regValue (pointAddX workStart) after = xR.val ∧
      regValue (pointAddY workStart) after = yR.val ∧
      after (pointAddInfinityFlag workStart) = false ∧
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) ∧
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) ∧
      Clean (pointAddBranchWork workStart) after

  exact
    ⟨hxFinal, hyFinal, hinfinity',
      hgeneric', hdouble', hcleanAfter⟩

/--
When only the infinity branch is enabled, the branch stage writes C into
`selected`.

The generic and doubling circuits still execute, but because their controls
are false their candidates are computed and uncomputed without changing
`selected`.
-/
theorem pointAddBranches_infinity_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = true)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (.some hC) := by
  rw [pointAddBranches, Classical.run_append,
    Classical.run_append,
    genericPointBranch_false workStart xC yC st hgeneric,
    doublePointBranch_false workStart st hdouble]
  exact infinityPointBranch_true_value
    workStart hC st hinfinity hclean

private theorem infinityPointBranch_false
    (workStart : Wire) (C : Point) (st : BasisState)
    (hcontrol : st (pointAddInfinityFlag workStart) = false) :
    Classical.run (infinityPointBranch workStart C) st = st := by
  let candidate := pointAddCandidate workStart
  let constant := (encode C).val
  have hcontrolNotCandidate :
      pointAddInfinityFlag workStart ∉ candidate := by
    intro hw
    exact pointAddInfinityFlag_not_mem_activeSupport workStart (by
      simp [candidate, pointAddBranchActiveSupport, hw])
  have hcontrolAfterLoad :
      Classical.run (loadConst candidate constant) st
          (pointAddInfinityFlag workStart) = false := by
    rw [loadConst_other
      (pointAddInfinityFlag workStart) candidate constant st
      hcontrolNotCandidate]
    exact hcontrol
  have hcandidateNodup : candidate.Nodup := by
    dsimp [candidate, pointAddCandidate]
    exact List.nodup_range'
  simp only [infinityPointBranch, Classical.run_append]
  rw [run_controlledCopyReg_false
    (pointAddInfinityFlag workStart) candidate
    (pointAddSelected workStart)
    (Classical.run (loadConst candidate constant) st)
    hcontrolAfterLoad]
  exact run_loadConst_twice candidate constant st hcandidateNodup

/--
When all three branch controls are false, nothing is XORed into `selected`.

Since `selected` starts clean, it stays zero, which is exactly the canonical
encoding of the point at infinity.
-/
theorem pointAddBranches_inverse_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (0 : Point) := by
  have hselectedClean :
      Clean (pointAddSelected workStart) st := by
    apply Arithmetic.Clean.mono hclean
    intro w hw
    simp [pointAddBranchWork, hw]
  rw [pointAddBranches, Classical.run_append,
    Classical.run_append,
    genericPointBranch_false workStart xC yC st hgeneric,
    doublePointBranch_false workStart st hdouble,
    infinityPointBranch_false workStart (.some hC) st hinfinity]
  simpa [encodeNat] using
    Arithmetic.Clean.regValue_eq_zero hselectedClean

private theorem pointAddCandidateSelected_nodup
    (workStart : Wire) :
    (pointAddCandidate workStart ++
      pointAddSelected workStart).Nodup := by
  simpa [pointAddCandidate, pointAddSelected] using
    (range'_append_nodup_of_le
      (workStart + candidateOffset) pointWidth
      (workStart + selectedOffset) pointWidth
      (by
        unfold selectedOffset
        omega))

private theorem pointAddControl_not_mem_selected
    (workStart index : Wire) (hindex : index < 6) :
    workStart + flagOffset + index ∉
      pointAddSelected workStart := by
  intro hw
  have hbounds := List.mem_range'_1.mp hw
  have hupper :
      workStart + flagOffset + index <
        workStart + candidateOffset := by
    simpa [candidateOffset, Nat.add_assoc] using
      Nat.add_lt_add_left hindex (workStart + flagOffset)
  have hcandidateBeforeSelected :
      workStart + candidateOffset ≤
        workStart + selectedOffset := by
    norm_num [selectedOffset, candidateOffset, pointWidth]
  exact (Nat.not_le_of_gt hupper)
    (hcandidateBeforeSelected.trans hbounds.1)

private theorem pointAddControl_candidateSelected_nodup
    (workStart index : Wire) (hindex : index < 6) :
    ((workStart + flagOffset + index) ::
      (pointAddCandidate workStart ++
        pointAddSelected workStart)).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro hw
    rcases List.mem_append.mp hw with hcandidate | hselected
    · exact pointAddControl_not_mem_activeSupport
        workStart index hindex (by
          simp [pointAddBranchActiveSupport, hcandidate])
    · exact pointAddControl_not_mem_selected
        workStart index hindex hselected
  · exact pointAddCandidateSelected_nodup workStart

private theorem pointAddActiveSupport_selected_disjoint
    (workStart : Wire) :
    ModExp.Schedule.WireDisjoint
      (pointAddBranchActiveSupport workStart)
      (pointAddSelected workStart) := by
  intro active hactive selected hselected
  have hselectedBounds := List.mem_range'_1.mp hselected
  have hflagBeforeSelected :
      workStart + flagOffset ≤
        workStart + selectedOffset := by
    norm_num [selectedOffset, candidateOffset, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset,
      fieldAreaSize, fieldWidth, Secp256k1Instance.fieldWidth,
      pointWidth]
  have hcandidateEnd :
      workStart + candidateOffset + pointWidth =
        workStart + selectedOffset := by
    simp [selectedOffset, Nat.add_assoc]
  have hselectedEnd :
      workStart + selectedOffset + pointWidth =
        pointAddArithmeticOffset workStart := by
    rw [pointAddArithmeticOffset, localWorkSize_eq]
    norm_num [selectedOffset, candidateOffset, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset,
      fieldAreaSize, fieldWidth, Secp256k1Instance.fieldWidth,
      pointWidth]
  have hfieldDisjoint
      (register : List Wire)
      (hregister : IsPointAddFieldRegister workStart register)
      (hactiveRegister : active ∈ register) :
      active ≠ selected := by
    intro heq
    subst selected
    exact (Nat.not_lt_of_ge
      (hflagBeforeSelected.trans hselectedBounds.1))
      (pointAddFieldRegister_belowFlagArea
        workStart register hregister active hactiveRegister)
  simp only [pointAddBranchActiveSupport, List.mem_append] at hactive
  rcases hactive with hx | hy | ht0 | ht1 | ht2 | ht3 | ht4 |
      hcandidate | hadd | hmul | hinv
  · exact hfieldDisjoint _
      (by simp [IsPointAddFieldRegister]) hx
  · exact hfieldDisjoint _
      (by simp [IsPointAddFieldRegister]) hy
  · exact hfieldDisjoint _
      (by simp [IsPointAddFieldRegister]) ht0
  · exact hfieldDisjoint _
      (by simp [IsPointAddFieldRegister]) ht1
  · exact hfieldDisjoint _
      (by simp [IsPointAddFieldRegister]) ht2
  · exact hfieldDisjoint _
      (by simp [IsPointAddFieldRegister]) ht3
  · exact hfieldDisjoint _
      (by simp [IsPointAddFieldRegister]) ht4
  · intro heq
    subst selected
    have hcandidateBounds := List.mem_range'_1.mp hcandidate
    rw [hcandidateEnd] at hcandidateBounds
    exact (Nat.not_lt_of_ge hselectedBounds.1)
      hcandidateBounds.2
  · intro heq
    subst selected
    have hlower := shiftWires_lower
      (pointAddArithmeticOffset workStart)
      Secp256k1Instance.secpAddLayout.allWires active hadd
    rw [← hselectedEnd] at hlower
    exact (Nat.not_lt_of_ge hlower) hselectedBounds.2
  · intro heq
    subst selected
    have hlower := shiftWires_lower
      (pointAddArithmeticOffset workStart)
      Secp256k1Instance.secpMulLayout.allWires active hmul
    rw [← hselectedEnd] at hlower
    exact (Nat.not_lt_of_ge hlower) hselectedBounds.2
  · intro heq
    subst selected
    have hlower := shiftWires_lower
      (pointAddArithmeticOffset workStart)
      Secp256k1Instance.secpLayout.allWires active hinv
    rw [← hselectedEnd] at hlower
    exact (Nat.not_lt_of_ge hlower) hselectedBounds.2

private theorem genericPointBranch_selectedValue
    (workStart : Wire) (xC yC : Fp)
    (st : BasisState)
    (hcontrol : st (pointAddGenericFlag workStart) = true)
    (hcleanSelected : Clean (pointAddSelected workStart) st) :
    regValue (pointAddSelected workStart)
        (Classical.run (genericPointBranch workStart xC yC) st) =
      regValue (pointAddCandidate workStart)
        (Classical.run
          (genericPointCompute workStart xC yC ++
            packFinitePoint
              (pointAddT2 workStart)
              (pointAddT4 workStart)
              (pointAddCandidate workStart)) st) := by
  let active :=
    genericPointCompute workStart xC yC ++
      packFinitePoint
        (pointAddT2 workStart)
        (pointAddT4 workStart)
        (pointAddCandidate workStart)
  let mid := Classical.run active st
  have hfree : Classical.HPFree active := by
    simp [active, genericPointCompute_HPFree, packFinitePoint_HPFree]
  have hwellFormed : CircuitWellFormed active := by
    simp [active, genericPointCompute_wellFormed,
      packFinitePoint_wellFormed]
  have huses :
      CircuitUsesOnly (pointAddBranchActiveSupport workStart) active :=
    usesOnly_append
      (genericPointCompute_usesOnly workStart xC yC)
      (packFinitePoint_usesOnly_pointAdd workStart)
  have hcontrolMid :
      mid (pointAddGenericFlag workStart) = true := by
    change Classical.run active st
      (pointAddGenericFlag workStart) = true
    rw [huses.preservesOutside st
      (pointAddGenericFlag workStart)
      (pointAddGenericFlag_not_mem_activeSupport workStart)]
    exact hcontrol
  have hcontrolledNodup :
      (pointAddGenericFlag workStart ::
        pointAddCandidate workStart ++
        pointAddSelected workStart).Nodup := by
    simpa [pointAddGenericFlag, Nat.add_assoc] using
      pointAddControl_candidateSelected_nodup workStart 3 (by norm_num)
  have hcontrolled :
      Classical.run
          (controlledCopyReg
            (pointAddGenericFlag workStart)
            (pointAddCandidate workStart)
            (pointAddSelected workStart)) mid =
        Classical.run
          (Arithmetic.copyReg
            (pointAddCandidate workStart)
            (pointAddSelected workStart)) mid :=
    run_controlledCopyReg_true
      (pointAddGenericFlag workStart)
      (pointAddCandidate workStart)
      (pointAddSelected workStart) mid
      hcontrolledNodup hcontrolMid
  have hbennett := ModExp.bennett_cleanup_copyOut
    active
    (pointAddBranchActiveSupport workStart)
    (pointAddCandidate workStart)
    (pointAddSelected workStart)
    st huses hfree hwellFormed
    (pointAddActiveSupport_selected_disjoint workStart)
    (by simp [pointAddCandidate, pointAddSelected])
    (pointAddCandidateSelected_nodup workStart)
    hcleanSelected
  have hbranchRun :
      Classical.run (genericPointBranch workStart xC yC) st =
        Classical.run
          (active ++
            Arithmetic.copyReg
              (pointAddCandidate workStart)
              (pointAddSelected workStart) ++
            active.reverse) st := by
    have hafterCopy := congrArg
      (Classical.run active.reverse) hcontrolled
    simpa [genericPointBranch, active, mid,
      Classical.run_append] using hafterCopy
  rw [hbranchRun]
  simpa only [active] using hbennett.2

private theorem doublePointBranch_selectedValue
    (workStart : Wire) (st : BasisState)
    (hcontrol : st (pointAddDoubleFlag workStart) = true)
    (hcleanSelected : Clean (pointAddSelected workStart) st) :
    regValue (pointAddSelected workStart)
        (Classical.run (doublePointBranch workStart) st) =
      regValue (pointAddCandidate workStart)
        (Classical.run
          (doublePointCompute workStart ++
            packFinitePoint
              (pointAddT2 workStart)
              (pointAddT4 workStart)
              (pointAddCandidate workStart)) st) := by
  let active :=
    doublePointCompute workStart ++
      packFinitePoint
        (pointAddT2 workStart)
        (pointAddT4 workStart)
        (pointAddCandidate workStart)
  let mid := Classical.run active st
  have hfree : Classical.HPFree active := by
    simp [active, doublePointCompute_HPFree, packFinitePoint_HPFree]
  have hwellFormed : CircuitWellFormed active := by
    simp [active, doublePointCompute_wellFormed,
      packFinitePoint_wellFormed]
  have huses :
      CircuitUsesOnly (pointAddBranchActiveSupport workStart) active :=
    usesOnly_append
      (doublePointCompute_usesOnly workStart)
      (packFinitePoint_usesOnly_pointAdd workStart)
  have hcontrolMid :
      mid (pointAddDoubleFlag workStart) = true := by
    change Classical.run active st
      (pointAddDoubleFlag workStart) = true
    rw [huses.preservesOutside st
      (pointAddDoubleFlag workStart)
      (pointAddDoubleFlag_not_mem_activeSupport workStart)]
    exact hcontrol
  have hcontrolledNodup :
      (pointAddDoubleFlag workStart ::
        pointAddCandidate workStart ++
        pointAddSelected workStart).Nodup := by
    simpa [pointAddDoubleFlag, Nat.add_assoc] using
      pointAddControl_candidateSelected_nodup workStart 5 (by norm_num)
  have hcontrolled :
      Classical.run
          (controlledCopyReg
            (pointAddDoubleFlag workStart)
            (pointAddCandidate workStart)
            (pointAddSelected workStart)) mid =
        Classical.run
          (Arithmetic.copyReg
            (pointAddCandidate workStart)
            (pointAddSelected workStart)) mid :=
    run_controlledCopyReg_true
      (pointAddDoubleFlag workStart)
      (pointAddCandidate workStart)
      (pointAddSelected workStart) mid
      hcontrolledNodup hcontrolMid
  have hbennett := ModExp.bennett_cleanup_copyOut
    active
    (pointAddBranchActiveSupport workStart)
    (pointAddCandidate workStart)
    (pointAddSelected workStart)
    st huses hfree hwellFormed
    (pointAddActiveSupport_selected_disjoint workStart)
    (by simp [pointAddCandidate, pointAddSelected])
    (pointAddCandidateSelected_nodup workStart)
    hcleanSelected
  have hbranchRun :
      Classical.run (doublePointBranch workStart) st =
        Classical.run
          (active ++
            Arithmetic.copyReg
              (pointAddCandidate workStart)
              (pointAddSelected workStart) ++
            active.reverse) st := by
    have hafterCopy := congrArg
      (Classical.run active.reverse) hcontrolled
    simpa [doublePointBranch, active, mid,
      Classical.run_append] using hafterCopy
  rw [hbranchRun]
  simpa only [active] using hbennett.2

private theorem threeXSquared_usesOnly_exact
    (offset : Wire) (x scratch₀ scratch₁ out : List Wire) :
    CircuitUsesOnly
      (x ++ scratch₀ ++ scratch₁ ++ out ++
        shiftWires offset
          Secp256k1Instance.secpAddLayout.allWires ++
        shiftWires offset
          Secp256k1Instance.secpMulLayout.allWires)
      (threeXSquared offset x scratch₀ scratch₁ out) := by
  let support :=
    x ++ scratch₀ ++ scratch₁ ++ out ++
      shiftWires offset
        Secp256k1Instance.secpAddLayout.allWires ++
      shiftWires offset
        Secp256k1Instance.secpMulLayout.allWires
  have hsquare : CircuitUsesOnly support
      (fieldMul offset x x scratch₀) := by
    apply usesOnly_mono (fieldMul_usesOnly offset x x scratch₀)
    intro w hw
    simp only [support, List.mem_append] at hw ⊢
    aesop
  have htwice : CircuitUsesOnly support
      (fieldAdd offset scratch₀ scratch₀ scratch₁) := by
    apply usesOnly_mono
      (fieldAdd_usesOnly offset scratch₀ scratch₀ scratch₁)
    intro w hw
    simp only [support, List.mem_append] at hw ⊢
    aesop
  have hthree : CircuitUsesOnly support
      (fieldAdd offset scratch₁ scratch₀ out) := by
    apply usesOnly_mono
      (fieldAdd_usesOnly offset scratch₁ scratch₀ out)
    intro w hw
    simp only [support, List.mem_append] at hw ⊢
    aesop
  have hall := usesOnly_append
    (usesOnly_append
      (usesOnly_append
        (usesOnly_append hsquare htwice) hthree)
      (usesOnly_reverse htwice))
    (usesOnly_reverse hsquare)
  simpa [support, threeXSquared, List.append_assoc] using hall

private theorem threeXSquared_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire) (xR : Fp) (st : BasisState)
    (hxReg : regValue (pointAddX workStart) st = xR.val)
    (hclean : Clean (pointAddBranchWork workStart) st) :
    let after := Classical.run
      (threeXSquared
        (pointAddArithmeticOffset workStart)
        (pointAddX workStart)
        (pointAddT0 workStart)
        (pointAddT1 workStart)
        (pointAddT2 workStart)) st
    regValue (pointAddT2 workStart) after =
        (doubleNumerator xR).val ∧
      ∀ w, w ∉ pointAddT2 workStart → after w = st w := by
  have hX : IsPointAddFieldRegister workStart
      (pointAddX workStart) := by
    simp [IsPointAddFieldRegister]
  have hT0 : IsPointAddFieldRegister workStart
      (pointAddT0 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT1 : IsPointAddFieldRegister workStart
      (pointAddT1 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT2 : IsPointAddFieldRegister workStart
      (pointAddT2 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT0T1 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT0, pointAddT1] using
      pointAddFieldAt_disjoint workStart 2 3 (by norm_num)
  have hT0T2 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT0, pointAddT2] using
      pointAddFieldAt_disjoint workStart 2 4 (by norm_num)
  have hT1T0 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT1, pointAddT0] using
      pointAddFieldAt_disjoint workStart 3 2 (by norm_num)
  have hT1T2 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT1, pointAddT2] using
      pointAddFieldAt_disjoint workStart 3 4 (by norm_num)
  have hT2T0 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT2, pointAddT0] using
      pointAddFieldAt_disjoint workStart 4 2 (by norm_num)
  have hT2T1 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT2, pointAddT1] using
      pointAddFieldAt_disjoint workStart 4 3 (by norm_num)
  have hXT2 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT2 workStart) := by
    simpa [pointAddX, pointAddT2] using
      pointAddFieldAt_disjoint workStart 0 4 (by norm_num)
  have hcleanT0 : Clean (pointAddT0 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT1 : Clean (pointAddT1 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT2 : Clean (pointAddT2 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanAdd := cleanAddEngine_of_branchWork workStart st hclean
  have hcleanMul := cleanMulEngine_of_branchWork workStart st hclean

  let square := fieldMul
    (pointAddArithmeticOffset workStart)
    (pointAddX workStart) (pointAddX workStart)
    (pointAddT0 workStart)
  let afterSquare := Classical.run square st
  have hsquare := fieldMul_correct workStart
    (pointAddX workStart) (pointAddX workStart)
    (pointAddT0 workStart) hX hX hT0
    (by
      simpa [pointAddT0, pointAddX] using
        pointAddFieldAt_ne workStart 2 0 (by norm_num))
    (by
      simpa [pointAddT0, pointAddX] using
        pointAddFieldAt_ne workStart 2 0 (by norm_num))
    st hcleanT0 hcleanMul
    (by rw [hxReg]; exact xR.val_lt)
    (by rw [hxReg]; exact xR.val_lt)
  dsimp only at hsquare
  change regValue (pointAddT0 workStart) afterSquare =
      regValue (pointAddX workStart) st *
        regValue (pointAddX workStart) st % p ∧
    ∀ w, w ∉ pointAddT0 workStart →
      afterSquare w = st w at hsquare
  have hsquareVal : regValue (pointAddT0 workStart) afterSquare =
      (xR ^ 2).val := by
    calc
      regValue (pointAddT0 workStart) afterSquare =
          xR.val * xR.val % p := by simpa [hxReg] using hsquare.1
      _ = (xR * xR).val := by rw [ZMod.val_mul]
      _ = (xR ^ 2).val := by rw [pow_two]

  let twice := fieldAdd
    (pointAddArithmeticOffset workStart)
    (pointAddT0 workStart) (pointAddT0 workStart)
    (pointAddT1 workStart)
  let afterTwice := Classical.run twice afterSquare
  have hcleanT1Square := clean_of_preserved_outside
    hT1T0 hcleanT1 hsquare.2
  have hcleanAddSquare := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanAdd hsquare.2
  have htwice := fieldAdd_correct workStart
    (pointAddT0 workStart) (pointAddT0 workStart)
    (pointAddT1 workStart) hT0 hT0 hT1
    (by
      simpa [pointAddT1, pointAddT0] using
        pointAddFieldAt_ne workStart 3 2 (by norm_num))
    (by
      simpa [pointAddT1, pointAddT0] using
        pointAddFieldAt_ne workStart 3 2 (by norm_num))
    afterSquare hcleanT1Square hcleanAddSquare
    (by rw [hsquareVal]; exact (xR ^ 2).val_lt)
    (by rw [hsquareVal]; exact (xR ^ 2).val_lt)
  dsimp only at htwice
  change regValue (pointAddT1 workStart) afterTwice =
      (regValue (pointAddT0 workStart) afterSquare +
        regValue (pointAddT0 workStart) afterSquare) % p ∧
    ∀ w, w ∉ pointAddT1 workStart →
      afterTwice w = afterSquare w at htwice
  have htwiceVal : regValue (pointAddT1 workStart) afterTwice =
      (2 * xR ^ 2).val := by
    rw [htwice.1, hsquareVal, ← ZMod.val_add, two_mul]
  have ht0Twice := regValue_of_preserved_outside hT0T1 htwice.2

  let three := fieldAdd
    (pointAddArithmeticOffset workStart)
    (pointAddT1 workStart) (pointAddT0 workStart)
    (pointAddT2 workStart)
  let afterThree := Classical.run three afterTwice
  have hcleanT2Square := clean_of_preserved_outside
    hT2T0 hcleanT2 hsquare.2
  have hcleanT2Twice := clean_of_preserved_outside
    hT2T1 hcleanT2Square htwice.2
  have hcleanAddTwice := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT1 workStart) hT1)
    hcleanAddSquare htwice.2
  have hthree := fieldAdd_correct workStart
    (pointAddT1 workStart) (pointAddT0 workStart)
    (pointAddT2 workStart) hT1 hT0 hT2
    (by
      simpa [pointAddT2, pointAddT1] using
        pointAddFieldAt_ne workStart 4 3 (by norm_num))
    (by
      simpa [pointAddT2, pointAddT0] using
        pointAddFieldAt_ne workStart 4 2 (by norm_num))
    afterTwice hcleanT2Twice hcleanAddTwice
    (by rw [htwiceVal]; exact (2 * xR ^ 2).val_lt)
    (by rw [ht0Twice, hsquareVal]; exact (xR ^ 2).val_lt)
  dsimp only at hthree
  change regValue (pointAddT2 workStart) afterThree =
      (regValue (pointAddT1 workStart) afterTwice +
        regValue (pointAddT0 workStart) afterTwice) % p ∧
    ∀ w, w ∉ pointAddT2 workStart →
      afterThree w = afterTwice w at hthree
  have hthreeVal : regValue (pointAddT2 workStart) afterThree =
      (doubleNumerator xR).val := by
    calc
      regValue (pointAddT2 workStart) afterThree =
          ((2 * xR ^ 2).val + (xR ^ 2).val) % p := by
        simpa [htwiceVal, ht0Twice, hsquareVal] using hthree.1
      _ = (2 * xR ^ 2 + xR ^ 2).val := by
        rw [ZMod.val_add]
      _ = (doubleNumerator xR).val := by
        exact congrArg ZMod.val (by
          simp only [doubleNumerator]
          ring)

  let preparation := square ++ twice
  let preparationSupport :=
    pointAddX workStart ++
      (pointAddT0 workStart ++
        (pointAddT1 workStart ++
          (shiftWires (pointAddArithmeticOffset workStart)
                Secp256k1Instance.secpAddLayout.allWires ++
            shiftWires (pointAddArithmeticOffset workStart)
              Secp256k1Instance.secpMulLayout.allWires)))
  have hpreparationRun :
      Classical.run preparation st = afterTwice := by
    simp [preparation, twice, afterTwice, square, afterSquare,
      Classical.run_append]
  have hpreparationUses :
      CircuitUsesOnly preparationSupport preparation := by
    apply usesOnly_append
    · apply usesOnly_mono
        (fieldMul_usesOnly (pointAddArithmeticOffset workStart)
          (pointAddX workStart) (pointAddX workStart)
          (pointAddT0 workStart))
      intro w hw
      rcases List.mem_append.mp hw with hprefix | hmul
      · rcases List.mem_append.mp hprefix with hpair | ht0w
        · rcases List.mem_append.mp hpair with hxw | hxw
          · simp [preparationSupport, hxw]
          · simp [preparationSupport, hxw]
        · simp [preparationSupport, ht0w]
      · simp [preparationSupport, hmul]
    · apply usesOnly_mono
        (fieldAdd_usesOnly (pointAddArithmeticOffset workStart)
          (pointAddT0 workStart) (pointAddT0 workStart)
          (pointAddT1 workStart))
      intro w hw
      rcases List.mem_append.mp hw with hprefix | hadd
      · rcases List.mem_append.mp hprefix with hpair | ht1w
        · rcases List.mem_append.mp hpair with ht0w | ht0w
          · simp [preparationSupport, ht0w]
          · simp [preparationSupport, ht0w]
        · simp [preparationSupport, ht1w]
      · simp [preparationSupport, hadd]
  have hpreparationFree : Classical.HPFree preparation := by
    simp [preparation, square, twice, fieldMul_HPFree,
      fieldAdd_HPFree]
  have hpreparationWellFormed : CircuitWellFormed preparation := by
    simp [preparation, square, twice, fieldMul_wellFormed,
      fieldAdd_wellFormed, IsPointAddFieldRegister]
  have hpreparationT2 : ModExp.Schedule.WireDisjoint
      preparationSupport (pointAddT2 workStart) := by
    intro w hw v hv
    dsimp only [preparationSupport] at hw
    rcases List.mem_append.mp hw with hxw | hrest
    · exact hXT2 w hxw v hv
    rcases List.mem_append.mp hrest with ht0w | hrest
    · exact hT0T2 w ht0w v hv
    rcases List.mem_append.mp hrest with ht1w | hrest
    · exact hT1T2 w ht1w v hv
    rcases List.mem_append.mp hrest with haddw | hmulw
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpAddLayout.allWires
        (pointAddT2 workStart) hT2) w haddw v hv
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpMulLayout.allWires
        (pointAddT2 workStart) hT2) w hmulw v hv
  have hresult := bennett_uncompute_after_local_update
    preparation three preparationSupport (pointAddT2 workStart) st
    hpreparationUses hpreparationFree hpreparationWellFormed
    hpreparationT2 (by
      intro w hw
      rw [hpreparationRun]
      exact hthree.2 w hw)
  dsimp only at hresult
  let after := Classical.run
    (preparation ++ three ++ preparation.reverse) st
  change (∀ w, w ∉ pointAddT2 workStart → after w = st w) ∧
    (∀ w ∈ pointAddT2 workStart,
      after w = Classical.run three
        (Classical.run preparation st) w) at hresult
  have hresultValue : regValue (pointAddT2 workStart) after =
      (doubleNumerator xR).val := by
    calc
      regValue (pointAddT2 workStart) after =
          regValue (pointAddT2 workStart)
            (Classical.run three
              (Classical.run preparation st)) := by
        apply regValue_congr
        exact hresult.2
      _ = regValue (pointAddT2 workStart) afterThree := by
        rw [hpreparationRun]
      _ = (doubleNumerator xR).val := hthreeVal
  have hrun :
      Classical.run
        (threeXSquared
          (pointAddArithmeticOffset workStart)
          (pointAddX workStart)
          (pointAddT0 workStart)
          (pointAddT1 workStart)
          (pointAddT2 workStart)) st = after := by
    simp [threeXSquared, after, preparation, square, twice, three,
      Classical.run_append, List.reverse_append, List.append_assoc]
  dsimp only
  rw [hrun]
  exact ⟨hresultValue, hresult.1⟩

private theorem genericPointCompute_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire) (xR yR xC yC : Fp)
    (hx : xR ≠ xC)
    (st : BasisState)
    (hxReg : regValue (pointAddX workStart) st = xR.val)
    (hyReg : regValue (pointAddY workStart) st = yR.val)
    (hclean : Clean (pointAddBranchWork workStart) st) :
    let after := Classical.run
      (genericPointCompute workStart xC yC) st
    regValue (pointAddT2 workStart) after =
        (genericX xR yR xC yC).val ∧
      regValue (pointAddT4 workStart) after =
        (genericY xR yR xC yC).val ∧
      Clean (pointAddCandidate workStart) after := by
  have hX : IsPointAddFieldRegister workStart
      (pointAddX workStart) := by
    simp [IsPointAddFieldRegister]
  have hY : IsPointAddFieldRegister workStart
      (pointAddY workStart) := by
    simp [IsPointAddFieldRegister]
  have hT0 : IsPointAddFieldRegister workStart
      (pointAddT0 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT1 : IsPointAddFieldRegister workStart
      (pointAddT1 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT2 : IsPointAddFieldRegister workStart
      (pointAddT2 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT3 : IsPointAddFieldRegister workStart
      (pointAddT3 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT4 : IsPointAddFieldRegister workStart
      (pointAddT4 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT0T1 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT0, pointAddT1] using
      pointAddFieldAt_disjoint workStart 2 3 (by norm_num)
  have hT0T2 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT0, pointAddT2] using
      pointAddFieldAt_disjoint workStart 2 4 (by norm_num)
  have hT0T3 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT3 workStart) := by
    simpa [pointAddT0, pointAddT3] using
      pointAddFieldAt_disjoint workStart 2 5 (by norm_num)
  have hT0T4 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT4 workStart) := by
    simpa [pointAddT0, pointAddT4] using
      pointAddFieldAt_disjoint workStart 2 6 (by norm_num)
  have hT1T0 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT1, pointAddT0] using
      pointAddFieldAt_disjoint workStart 3 2 (by norm_num)
  have hT1T2 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT1, pointAddT2] using
      pointAddFieldAt_disjoint workStart 3 4 (by norm_num)
  have hT1T3 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT3 workStart) := by
    simpa [pointAddT1, pointAddT3] using
      pointAddFieldAt_disjoint workStart 3 5 (by norm_num)
  have hT1T4 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT4 workStart) := by
    simpa [pointAddT1, pointAddT4] using
      pointAddFieldAt_disjoint workStart 3 6 (by norm_num)
  have hT2T0 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT2, pointAddT0] using
      pointAddFieldAt_disjoint workStart 4 2 (by norm_num)
  have hT2T1 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT2, pointAddT1] using
      pointAddFieldAt_disjoint workStart 4 3 (by norm_num)
  have hT2T3 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT3 workStart) := by
    simpa [pointAddT2, pointAddT3] using
      pointAddFieldAt_disjoint workStart 4 5 (by norm_num)
  have hT2T4 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT4 workStart) := by
    simpa [pointAddT2, pointAddT4] using
      pointAddFieldAt_disjoint workStart 4 6 (by norm_num)
  have hT3T0 : ModExp.Schedule.WireDisjoint
      (pointAddT3 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT3, pointAddT0] using
      pointAddFieldAt_disjoint workStart 5 2 (by norm_num)
  have hT3T1 : ModExp.Schedule.WireDisjoint
      (pointAddT3 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT3, pointAddT1] using
      pointAddFieldAt_disjoint workStart 5 3 (by norm_num)
  have hT3T2 : ModExp.Schedule.WireDisjoint
      (pointAddT3 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT3, pointAddT2] using
      pointAddFieldAt_disjoint workStart 5 4 (by norm_num)
  have hT4T0 : ModExp.Schedule.WireDisjoint
      (pointAddT4 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT4, pointAddT0] using
      pointAddFieldAt_disjoint workStart 6 2 (by norm_num)
  have hT4T1 : ModExp.Schedule.WireDisjoint
      (pointAddT4 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT4, pointAddT1] using
      pointAddFieldAt_disjoint workStart 6 3 (by norm_num)
  have hT4T2 : ModExp.Schedule.WireDisjoint
      (pointAddT4 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT4, pointAddT2] using
      pointAddFieldAt_disjoint workStart 6 4 (by norm_num)
  have hT4T3 : ModExp.Schedule.WireDisjoint
      (pointAddT4 workStart) (pointAddT3 workStart) := by
    simpa [pointAddT4, pointAddT3] using
      pointAddFieldAt_disjoint workStart 6 5 (by norm_num)
  have hXT0 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT0 workStart) := by
    simpa [pointAddX, pointAddT0] using
      pointAddFieldAt_disjoint workStart 0 2 (by norm_num)
  have hXT1 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT1 workStart) := by
    simpa [pointAddX, pointAddT1] using
      pointAddFieldAt_disjoint workStart 0 3 (by norm_num)
  have hXT2 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT2 workStart) := by
    simpa [pointAddX, pointAddT2] using
      pointAddFieldAt_disjoint workStart 0 4 (by norm_num)
  have hYT0 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT0 workStart) := by
    simpa [pointAddY, pointAddT0] using
      pointAddFieldAt_disjoint workStart 1 2 (by norm_num)
  have hYT1 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT1 workStart) := by
    simpa [pointAddY, pointAddT1] using
      pointAddFieldAt_disjoint workStart 1 3 (by norm_num)
  have hYT2 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT2 workStart) := by
    simpa [pointAddY, pointAddT2] using
      pointAddFieldAt_disjoint workStart 1 4 (by norm_num)
  have hYT4 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT4 workStart) := by
    simpa [pointAddY, pointAddT4] using
      pointAddFieldAt_disjoint workStart 1 6 (by norm_num)
  have hcleanT0 : Clean (pointAddT0 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT1 : Clean (pointAddT1 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT2 : Clean (pointAddT2 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT3 : Clean (pointAddT3 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT4 : Clean (pointAddT4 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanCandidate : Clean (pointAddCandidate workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanAdd := cleanAddEngine_of_branchWork workStart st hclean
  have hcleanMul := cleanMulEngine_of_branchWork workStart st hclean
  have hcleanInv := cleanInvEngine_of_branchWork workStart st hclean

  let numerator := fieldSubConst
    (pointAddArithmeticOffset workStart)
    (pointAddY workStart) yC.val (pointAddT0 workStart)
  let afterNumerator := Classical.run numerator st
  have hn := fieldSubConst_correct workStart
    (pointAddY workStart) (pointAddT0 workStart) yC.val
    hY hT0 (by
      simpa [pointAddY, pointAddT0] using
        pointAddFieldAt_ne workStart 2 1 (by norm_num))
    st hcleanT0
    (clean_fieldSubEngine_of_addEngine workStart st hcleanAdd)
    (by simpa [hyReg] using yR.val_lt) yC.val_lt
  dsimp only at hn
  change regValue (pointAddT0 workStart) afterNumerator =
      (regValue (pointAddY workStart) st + p - yC.val) % p ∧
    ∀ w, w ∉ pointAddT0 workStart →
      afterNumerator w = st w at hn
  have hnVal : regValue (pointAddT0 workStart) afterNumerator =
      (yR - yC).val := by
    calc
      regValue (pointAddT0 workStart) afterNumerator =
          (yR.val + p - yC.val) % p := by
        simpa [hyReg] using hn.1
      _ = (yR - yC).val := fieldSubVal yR yC

  let denominator := fieldSubConst
    (pointAddArithmeticOffset workStart)
    (pointAddX workStart) xC.val (pointAddT1 workStart)
  let afterDenominator := Classical.run denominator afterNumerator
  have hcleanT1N := clean_of_preserved_outside
    hT1T0 hcleanT1 hn.2
  have hcleanAddN := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanAdd hn.2
  have hxN := regValue_of_preserved_outside hXT0 hn.2
  have hd := fieldSubConst_correct workStart
    (pointAddX workStart) (pointAddT1 workStart) xC.val
    hX hT1 (by
      simpa [pointAddX, pointAddT1] using
        pointAddFieldAt_ne workStart 3 0 (by norm_num))
    afterNumerator hcleanT1N
    (clean_fieldSubEngine_of_addEngine workStart afterNumerator hcleanAddN)
    (by rw [hxN, hxReg]; exact xR.val_lt) xC.val_lt
  dsimp only at hd
  change regValue (pointAddT1 workStart) afterDenominator =
      (regValue (pointAddX workStart) afterNumerator + p - xC.val) % p ∧
    ∀ w, w ∉ pointAddT1 workStart →
      afterDenominator w = afterNumerator w at hd
  have hdVal : regValue (pointAddT1 workStart) afterDenominator =
      (xR - xC).val := by
    calc
      regValue (pointAddT1 workStart) afterDenominator =
          (xR.val + p - xC.val) % p := by
        simpa [hxN, hxReg] using hd.1
      _ = (xR - xC).val := fieldSubVal xR xC

  let inverse := fieldInv
    (pointAddArithmeticOffset workStart)
    (pointAddT1 workStart) (pointAddT2 workStart)
  let afterInverse := Classical.run inverse afterDenominator
  have hcleanT2N := clean_of_preserved_outside
    hT2T0 hcleanT2 hn.2
  have hcleanT2D := clean_of_preserved_outside
    hT2T1 hcleanT2N hd.2
  have hcleanInvN := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanInv hn.2
  have hcleanInvD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpLayout.allWires
      (pointAddT1 workStart) hT1)
    hcleanInvN hd.2
  have hdenNonzero :
      ((regValue (pointAddT1 workStart) afterDenominator : Nat) : Fp) ≠ 0 := by
    rw [hdVal, ZMod.natCast_zmod_val]
    exact sub_ne_zero.mpr hx
  have hi := fieldInv_correct workStart
    (pointAddT1 workStart) (pointAddT2 workStart)
    hT1 hT2 (by
      simpa [pointAddT1, pointAddT2] using
        pointAddFieldAt_ne workStart 4 3 (by norm_num))
    afterDenominator hcleanT2D hcleanInvD
    (by rw [hdVal]; exact (xR - xC).val_lt) hdenNonzero
  dsimp only at hi
  change regValue (pointAddT2 workStart) afterInverse =
      (((regValue (pointAddT1 workStart) afterDenominator : Nat) : Fp)⁻¹).val ∧
    ∀ w, w ∉ pointAddT2 workStart →
      afterInverse w = afterDenominator w at hi
  have hiVal : regValue (pointAddT2 workStart) afterInverse =
      (xR - xC)⁻¹.val := by
    simpa [hdVal, ZMod.natCast_zmod_val] using hi.1

  let slope := fieldMul
    (pointAddArithmeticOffset workStart)
    (pointAddT0 workStart) (pointAddT2 workStart)
    (pointAddT3 workStart)
  let afterSlope := Classical.run slope afterInverse
  have hcleanT3N := clean_of_preserved_outside
    hT3T0 hcleanT3 hn.2
  have hcleanT3D := clean_of_preserved_outside
    hT3T1 hcleanT3N hd.2
  have hcleanT3I := clean_of_preserved_outside
    hT3T2 hcleanT3D hi.2
  have hcleanMulN := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanMul hn.2
  have hcleanMulD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT1 workStart) hT1)
    hcleanMulN hd.2
  have hcleanMulI := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT2 workStart) hT2)
    hcleanMulD hi.2
  have hnD := regValue_of_preserved_outside hT0T1 hd.2
  have hnI := regValue_of_preserved_outside hT0T2 hi.2
  have ht0I : regValue (pointAddT0 workStart) afterInverse =
      (yR - yC).val := by
    rw [hnI, hnD, hnVal]
  have hs := fieldMul_correct workStart
    (pointAddT0 workStart) (pointAddT2 workStart)
    (pointAddT3 workStart) hT0 hT2 hT3
    (by
      simpa [pointAddT3, pointAddT0] using
        pointAddFieldAt_ne workStart 5 2 (by norm_num))
    (by
      simpa [pointAddT3, pointAddT2] using
        pointAddFieldAt_ne workStart 5 4 (by norm_num))
    afterInverse hcleanT3I hcleanMulI
    (by rw [ht0I]; exact (yR - yC).val_lt)
    (by rw [hiVal]; exact (xR - xC)⁻¹.val_lt)
  dsimp only at hs
  change regValue (pointAddT3 workStart) afterSlope =
      regValue (pointAddT0 workStart) afterInverse *
        regValue (pointAddT2 workStart) afterInverse % p ∧
    ∀ w, w ∉ pointAddT3 workStart →
      afterSlope w = afterInverse w at hs
  have hsVal : regValue (pointAddT3 workStart) afterSlope =
      (genericSlope xR yR xC yC).val := by
    calc
      regValue (pointAddT3 workStart) afterSlope =
          (yR - yC).val * (xR - xC)⁻¹.val % p := by
        simpa [ht0I, hiVal] using hs.1
      _ = ((yR - yC) * (xR - xC)⁻¹).val := by
        rw [ZMod.val_mul]
      _ = (genericSlope xR yR xC yC).val := by
        rfl

  let preparation := numerator ++ denominator ++ inverse
  let preparationSupport :=
    pointAddX workStart ++
      (pointAddY workStart ++
        (pointAddT0 workStart ++
          (pointAddT1 workStart ++
            (pointAddT2 workStart ++
              (shiftWires (pointAddArithmeticOffset workStart)
                    Secp256k1Instance.secpAddLayout.allWires ++
                shiftWires (pointAddArithmeticOffset workStart)
                  Secp256k1Instance.secpLayout.allWires)))))
  have hpreparationRun :
      Classical.run preparation st = afterInverse := by
    simp [preparation, inverse, afterInverse, denominator,
      afterDenominator, numerator, afterNumerator,
      Classical.run_append]
  have hpreparationUses : CircuitUsesOnly preparationSupport preparation := by
    apply usesOnly_append
    · apply usesOnly_append
      · apply usesOnly_mono
          (fieldSubConst_usesOnly
            (pointAddArithmeticOffset workStart)
            (pointAddY workStart) yC.val (pointAddT0 workStart))
        intro w hw
        rcases List.mem_append.mp hw with hfields | haddw
        · rcases List.mem_append.mp hfields with hyw | ht0w
          · simp only [preparationSupport, List.mem_append]
            exact Or.inr (Or.inl hyw)
          · simp only [preparationSupport, List.mem_append]
            exact Or.inr (Or.inr (Or.inl ht0w))
        · simp only [preparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inl haddw)))))
      · apply usesOnly_mono
          (fieldSubConst_usesOnly
            (pointAddArithmeticOffset workStart)
            (pointAddX workStart) xC.val (pointAddT1 workStart))
        intro w hw
        rcases List.mem_append.mp hw with hfields | haddw
        · rcases List.mem_append.mp hfields with hxw | ht1w
          · simp only [preparationSupport, List.mem_append]
            exact Or.inl hxw
          · simp only [preparationSupport, List.mem_append]
            exact Or.inr (Or.inr (Or.inr (Or.inl ht1w)))
        · simp only [preparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inl haddw)))))
    · apply usesOnly_mono
        (fieldInv_usesOnly
          (pointAddArithmeticOffset workStart)
          (pointAddT1 workStart) (pointAddT2 workStart))
      intro w hw
      rcases List.mem_append.mp hw with hfields | hinvw
      · rcases List.mem_append.mp hfields with ht1w | ht2w
        · simp only [preparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inr (Or.inl ht1w)))
        · simp only [preparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht2w))))
      · simp only [preparationSupport, List.mem_append]
        exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr hinvw)))))
  have hpreparationFree : Classical.HPFree preparation := by
    simp [preparation, numerator, denominator, inverse,
      fieldSubConst_HPFree, fieldInv_HPFree]
  have hpreparationWellFormed : CircuitWellFormed preparation := by
    simp [preparation, numerator, denominator, inverse,
      fieldSubConst_wellFormed, fieldInv_wellFormed,
      IsPointAddFieldRegister]
  have hpreparationT3 : ModExp.Schedule.WireDisjoint
      preparationSupport (pointAddT3 workStart) := by
    intro w hw v hv
    dsimp only [preparationSupport] at hw
    rcases List.mem_append.mp hw with hxw | hrest
    · exact (pointAddFieldAt_disjoint workStart 0 5 (by norm_num))
        w (by simpa [pointAddX] using hxw) v
        (by simpa [pointAddT3] using hv)
    rcases List.mem_append.mp hrest with hyw | hrest
    · exact (pointAddFieldAt_disjoint workStart 1 5 (by norm_num))
        w (by simpa [pointAddY] using hyw) v
        (by simpa [pointAddT3] using hv)
    rcases List.mem_append.mp hrest with ht0w | hrest
    · exact hT0T3 w ht0w v hv
    rcases List.mem_append.mp hrest with ht1w | hrest
    · exact hT1T3 w ht1w v hv
    rcases List.mem_append.mp hrest with ht2w | hrest
    · exact hT2T3 w ht2w v hv
    rcases List.mem_append.mp hrest with haddw | hinvw
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpAddLayout.allWires
        (pointAddT3 workStart) hT3) w haddw v hv
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpLayout.allWires
        (pointAddT3 workStart) hT3) w hinvw v hv
  have hstage1 := bennett_uncompute_after_local_update
    preparation slope preparationSupport (pointAddT3 workStart) st
    hpreparationUses hpreparationFree hpreparationWellFormed
    hpreparationT3 (by
      intro w hw
      rw [hpreparationRun]
      exact hs.2 w hw)
  dsimp only at hstage1
  let stage1 := Classical.run
    (preparation ++ slope ++ preparation.reverse) st
  change (∀ w, w ∉ pointAddT3 workStart → stage1 w = st w) ∧
    (∀ w ∈ pointAddT3 workStart,
      stage1 w = Classical.run slope
        (Classical.run preparation st) w) at hstage1
  have hstage1T3 : regValue (pointAddT3 workStart) stage1 =
      (genericSlope xR yR xC yC).val := by
    calc
      regValue (pointAddT3 workStart) stage1 =
          regValue (pointAddT3 workStart)
            (Classical.run slope (Classical.run preparation st)) := by
        apply regValue_congr
        exact hstage1.2
      _ = regValue (pointAddT3 workStart) afterSlope := by
        rw [hpreparationRun]
      _ = (genericSlope xR yR xC yC).val := hsVal

  let slopeSq := fieldMul
    (pointAddArithmeticOffset workStart)
    (pointAddT3 workStart) (pointAddT3 workStart)
    (pointAddT0 workStart)
  let afterSlopeSq := Classical.run slopeSq stage1
  have hcleanT0Stage1 := clean_of_preserved_outside
    hT0T3 hcleanT0 hstage1.1
  have hcleanMulStage1 := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT3 workStart) hT3)
    hcleanMul hstage1.1
  have hss := fieldMul_correct workStart
    (pointAddT3 workStart) (pointAddT3 workStart)
    (pointAddT0 workStart) hT3 hT3 hT0
    (by
      simpa [pointAddT0, pointAddT3] using
        pointAddFieldAt_ne workStart 2 5 (by norm_num))
    (by
      simpa [pointAddT0, pointAddT3] using
        pointAddFieldAt_ne workStart 2 5 (by norm_num))
    stage1 hcleanT0Stage1 hcleanMulStage1
    (by rw [hstage1T3]; exact (genericSlope xR yR xC yC).val_lt)
    (by rw [hstage1T3]; exact (genericSlope xR yR xC yC).val_lt)
  dsimp only at hss
  change regValue (pointAddT0 workStart) afterSlopeSq =
      regValue (pointAddT3 workStart) stage1 *
        regValue (pointAddT3 workStart) stage1 % p ∧
    ∀ w, w ∉ pointAddT0 workStart →
      afterSlopeSq w = stage1 w at hss
  have hssVal : regValue (pointAddT0 workStart) afterSlopeSq =
      (genericSlope xR yR xC yC ^ 2).val := by
    calc
      regValue (pointAddT0 workStart) afterSlopeSq =
          (genericSlope xR yR xC yC).val *
            (genericSlope xR yR xC yC).val % p := by
        simpa [hstage1T3] using hss.1
      _ = (genericSlope xR yR xC yC *
          genericSlope xR yR xC yC).val := by
        rw [ZMod.val_mul]
      _ = (genericSlope xR yR xC yC ^ 2).val := by
        rw [pow_two]

  let minusX := fieldSub
    (pointAddArithmeticOffset workStart)
    (pointAddT0 workStart) (pointAddX workStart)
    (pointAddT1 workStart)
  let afterMinusX := Classical.run minusX afterSlopeSq
  have hcleanT1Stage1 := clean_of_preserved_outside
    hT1T3 hcleanT1 hstage1.1
  have hcleanT1SS := clean_of_preserved_outside
    hT1T0 hcleanT1Stage1 hss.2
  have hcleanAddStage1 := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT3 workStart) hT3)
    hcleanAdd hstage1.1
  have hcleanAddSS := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanAddStage1 hss.2
  have hxT3 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT3 workStart) := by
    simpa [pointAddX, pointAddT3] using
      pointAddFieldAt_disjoint workStart 0 5 (by norm_num)
  have hxStage1 := regValue_of_preserved_outside hxT3 hstage1.1
  have hxSS := regValue_of_preserved_outside hXT0 hss.2
  have hmx := fieldSub_correct workStart
    (pointAddT0 workStart) (pointAddX workStart)
    (pointAddT1 workStart) hT0 hX hT1
    (by
      simpa [pointAddT1, pointAddT0] using
        pointAddFieldAt_ne workStart 3 2 (by norm_num))
    (by
      simpa [pointAddT1, pointAddX] using
        pointAddFieldAt_ne workStart 3 0 (by norm_num))
    afterSlopeSq hcleanT1SS
    (clean_fieldSubEngine_of_addEngine workStart afterSlopeSq hcleanAddSS)
    (by rw [hssVal]; exact (genericSlope xR yR xC yC ^ 2).val_lt)
    (by rw [hxSS, hxStage1, hxReg]; exact xR.val_lt)
  dsimp only at hmx
  change regValue (pointAddT1 workStart) afterMinusX =
      (regValue (pointAddT0 workStart) afterSlopeSq + p -
        regValue (pointAddX workStart) afterSlopeSq) % p ∧
    ∀ w, w ∉ pointAddT1 workStart →
      afterMinusX w = afterSlopeSq w at hmx
  have hmxVal : regValue (pointAddT1 workStart) afterMinusX =
      (genericSlope xR yR xC yC ^ 2 - xR).val := by
    calc
      regValue (pointAddT1 workStart) afterMinusX =
          ((genericSlope xR yR xC yC ^ 2).val + p - xR.val) % p := by
        simpa [hssVal, hxSS, hxStage1, hxReg] using hmx.1
      _ = (genericSlope xR yR xC yC ^ 2 - xR).val :=
        fieldSubVal _ _

  let xOut := fieldSubConst
    (pointAddArithmeticOffset workStart)
    (pointAddT1 workStart) xC.val (pointAddT2 workStart)
  let afterXOut := Classical.run xOut afterMinusX
  have hcleanT2Stage1 := clean_of_preserved_outside
    hT2T3 hcleanT2 hstage1.1
  have hcleanT2SS := clean_of_preserved_outside
    hT2T0 hcleanT2Stage1 hss.2
  have hcleanT2MX := clean_of_preserved_outside
    hT2T1 hcleanT2SS hmx.2
  have hcleanAddMX := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT1 workStart) hT1)
    hcleanAddSS hmx.2
  have hxo := fieldSubConst_correct workStart
    (pointAddT1 workStart) (pointAddT2 workStart) xC.val
    hT1 hT2 (by
      simpa [pointAddT1, pointAddT2] using
        pointAddFieldAt_ne workStart 4 3 (by norm_num))
    afterMinusX hcleanT2MX
    (clean_fieldSubEngine_of_addEngine workStart afterMinusX hcleanAddMX)
    (by rw [hmxVal]; exact
      (genericSlope xR yR xC yC ^ 2 - xR).val_lt)
    xC.val_lt
  dsimp only at hxo
  change regValue (pointAddT2 workStart) afterXOut =
      (regValue (pointAddT1 workStart) afterMinusX + p - xC.val) % p ∧
    ∀ w, w ∉ pointAddT2 workStart →
      afterXOut w = afterMinusX w at hxo
  have hxoVal : regValue (pointAddT2 workStart) afterXOut =
      (genericX xR yR xC yC).val := by
    calc
      regValue (pointAddT2 workStart) afterXOut =
          ((genericSlope xR yR xC yC ^ 2 - xR).val + p - xC.val) % p := by
        simpa [hmxVal] using hxo.1
      _ = ((genericSlope xR yR xC yC ^ 2 - xR) - xC).val :=
        fieldSubVal _ _
      _ = (genericX xR yR xC yC).val := by
        rfl

  let xPreparation := slopeSq ++ minusX
  let xPreparationSupport :=
    pointAddX workStart ++
      (pointAddT0 workStart ++
        (pointAddT1 workStart ++
          (pointAddT3 workStart ++
            (shiftWires (pointAddArithmeticOffset workStart)
                  Secp256k1Instance.secpAddLayout.allWires ++
              shiftWires (pointAddArithmeticOffset workStart)
                Secp256k1Instance.secpMulLayout.allWires))))
  have hxPreparationRun :
      Classical.run xPreparation stage1 = afterMinusX := by
    simp [xPreparation, minusX, afterMinusX, slopeSq, afterSlopeSq,
      Classical.run_append]
  have hxPreparationUses :
      CircuitUsesOnly xPreparationSupport xPreparation := by
    apply usesOnly_append
    · apply usesOnly_mono
        (fieldMul_usesOnly (pointAddArithmeticOffset workStart)
          (pointAddT3 workStart) (pointAddT3 workStart)
          (pointAddT0 workStart))
      intro w hw
      rcases List.mem_append.mp hw with hprefix | hmul
      · rcases List.mem_append.mp hprefix with hpair | ht0w
        · rcases List.mem_append.mp hpair with ht3w | ht3w
          · simp only [xPreparationSupport, List.mem_append]
            exact Or.inr (Or.inr (Or.inr (Or.inl ht3w)))
          · simp only [xPreparationSupport, List.mem_append]
            exact Or.inr (Or.inr (Or.inr (Or.inl ht3w)))
        · simp only [xPreparationSupport, List.mem_append]
          exact Or.inr (Or.inl ht0w)
      · simp only [xPreparationSupport, List.mem_append]
        exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr hmul))))
    · apply usesOnly_mono
        (fieldSub_usesOnly (pointAddArithmeticOffset workStart)
          (pointAddT0 workStart) (pointAddX workStart)
          (pointAddT1 workStart))
      intro w hw
      rcases List.mem_append.mp hw with hprefix | hadd
      · rcases List.mem_append.mp hprefix with hpair | ht1w
        · rcases List.mem_append.mp hpair with ht0w | hxw
          · simp only [xPreparationSupport, List.mem_append]
            exact Or.inr (Or.inl ht0w)
          · simp only [xPreparationSupport, List.mem_append]
            exact Or.inl hxw
        · simp only [xPreparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inl ht1w))
      · simp only [xPreparationSupport, List.mem_append]
        exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hadd))))
  have hxPreparationFree : Classical.HPFree xPreparation := by
    simp [xPreparation, slopeSq, minusX,
      fieldMul_HPFree, fieldSub_HPFree]
  have hxPreparationWellFormed : CircuitWellFormed xPreparation := by
    simp [xPreparation, slopeSq, minusX,
      fieldMul_wellFormed, fieldSub_wellFormed,
      IsPointAddFieldRegister]
  have hxPreparationT2 : ModExp.Schedule.WireDisjoint
      xPreparationSupport (pointAddT2 workStart) := by
    intro w hw v hv
    dsimp only [xPreparationSupport] at hw
    rcases List.mem_append.mp hw with hxw | hrest
    · exact (pointAddFieldAt_disjoint workStart 0 4 (by norm_num))
        w (by simpa [pointAddX] using hxw) v
        (by simpa [pointAddT2] using hv)
    rcases List.mem_append.mp hrest with ht0w | hrest
    · exact hT0T2 w ht0w v hv
    rcases List.mem_append.mp hrest with ht1w | hrest
    · exact hT1T2 w ht1w v hv
    rcases List.mem_append.mp hrest with ht3w | hrest
    · exact hT3T2 w ht3w v hv
    rcases List.mem_append.mp hrest with haddw | hmulw
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpAddLayout.allWires
        (pointAddT2 workStart) hT2) w haddw v hv
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpMulLayout.allWires
        (pointAddT2 workStart) hT2) w hmulw v hv
  have hstage2 := bennett_uncompute_after_local_update
    xPreparation xOut xPreparationSupport (pointAddT2 workStart)
    stage1 hxPreparationUses hxPreparationFree
    hxPreparationWellFormed hxPreparationT2 (by
      intro w hw
      rw [hxPreparationRun]
      exact hxo.2 w hw)
  dsimp only at hstage2
  let stage2 := Classical.run
    (xPreparation ++ xOut ++ xPreparation.reverse) stage1
  change (∀ w, w ∉ pointAddT2 workStart → stage2 w = stage1 w) ∧
    (∀ w ∈ pointAddT2 workStart,
      stage2 w = Classical.run xOut
        (Classical.run xPreparation stage1) w) at hstage2
  have hstage2T2 : regValue (pointAddT2 workStart) stage2 =
      (genericX xR yR xC yC).val := by
    calc
      regValue (pointAddT2 workStart) stage2 =
          regValue (pointAddT2 workStart)
            (Classical.run xOut
              (Classical.run xPreparation stage1)) := by
        apply regValue_congr
        exact hstage2.2
      _ = regValue (pointAddT2 workStart) afterXOut := by
        rw [hxPreparationRun]
      _ = (genericX xR yR xC yC).val := hxoVal

  let xDifference := fieldSub
    (pointAddArithmeticOffset workStart)
    (pointAddX workStart) (pointAddT2 workStart)
    (pointAddT0 workStart)
  let afterXDifference := Classical.run xDifference stage2
  have hcleanT0Stage2 := clean_of_preserved_outside
    hT0T2 hcleanT0Stage1 hstage2.1
  have hcleanAddStage2 := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT2 workStart) hT2)
    hcleanAddStage1 hstage2.1
  have hxStage2 := regValue_of_preserved_outside hXT2 hstage2.1
  have hxd := fieldSub_correct workStart
    (pointAddX workStart) (pointAddT2 workStart)
    (pointAddT0 workStart) hX hT2 hT0
    (by
      simpa [pointAddT0, pointAddX] using
        pointAddFieldAt_ne workStart 2 0 (by norm_num))
    (by
      simpa [pointAddT0, pointAddT2] using
        pointAddFieldAt_ne workStart 2 4 (by norm_num))
    stage2 hcleanT0Stage2
    (clean_fieldSubEngine_of_addEngine workStart stage2 hcleanAddStage2)
    (by rw [hxStage2, hxStage1, hxReg]; exact xR.val_lt)
    (by rw [hstage2T2]; exact (genericX xR yR xC yC).val_lt)
  dsimp only at hxd
  change regValue (pointAddT0 workStart) afterXDifference =
      (regValue (pointAddX workStart) stage2 + p -
        regValue (pointAddT2 workStart) stage2) % p ∧
    ∀ w, w ∉ pointAddT0 workStart →
      afterXDifference w = stage2 w at hxd
  have hxdVal : regValue (pointAddT0 workStart) afterXDifference =
      (xR - genericX xR yR xC yC).val := by
    calc
      regValue (pointAddT0 workStart) afterXDifference =
          (xR.val + p - (genericX xR yR xC yC).val) % p := by
        simpa [hxStage2, hxStage1, hxReg, hstage2T2] using hxd.1
      _ = (xR - genericX xR yR xC yC).val := fieldSubVal _ _

  let yProduct := fieldMul
    (pointAddArithmeticOffset workStart)
    (pointAddT3 workStart) (pointAddT0 workStart)
    (pointAddT1 workStart)
  let afterYProduct := Classical.run yProduct afterXDifference
  have hcleanT1Stage2 := clean_of_preserved_outside
    hT1T2 hcleanT1Stage1 hstage2.1
  have hcleanT1XD := clean_of_preserved_outside
    hT1T0 hcleanT1Stage2 hxd.2
  have hcleanMulStage2 := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT2 workStart) hT2)
    hcleanMulStage1 hstage2.1
  have hcleanMulXD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanMulStage2 hxd.2
  have ht3Stage2 := regValue_of_preserved_outside hT3T2 hstage2.1
  have ht3XD := regValue_of_preserved_outside hT3T0 hxd.2
  have hyp := fieldMul_correct workStart
    (pointAddT3 workStart) (pointAddT0 workStart)
    (pointAddT1 workStart) hT3 hT0 hT1
    (by
      simpa [pointAddT1, pointAddT3] using
        pointAddFieldAt_ne workStart 3 5 (by norm_num))
    (by
      simpa [pointAddT1, pointAddT0] using
        pointAddFieldAt_ne workStart 3 2 (by norm_num))
    afterXDifference hcleanT1XD hcleanMulXD
    (by rw [ht3XD, ht3Stage2, hstage1T3]; exact
      (genericSlope xR yR xC yC).val_lt)
    (by rw [hxdVal]; exact
      (xR - genericX xR yR xC yC).val_lt)
  dsimp only at hyp
  change regValue (pointAddT1 workStart) afterYProduct =
      regValue (pointAddT3 workStart) afterXDifference *
        regValue (pointAddT0 workStart) afterXDifference % p ∧
    ∀ w, w ∉ pointAddT1 workStart →
      afterYProduct w = afterXDifference w at hyp
  have hypVal : regValue (pointAddT1 workStart) afterYProduct =
      (genericSlope xR yR xC yC *
        (xR - genericX xR yR xC yC)).val := by
    calc
      regValue (pointAddT1 workStart) afterYProduct =
          (genericSlope xR yR xC yC).val *
            (xR - genericX xR yR xC yC).val % p := by
        simpa [ht3XD, ht3Stage2, hstage1T3, hxdVal] using hyp.1
      _ = (genericSlope xR yR xC yC *
          (xR - genericX xR yR xC yC)).val := by
        rw [ZMod.val_mul]

  let yOut := fieldSub
    (pointAddArithmeticOffset workStart)
    (pointAddT1 workStart) (pointAddY workStart)
    (pointAddT4 workStart)
  let afterYOut := Classical.run yOut afterYProduct
  have hcleanT4Stage1 := clean_of_preserved_outside
    hT4T3 hcleanT4 hstage1.1
  have hcleanT4Stage2 := clean_of_preserved_outside
    hT4T2 hcleanT4Stage1 hstage2.1
  have hcleanT4XD := clean_of_preserved_outside
    hT4T0 hcleanT4Stage2 hxd.2
  have hcleanT4YP := clean_of_preserved_outside
    hT4T1 hcleanT4XD hyp.2
  have hcleanAddXD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanAddStage2 hxd.2
  have hcleanAddYP := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT1 workStart) hT1)
    hcleanAddXD hyp.2
  have hyT3 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT3 workStart) := by
    simpa [pointAddY, pointAddT3] using
      pointAddFieldAt_disjoint workStart 1 5 (by norm_num)
  have hyStage1 := regValue_of_preserved_outside hyT3 hstage1.1
  have hyStage2 := regValue_of_preserved_outside hYT2 hstage2.1
  have hyXD := regValue_of_preserved_outside hYT0 hxd.2
  have hyYP := regValue_of_preserved_outside hYT1 hyp.2
  have hyo := fieldSub_correct workStart
    (pointAddT1 workStart) (pointAddY workStart)
    (pointAddT4 workStart) hT1 hY hT4
    (by
      simpa [pointAddT4, pointAddT1] using
        pointAddFieldAt_ne workStart 6 3 (by norm_num))
    (by
      simpa [pointAddT4, pointAddY] using
        pointAddFieldAt_ne workStart 6 1 (by norm_num))
    afterYProduct hcleanT4YP
    (clean_fieldSubEngine_of_addEngine workStart afterYProduct hcleanAddYP)
    (by rw [hypVal]; exact
      (genericSlope xR yR xC yC *
        (xR - genericX xR yR xC yC)).val_lt)
    (by rw [hyYP, hyXD, hyStage2, hyStage1, hyReg]; exact yR.val_lt)
  dsimp only at hyo
  change regValue (pointAddT4 workStart) afterYOut =
      (regValue (pointAddT1 workStart) afterYProduct + p -
        regValue (pointAddY workStart) afterYProduct) % p ∧
    ∀ w, w ∉ pointAddT4 workStart →
      afterYOut w = afterYProduct w at hyo
  have hyoVal : regValue (pointAddT4 workStart) afterYOut =
      (genericY xR yR xC yC).val := by
    calc
      regValue (pointAddT4 workStart) afterYOut =
          ((genericSlope xR yR xC yC *
              (xR - genericX xR yR xC yC)).val + p - yR.val) % p := by
        simpa [hypVal, hyYP, hyXD, hyStage2, hyStage1, hyReg] using hyo.1
      _ = (genericSlope xR yR xC yC *
          (xR - genericX xR yR xC yC) - yR).val :=
        fieldSubVal _ _
      _ = (genericY xR yR xC yC).val := by
        rfl
  have ht2XD := regValue_of_preserved_outside hT2T0 hxd.2
  have ht2YP := regValue_of_preserved_outside hT2T1 hyp.2
  have ht2YO := regValue_of_preserved_outside hT2T4 hyo.2
  have hfinalT2 : regValue (pointAddT2 workStart) afterYOut =
      (genericX xR yR xC yC).val := by
    rw [ht2YO, ht2YP, ht2XD, hstage2T2]
  have hcleanCandidateStage1 := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT3 workStart) hT3)
    hcleanCandidate hstage1.1
  have hcleanCandidateStage2 := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT2 workStart) hT2)
    hcleanCandidateStage1 hstage2.1
  have hcleanCandidateXD := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT0 workStart) hT0)
    hcleanCandidateStage2 hxd.2
  have hcleanCandidateYP := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT1 workStart) hT1)
    hcleanCandidateXD hyp.2
  have hcleanCandidateYO := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT4 workStart) hT4)
    hcleanCandidateYP hyo.2
  have hgenericRun :
      Classical.run (genericPointCompute workStart xC yC) st = afterYOut := by
    simp [genericPointCompute, preparation, xPreparation,
      stage1, stage2, numerator, denominator, inverse, slope,
      slopeSq, minusX, xOut, xDifference, yProduct, yOut,
      afterXDifference, afterYProduct, afterYOut, Classical.run_append,
      List.reverse_append, List.append_assoc]
  dsimp only
  rw [hgenericRun]
  exact ⟨hfinalT2, hyoVal, hcleanCandidateYO⟩

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 300 in
private theorem doublePointCompute_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire) (xR yR : Fp)
    (hy : yR ≠ -yR)
    (st : BasisState)
    (hxReg : regValue (pointAddX workStart) st = xR.val)
    (hyReg : regValue (pointAddY workStart) st = yR.val)
    (hclean : Clean (pointAddBranchWork workStart) st) :
    let after := Classical.run (doublePointCompute workStart) st
    regValue (pointAddT2 workStart) after =
        (doubleX xR yR).val ∧
      regValue (pointAddT4 workStart) after =
        (doubleY xR yR).val ∧
      Clean (pointAddCandidate workStart) after := by
  have hX : IsPointAddFieldRegister workStart
      (pointAddX workStart) := by
    simp [IsPointAddFieldRegister]
  have hY : IsPointAddFieldRegister workStart
      (pointAddY workStart) := by
    simp [IsPointAddFieldRegister]
  have hT0 : IsPointAddFieldRegister workStart
      (pointAddT0 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT1 : IsPointAddFieldRegister workStart
      (pointAddT1 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT2 : IsPointAddFieldRegister workStart
      (pointAddT2 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT3 : IsPointAddFieldRegister workStart
      (pointAddT3 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT4 : IsPointAddFieldRegister workStart
      (pointAddT4 workStart) := by
    simp [IsPointAddFieldRegister]
  have hT0T1 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT0, pointAddT1] using
      pointAddFieldAt_disjoint workStart 2 3 (by norm_num)
  have hT0T2 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT0, pointAddT2] using
      pointAddFieldAt_disjoint workStart 2 4 (by norm_num)
  have hT0T3 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT3 workStart) := by
    simpa [pointAddT0, pointAddT3] using
      pointAddFieldAt_disjoint workStart 2 5 (by norm_num)
  have hT0T4 : ModExp.Schedule.WireDisjoint
      (pointAddT0 workStart) (pointAddT4 workStart) := by
    simpa [pointAddT0, pointAddT4] using
      pointAddFieldAt_disjoint workStart 2 6 (by norm_num)
  have hT1T0 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT1, pointAddT0] using
      pointAddFieldAt_disjoint workStart 3 2 (by norm_num)
  have hT1T2 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT1, pointAddT2] using
      pointAddFieldAt_disjoint workStart 3 4 (by norm_num)
  have hT1T3 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT3 workStart) := by
    simpa [pointAddT1, pointAddT3] using
      pointAddFieldAt_disjoint workStart 3 5 (by norm_num)
  have hT1T4 : ModExp.Schedule.WireDisjoint
      (pointAddT1 workStart) (pointAddT4 workStart) := by
    simpa [pointAddT1, pointAddT4] using
      pointAddFieldAt_disjoint workStart 3 6 (by norm_num)
  have hT2T0 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT2, pointAddT0] using
      pointAddFieldAt_disjoint workStart 4 2 (by norm_num)
  have hT2T1 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT2, pointAddT1] using
      pointAddFieldAt_disjoint workStart 4 3 (by norm_num)
  have hT2T3 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT3 workStart) := by
    simpa [pointAddT2, pointAddT3] using
      pointAddFieldAt_disjoint workStart 4 5 (by norm_num)
  have hT2T4 : ModExp.Schedule.WireDisjoint
      (pointAddT2 workStart) (pointAddT4 workStart) := by
    simpa [pointAddT2, pointAddT4] using
      pointAddFieldAt_disjoint workStart 4 6 (by norm_num)
  have hT3T0 : ModExp.Schedule.WireDisjoint
      (pointAddT3 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT3, pointAddT0] using
      pointAddFieldAt_disjoint workStart 5 2 (by norm_num)
  have hT3T1 : ModExp.Schedule.WireDisjoint
      (pointAddT3 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT3, pointAddT1] using
      pointAddFieldAt_disjoint workStart 5 3 (by norm_num)
  have hT3T2 : ModExp.Schedule.WireDisjoint
      (pointAddT3 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT3, pointAddT2] using
      pointAddFieldAt_disjoint workStart 5 4 (by norm_num)
  have hT4T0 : ModExp.Schedule.WireDisjoint
      (pointAddT4 workStart) (pointAddT0 workStart) := by
    simpa [pointAddT4, pointAddT0] using
      pointAddFieldAt_disjoint workStart 6 2 (by norm_num)
  have hT4T1 : ModExp.Schedule.WireDisjoint
      (pointAddT4 workStart) (pointAddT1 workStart) := by
    simpa [pointAddT4, pointAddT1] using
      pointAddFieldAt_disjoint workStart 6 3 (by norm_num)
  have hT4T2 : ModExp.Schedule.WireDisjoint
      (pointAddT4 workStart) (pointAddT2 workStart) := by
    simpa [pointAddT4, pointAddT2] using
      pointAddFieldAt_disjoint workStart 6 4 (by norm_num)
  have hT4T3 : ModExp.Schedule.WireDisjoint
      (pointAddT4 workStart) (pointAddT3 workStart) := by
    simpa [pointAddT4, pointAddT3] using
      pointAddFieldAt_disjoint workStart 6 5 (by norm_num)
  have hXT0 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT0 workStart) := by
    simpa [pointAddX, pointAddT0] using
      pointAddFieldAt_disjoint workStart 0 2 (by norm_num)
  have hXT1 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT1 workStart) := by
    simpa [pointAddX, pointAddT1] using
      pointAddFieldAt_disjoint workStart 0 3 (by norm_num)
  have hXT2 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT2 workStart) := by
    simpa [pointAddX, pointAddT2] using
      pointAddFieldAt_disjoint workStart 0 4 (by norm_num)
  have hYT0 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT0 workStart) := by
    simpa [pointAddY, pointAddT0] using
      pointAddFieldAt_disjoint workStart 1 2 (by norm_num)
  have hYT1 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT1 workStart) := by
    simpa [pointAddY, pointAddT1] using
      pointAddFieldAt_disjoint workStart 1 3 (by norm_num)
  have hYT2 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT2 workStart) := by
    simpa [pointAddY, pointAddT2] using
      pointAddFieldAt_disjoint workStart 1 4 (by norm_num)
  have hYT4 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT4 workStart) := by
    simpa [pointAddY, pointAddT4] using
      pointAddFieldAt_disjoint workStart 1 6 (by norm_num)
  have hcleanT0 : Clean (pointAddT0 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT1 : Clean (pointAddT1 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT2 : Clean (pointAddT2 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT3 : Clean (pointAddT3 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanT4 : Clean (pointAddT4 workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanCandidate : Clean (pointAddCandidate workStart) st := by
    intro w hw
    exact hclean w (by simp [pointAddBranchWork, hw])
  have hcleanAdd := cleanAddEngine_of_branchWork workStart st hclean
  have hcleanMul := cleanMulEngine_of_branchWork workStart st hclean
  have hcleanInv := cleanInvEngine_of_branchWork workStart st hclean

  let numerator := threeXSquared
    (pointAddArithmeticOffset workStart)
    (pointAddX workStart) (pointAddT0 workStart)
    (pointAddT1 workStart) (pointAddT2 workStart)
  let afterNumerator := Classical.run numerator st
  have hn := threeXSquared_correct workStart xR st hxReg hclean
  dsimp only at hn
  change regValue (pointAddT2 workStart) afterNumerator =
      (doubleNumerator xR).val ∧
    ∀ w, w ∉ pointAddT2 workStart →
      afterNumerator w = st w at hn

  let denominator := fieldAdd
    (pointAddArithmeticOffset workStart)
    (pointAddY workStart) (pointAddY workStart)
    (pointAddT0 workStart)
  let afterDenominator := Classical.run denominator afterNumerator
  have hcleanT0N := clean_of_preserved_outside
    hT0T2 hcleanT0 hn.2
  have hcleanAddN := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT2 workStart) hT2)
    hcleanAdd hn.2
  have hyN := regValue_of_preserved_outside hYT2 hn.2
  have hd := fieldAdd_correct workStart
    (pointAddY workStart) (pointAddY workStart)
    (pointAddT0 workStart) hY hY hT0
    (by
      simpa [pointAddT0, pointAddY] using
        pointAddFieldAt_ne workStart 2 1 (by norm_num))
    (by
      simpa [pointAddT0, pointAddY] using
        pointAddFieldAt_ne workStart 2 1 (by norm_num))
    afterNumerator hcleanT0N hcleanAddN
    (by rw [hyN, hyReg]; exact yR.val_lt)
    (by rw [hyN, hyReg]; exact yR.val_lt)
  dsimp only at hd
  change regValue (pointAddT0 workStart) afterDenominator =
      (regValue (pointAddY workStart) afterNumerator +
        regValue (pointAddY workStart) afterNumerator) % p ∧
    ∀ w, w ∉ pointAddT0 workStart →
      afterDenominator w = afterNumerator w at hd
  have hdVal : regValue (pointAddT0 workStart) afterDenominator =
      (doubleDenominator yR).val := by
    rw [hd.1, hyN, hyReg, ← ZMod.val_add]
    simp [doubleDenominator, two_mul]

  let inverse := fieldInv
    (pointAddArithmeticOffset workStart)
    (pointAddT0 workStart) (pointAddT1 workStart)
  let afterInverse := Classical.run inverse afterDenominator
  have hcleanT1N := clean_of_preserved_outside
    hT1T2 hcleanT1 hn.2
  have hcleanT1D := clean_of_preserved_outside
    hT1T0 hcleanT1N hd.2
  have hcleanInvN := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpLayout.allWires
      (pointAddT2 workStart) hT2)
    hcleanInv hn.2
  have hcleanInvD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanInvN hd.2
  have hdenNonzero :
      ((regValue (pointAddT0 workStart) afterDenominator : Nat) : Fp) ≠ 0 := by
    rw [hdVal, ZMod.natCast_zmod_val]
    exact doubleDenominator_ne_zero hy
  have hi := fieldInv_correct workStart
    (pointAddT0 workStart) (pointAddT1 workStart)
    hT0 hT1 (by
      simpa [pointAddT0, pointAddT1] using
        pointAddFieldAt_ne workStart 3 2 (by norm_num))
    afterDenominator hcleanT1D hcleanInvD
    (by rw [hdVal]; exact (doubleDenominator yR).val_lt)
    hdenNonzero
  dsimp only at hi
  change regValue (pointAddT1 workStart) afterInverse =
      (((regValue (pointAddT0 workStart) afterDenominator : Nat) : Fp)⁻¹).val ∧
    ∀ w, w ∉ pointAddT1 workStart →
      afterInverse w = afterDenominator w at hi
  have hiVal : regValue (pointAddT1 workStart) afterInverse =
      (doubleDenominator yR)⁻¹.val := by
    simpa [hdVal, ZMod.natCast_zmod_val] using hi.1

  let slope := fieldMul
    (pointAddArithmeticOffset workStart)
    (pointAddT2 workStart) (pointAddT1 workStart)
    (pointAddT3 workStart)
  let afterSlope := Classical.run slope afterInverse
  have hcleanT3N := clean_of_preserved_outside
    hT3T2 hcleanT3 hn.2
  have hcleanT3D := clean_of_preserved_outside
    hT3T0 hcleanT3N hd.2
  have hcleanT3I := clean_of_preserved_outside
    hT3T1 hcleanT3D hi.2
  have hcleanMulN := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT2 workStart) hT2)
    hcleanMul hn.2
  have hcleanMulD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanMulN hd.2
  have hcleanMulI := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT1 workStart) hT1)
    hcleanMulD hi.2
  have hnD := regValue_of_preserved_outside hT2T0 hd.2
  have hnI := regValue_of_preserved_outside hT2T1 hi.2
  have ht2I : regValue (pointAddT2 workStart) afterInverse =
      (doubleNumerator xR).val := by
    rw [hnI, hnD, hn.1]
  have hs := fieldMul_correct workStart
    (pointAddT2 workStart) (pointAddT1 workStart)
    (pointAddT3 workStart) hT2 hT1 hT3
    (by
      simpa [pointAddT3, pointAddT2] using
        pointAddFieldAt_ne workStart 5 4 (by norm_num))
    (by
      simpa [pointAddT3, pointAddT1] using
        pointAddFieldAt_ne workStart 5 3 (by norm_num))
    afterInverse hcleanT3I hcleanMulI
    (by rw [ht2I]; exact (doubleNumerator xR).val_lt)
    (by rw [hiVal]; exact (doubleDenominator yR)⁻¹.val_lt)
  dsimp only at hs
  change regValue (pointAddT3 workStart) afterSlope =
      regValue (pointAddT2 workStart) afterInverse *
        regValue (pointAddT1 workStart) afterInverse % p ∧
    ∀ w, w ∉ pointAddT3 workStart →
      afterSlope w = afterInverse w at hs
  have hsVal : regValue (pointAddT3 workStart) afterSlope =
      (doubleSlope xR yR).val := by
    calc
      regValue (pointAddT3 workStart) afterSlope =
          (doubleNumerator xR).val *
            (doubleDenominator yR)⁻¹.val % p := by
        simpa [ht2I, hiVal] using hs.1
      _ = (doubleNumerator xR *
          (doubleDenominator yR)⁻¹).val := by
        rw [ZMod.val_mul]
      _ = (doubleSlope xR yR).val := by
        rfl

  let preparation := numerator ++ denominator ++ inverse
  let preparationSupport :=
    pointAddX workStart ++
      (pointAddY workStart ++
        (pointAddT0 workStart ++
          (pointAddT1 workStart ++
            (pointAddT2 workStart ++
              (shiftWires (pointAddArithmeticOffset workStart)
                    Secp256k1Instance.secpAddLayout.allWires ++
                (shiftWires (pointAddArithmeticOffset workStart)
                      Secp256k1Instance.secpMulLayout.allWires ++
                  shiftWires (pointAddArithmeticOffset workStart)
                    Secp256k1Instance.secpLayout.allWires))))))
  have hpreparationRun :
      Classical.run preparation st = afterInverse := by
    simp [preparation, inverse, afterInverse, denominator,
      afterDenominator, numerator, afterNumerator,
      Classical.run_append]
  have hpreparationUses :
      CircuitUsesOnly preparationSupport preparation := by
    apply usesOnly_append
    · apply usesOnly_append
      · apply usesOnly_mono
          (threeXSquared_usesOnly_exact
            (pointAddArithmeticOffset workStart)
            (pointAddX workStart) (pointAddT0 workStart)
            (pointAddT1 workStart) (pointAddT2 workStart))
        intro w hw
        rcases List.mem_append.mp hw with hprefix | hmulw
        · rcases List.mem_append.mp hprefix with hprefix | haddw
          · rcases List.mem_append.mp hprefix with hprefix | ht2w
            · rcases List.mem_append.mp hprefix with hprefix | ht1w
              · rcases List.mem_append.mp hprefix with hxw | ht0w
                · simp only [preparationSupport, List.mem_append]
                  exact Or.inl hxw
                · simp only [preparationSupport, List.mem_append]
                  exact Or.inr (Or.inr (Or.inl ht0w))
              · simp only [preparationSupport, List.mem_append]
                exact Or.inr (Or.inr (Or.inr (Or.inl ht1w)))
            · simp only [preparationSupport, List.mem_append]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht2w))))
          · simp only [preparationSupport, List.mem_append]
            exact Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl haddw)))))
        · simp only [preparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inl hmulw))))))
      · apply usesOnly_mono
          (fieldAdd_usesOnly
            (pointAddArithmeticOffset workStart)
            (pointAddY workStart) (pointAddY workStart)
            (pointAddT0 workStart))
        intro w hw
        rcases List.mem_append.mp hw with hprefix | haddw
        · rcases List.mem_append.mp hprefix with hpair | ht0w
          · rcases List.mem_append.mp hpair with hyw | hyw
            · simp only [preparationSupport, List.mem_append]
              exact Or.inr (Or.inl hyw)
            · simp only [preparationSupport, List.mem_append]
              exact Or.inr (Or.inl hyw)
          · simp only [preparationSupport, List.mem_append]
            exact Or.inr (Or.inr (Or.inl ht0w))
        · simp only [preparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl haddw)))))
    · apply usesOnly_mono
        (fieldInv_usesOnly
          (pointAddArithmeticOffset workStart)
          (pointAddT0 workStart) (pointAddT1 workStart))
      intro w hw
      rcases List.mem_append.mp hw with hpair | hinvw
      · rcases List.mem_append.mp hpair with ht0w | ht1w
        · simp only [preparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inl ht0w))
        · simp only [preparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inr (Or.inl ht1w)))
      · simp only [preparationSupport, List.mem_append]
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr hinvw))))))
  have hpreparationFree : Classical.HPFree preparation := by
    simp [preparation, numerator, denominator, inverse,
      threeXSquared_HPFree, fieldAdd_HPFree, fieldInv_HPFree]
  have hpreparationWellFormed : CircuitWellFormed preparation := by
    simp [preparation, numerator, denominator, inverse,
      threeXSquared_wellFormed, fieldAdd_wellFormed,
      fieldInv_wellFormed, IsPointAddFieldRegister]
  have hpreparationT3 : ModExp.Schedule.WireDisjoint
      preparationSupport (pointAddT3 workStart) := by
    intro w hw v hv
    dsimp only [preparationSupport] at hw
    rcases List.mem_append.mp hw with hxw | hrest
    · exact (pointAddFieldAt_disjoint workStart 0 5 (by norm_num))
        w (by simpa [pointAddX] using hxw) v
        (by simpa [pointAddT3] using hv)
    rcases List.mem_append.mp hrest with hyw | hrest
    · exact (pointAddFieldAt_disjoint workStart 1 5 (by norm_num))
        w (by simpa [pointAddY] using hyw) v
        (by simpa [pointAddT3] using hv)
    rcases List.mem_append.mp hrest with ht0w | hrest
    · exact hT0T3 w ht0w v hv
    rcases List.mem_append.mp hrest with ht1w | hrest
    · exact hT1T3 w ht1w v hv
    rcases List.mem_append.mp hrest with ht2w | hrest
    · exact hT2T3 w ht2w v hv
    rcases List.mem_append.mp hrest with haddw | hrest
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpAddLayout.allWires
        (pointAddT3 workStart) hT3) w haddw v hv
    rcases List.mem_append.mp hrest with hmulw | hinvw
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpMulLayout.allWires
        (pointAddT3 workStart) hT3) w hmulw v hv
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpLayout.allWires
        (pointAddT3 workStart) hT3) w hinvw v hv
  have hstage1 := bennett_uncompute_after_local_update
    preparation slope preparationSupport (pointAddT3 workStart) st
    hpreparationUses hpreparationFree hpreparationWellFormed
    hpreparationT3 (by
      intro w hw
      rw [hpreparationRun]
      exact hs.2 w hw)
  dsimp only at hstage1
  let stage1 := Classical.run
    (preparation ++ slope ++ preparation.reverse) st
  change (∀ w, w ∉ pointAddT3 workStart → stage1 w = st w) ∧
    (∀ w ∈ pointAddT3 workStart,
      stage1 w = Classical.run slope
        (Classical.run preparation st) w) at hstage1
  have hstage1T3 : regValue (pointAddT3 workStart) stage1 =
      (doubleSlope xR yR).val := by
    calc
      regValue (pointAddT3 workStart) stage1 =
          regValue (pointAddT3 workStart)
            (Classical.run slope (Classical.run preparation st)) := by
        apply regValue_congr
        exact hstage1.2
      _ = regValue (pointAddT3 workStart) afterSlope := by
        rw [hpreparationRun]
      _ = (doubleSlope xR yR).val := hsVal

  let slopeSq := fieldMul
    (pointAddArithmeticOffset workStart)
    (pointAddT3 workStart) (pointAddT3 workStart)
    (pointAddT0 workStart)
  let afterSlopeSq := Classical.run slopeSq stage1
  have hcleanT0Stage1 := clean_of_preserved_outside
    hT0T3 hcleanT0 hstage1.1
  have hcleanMulStage1 := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT3 workStart) hT3)
    hcleanMul hstage1.1
  have hss := fieldMul_correct workStart
    (pointAddT3 workStart) (pointAddT3 workStart)
    (pointAddT0 workStart) hT3 hT3 hT0
    (by
      simpa [pointAddT0, pointAddT3] using
        pointAddFieldAt_ne workStart 2 5 (by norm_num))
    (by
      simpa [pointAddT0, pointAddT3] using
        pointAddFieldAt_ne workStart 2 5 (by norm_num))
    stage1 hcleanT0Stage1 hcleanMulStage1
    (by rw [hstage1T3]; exact (doubleSlope xR yR).val_lt)
    (by rw [hstage1T3]; exact (doubleSlope xR yR).val_lt)
  dsimp only at hss
  change regValue (pointAddT0 workStart) afterSlopeSq =
      regValue (pointAddT3 workStart) stage1 *
        regValue (pointAddT3 workStart) stage1 % p ∧
    ∀ w, w ∉ pointAddT0 workStart →
      afterSlopeSq w = stage1 w at hss
  have hssVal : regValue (pointAddT0 workStart) afterSlopeSq =
      (doubleSlope xR yR ^ 2).val := by
    calc
      regValue (pointAddT0 workStart) afterSlopeSq =
          (doubleSlope xR yR).val *
            (doubleSlope xR yR).val % p := by
        simpa [hstage1T3] using hss.1
      _ = (doubleSlope xR yR * doubleSlope xR yR).val := by
        rw [ZMod.val_mul]
      _ = (doubleSlope xR yR ^ 2).val := by
        rw [pow_two]

  let twoX := fieldAdd
    (pointAddArithmeticOffset workStart)
    (pointAddX workStart) (pointAddX workStart)
    (pointAddT1 workStart)
  let afterTwoX := Classical.run twoX afterSlopeSq
  have hcleanT1Stage1 := clean_of_preserved_outside
    hT1T3 hcleanT1 hstage1.1
  have hcleanT1SS := clean_of_preserved_outside
    hT1T0 hcleanT1Stage1 hss.2
  have hcleanAddStage1 := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT3 workStart) hT3)
    hcleanAdd hstage1.1
  have hcleanAddSS := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanAddStage1 hss.2
  have hxT3 : ModExp.Schedule.WireDisjoint
      (pointAddX workStart) (pointAddT3 workStart) := by
    simpa [pointAddX, pointAddT3] using
      pointAddFieldAt_disjoint workStart 0 5 (by norm_num)
  have hxStage1 := regValue_of_preserved_outside hxT3 hstage1.1
  have hxSS := regValue_of_preserved_outside hXT0 hss.2
  have htx := fieldAdd_correct workStart
    (pointAddX workStart) (pointAddX workStart)
    (pointAddT1 workStart) hX hX hT1
    (by
      simpa [pointAddT1, pointAddX] using
        pointAddFieldAt_ne workStart 3 0 (by norm_num))
    (by
      simpa [pointAddT1, pointAddX] using
        pointAddFieldAt_ne workStart 3 0 (by norm_num))
    afterSlopeSq hcleanT1SS hcleanAddSS
    (by rw [hxSS, hxStage1, hxReg]; exact xR.val_lt)
    (by rw [hxSS, hxStage1, hxReg]; exact xR.val_lt)
  dsimp only at htx
  change regValue (pointAddT1 workStart) afterTwoX =
      (regValue (pointAddX workStart) afterSlopeSq +
        regValue (pointAddX workStart) afterSlopeSq) % p ∧
    ∀ w, w ∉ pointAddT1 workStart →
      afterTwoX w = afterSlopeSq w at htx
  have htxVal : regValue (pointAddT1 workStart) afterTwoX =
      (2 * xR).val := by
    rw [htx.1, hxSS, hxStage1, hxReg, ← ZMod.val_add, two_mul]
  have ht0TX := regValue_of_preserved_outside hT0T1 htx.2

  let xOut := fieldSub
    (pointAddArithmeticOffset workStart)
    (pointAddT0 workStart) (pointAddT1 workStart)
    (pointAddT2 workStart)
  let afterXOut := Classical.run xOut afterTwoX
  have hcleanT2Stage1 := clean_of_preserved_outside
    hT2T3 hcleanT2 hstage1.1
  have hcleanT2SS := clean_of_preserved_outside
    hT2T0 hcleanT2Stage1 hss.2
  have hcleanT2TX := clean_of_preserved_outside
    hT2T1 hcleanT2SS htx.2
  have hcleanAddTX := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT1 workStart) hT1)
    hcleanAddSS htx.2
  have hxo := fieldSub_correct workStart
    (pointAddT0 workStart) (pointAddT1 workStart)
    (pointAddT2 workStart) hT0 hT1 hT2
    (by
      simpa [pointAddT2, pointAddT0] using
        pointAddFieldAt_ne workStart 4 2 (by norm_num))
    (by
      simpa [pointAddT2, pointAddT1] using
        pointAddFieldAt_ne workStart 4 3 (by norm_num))
    afterTwoX hcleanT2TX
    (clean_fieldSubEngine_of_addEngine workStart afterTwoX hcleanAddTX)
    (by rw [ht0TX, hssVal]; exact (doubleSlope xR yR ^ 2).val_lt)
    (by rw [htxVal]; exact (2 * xR).val_lt)
  dsimp only at hxo
  change regValue (pointAddT2 workStart) afterXOut =
      (regValue (pointAddT0 workStart) afterTwoX + p -
        regValue (pointAddT1 workStart) afterTwoX) % p ∧
    ∀ w, w ∉ pointAddT2 workStart →
      afterXOut w = afterTwoX w at hxo
  have hxoVal : regValue (pointAddT2 workStart) afterXOut =
      (doubleX xR yR).val := by
    calc
      regValue (pointAddT2 workStart) afterXOut =
          ((doubleSlope xR yR ^ 2).val + p -
            (2 * xR).val) % p := by
        simpa [ht0TX, hssVal, htxVal] using hxo.1
      _ = (doubleSlope xR yR ^ 2 - 2 * xR).val :=
        fieldSubVal _ _
      _ = (doubleX xR yR).val := by
        rfl

  let xPreparation := slopeSq ++ twoX
  let xPreparationSupport :=
    pointAddX workStart ++
      (pointAddT0 workStart ++
        (pointAddT1 workStart ++
          (pointAddT3 workStart ++
            (shiftWires (pointAddArithmeticOffset workStart)
                  Secp256k1Instance.secpAddLayout.allWires ++
              shiftWires (pointAddArithmeticOffset workStart)
                Secp256k1Instance.secpMulLayout.allWires))))
  have hxPreparationRun :
      Classical.run xPreparation stage1 = afterTwoX := by
    simp [xPreparation, twoX, afterTwoX, slopeSq, afterSlopeSq,
      Classical.run_append]
  have hxPreparationUses :
      CircuitUsesOnly xPreparationSupport xPreparation := by
    apply usesOnly_append
    · apply usesOnly_mono
        (fieldMul_usesOnly (pointAddArithmeticOffset workStart)
          (pointAddT3 workStart) (pointAddT3 workStart)
          (pointAddT0 workStart))
      intro w hw
      rcases List.mem_append.mp hw with hprefix | hmul
      · rcases List.mem_append.mp hprefix with hpair | ht0w
        · rcases List.mem_append.mp hpair with ht3w | ht3w
          · simp only [xPreparationSupport, List.mem_append]
            exact Or.inr (Or.inr (Or.inr (Or.inl ht3w)))
          · simp only [xPreparationSupport, List.mem_append]
            exact Or.inr (Or.inr (Or.inr (Or.inl ht3w)))
        · simp only [xPreparationSupport, List.mem_append]
          exact Or.inr (Or.inl ht0w)
      · simp only [xPreparationSupport, List.mem_append]
        exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr hmul))))
    · apply usesOnly_mono
        (fieldAdd_usesOnly (pointAddArithmeticOffset workStart)
          (pointAddX workStart) (pointAddX workStart)
          (pointAddT1 workStart))
      intro w hw
      rcases List.mem_append.mp hw with hprefix | hadd
      · rcases List.mem_append.mp hprefix with hpair | ht1w
        · rcases List.mem_append.mp hpair with hxw | hxw
          · simp only [xPreparationSupport, List.mem_append]
            exact Or.inl hxw
          · simp only [xPreparationSupport, List.mem_append]
            exact Or.inl hxw
        · simp only [xPreparationSupport, List.mem_append]
          exact Or.inr (Or.inr (Or.inl ht1w))
      · simp only [xPreparationSupport, List.mem_append]
        exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hadd))))
  have hxPreparationFree : Classical.HPFree xPreparation := by
    simp [xPreparation, slopeSq, twoX,
      fieldMul_HPFree, fieldAdd_HPFree]
  have hxPreparationWellFormed : CircuitWellFormed xPreparation := by
    simp [xPreparation, slopeSq, twoX,
      fieldMul_wellFormed, fieldAdd_wellFormed,
      IsPointAddFieldRegister]
  have hxPreparationT2 : ModExp.Schedule.WireDisjoint
      xPreparationSupport (pointAddT2 workStart) := by
    intro w hw v hv
    dsimp only [xPreparationSupport] at hw
    rcases List.mem_append.mp hw with hxw | hrest
    · exact hXT2 w hxw v hv
    rcases List.mem_append.mp hrest with ht0w | hrest
    · exact hT0T2 w ht0w v hv
    rcases List.mem_append.mp hrest with ht1w | hrest
    · exact hT1T2 w ht1w v hv
    rcases List.mem_append.mp hrest with ht3w | hrest
    · exact hT3T2 w ht3w v hv
    rcases List.mem_append.mp hrest with haddw | hmulw
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpAddLayout.allWires
        (pointAddT2 workStart) hT2) w haddw v hv
    · exact (pointAddEngine_field_disjoint workStart
        Secp256k1Instance.secpMulLayout.allWires
        (pointAddT2 workStart) hT2) w hmulw v hv
  have hstage2 := bennett_uncompute_after_local_update
    xPreparation xOut xPreparationSupport (pointAddT2 workStart)
    stage1 hxPreparationUses hxPreparationFree
    hxPreparationWellFormed hxPreparationT2 (by
      intro w hw
      rw [hxPreparationRun]
      exact hxo.2 w hw)
  dsimp only at hstage2
  let stage2 := Classical.run
    (xPreparation ++ xOut ++ xPreparation.reverse) stage1
  change (∀ w, w ∉ pointAddT2 workStart → stage2 w = stage1 w) ∧
    (∀ w ∈ pointAddT2 workStart,
      stage2 w = Classical.run xOut
        (Classical.run xPreparation stage1) w) at hstage2
  have hstage2T2 : regValue (pointAddT2 workStart) stage2 =
      (doubleX xR yR).val := by
    calc
      regValue (pointAddT2 workStart) stage2 =
          regValue (pointAddT2 workStart)
            (Classical.run xOut
              (Classical.run xPreparation stage1)) := by
        apply regValue_congr
        exact hstage2.2
      _ = regValue (pointAddT2 workStart) afterXOut := by
        rw [hxPreparationRun]
      _ = (doubleX xR yR).val := hxoVal

  let xDifference := fieldSub
    (pointAddArithmeticOffset workStart)
    (pointAddX workStart) (pointAddT2 workStart)
    (pointAddT0 workStart)
  let afterXDifference := Classical.run xDifference stage2
  have hcleanT0Stage2 := clean_of_preserved_outside
    hT0T2 hcleanT0Stage1 hstage2.1
  have hcleanAddStage2 := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT2 workStart) hT2)
    hcleanAddStage1 hstage2.1
  have hxStage2 := regValue_of_preserved_outside hXT2 hstage2.1
  have hxd := fieldSub_correct workStart
    (pointAddX workStart) (pointAddT2 workStart)
    (pointAddT0 workStart) hX hT2 hT0
    (by
      simpa [pointAddT0, pointAddX] using
        pointAddFieldAt_ne workStart 2 0 (by norm_num))
    (by
      simpa [pointAddT0, pointAddT2] using
        pointAddFieldAt_ne workStart 2 4 (by norm_num))
    stage2 hcleanT0Stage2
    (clean_fieldSubEngine_of_addEngine workStart stage2 hcleanAddStage2)
    (by rw [hxStage2, hxStage1, hxReg]; exact xR.val_lt)
    (by rw [hstage2T2]; exact (doubleX xR yR).val_lt)
  dsimp only at hxd
  change regValue (pointAddT0 workStart) afterXDifference =
      (regValue (pointAddX workStart) stage2 + p -
        regValue (pointAddT2 workStart) stage2) % p ∧
    ∀ w, w ∉ pointAddT0 workStart →
      afterXDifference w = stage2 w at hxd
  have hxdVal : regValue (pointAddT0 workStart) afterXDifference =
      (xR - doubleX xR yR).val := by
    calc
      regValue (pointAddT0 workStart) afterXDifference =
          (xR.val + p - (doubleX xR yR).val) % p := by
        simpa [hxStage2, hxStage1, hxReg, hstage2T2] using hxd.1
      _ = (xR - doubleX xR yR).val := fieldSubVal _ _

  let yProduct := fieldMul
    (pointAddArithmeticOffset workStart)
    (pointAddT3 workStart) (pointAddT0 workStart)
    (pointAddT1 workStart)
  let afterYProduct := Classical.run yProduct afterXDifference
  have hcleanT1Stage2 := clean_of_preserved_outside
    hT1T2 hcleanT1Stage1 hstage2.1
  have hcleanT1XD := clean_of_preserved_outside
    hT1T0 hcleanT1Stage2 hxd.2
  have hcleanMulStage2 := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT2 workStart) hT2)
    hcleanMulStage1 hstage2.1
  have hcleanMulXD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpMulLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanMulStage2 hxd.2
  have ht3Stage2 := regValue_of_preserved_outside hT3T2 hstage2.1
  have ht3XD := regValue_of_preserved_outside hT3T0 hxd.2
  have hyp := fieldMul_correct workStart
    (pointAddT3 workStart) (pointAddT0 workStart)
    (pointAddT1 workStart) hT3 hT0 hT1
    (by
      simpa [pointAddT1, pointAddT3] using
        pointAddFieldAt_ne workStart 3 5 (by norm_num))
    (by
      simpa [pointAddT1, pointAddT0] using
        pointAddFieldAt_ne workStart 3 2 (by norm_num))
    afterXDifference hcleanT1XD hcleanMulXD
    (by rw [ht3XD, ht3Stage2, hstage1T3]; exact
      (doubleSlope xR yR).val_lt)
    (by rw [hxdVal]; exact (xR - doubleX xR yR).val_lt)
  dsimp only at hyp
  change regValue (pointAddT1 workStart) afterYProduct =
      regValue (pointAddT3 workStart) afterXDifference *
        regValue (pointAddT0 workStart) afterXDifference % p ∧
    ∀ w, w ∉ pointAddT1 workStart →
      afterYProduct w = afterXDifference w at hyp
  have hypVal : regValue (pointAddT1 workStart) afterYProduct =
      (doubleSlope xR yR * (xR - doubleX xR yR)).val := by
    calc
      regValue (pointAddT1 workStart) afterYProduct =
          (doubleSlope xR yR).val *
            (xR - doubleX xR yR).val % p := by
        simpa [ht3XD, ht3Stage2, hstage1T3, hxdVal] using hyp.1
      _ = (doubleSlope xR yR *
          (xR - doubleX xR yR)).val := by
        rw [ZMod.val_mul]

  let yOut := fieldSub
    (pointAddArithmeticOffset workStart)
    (pointAddT1 workStart) (pointAddY workStart)
    (pointAddT4 workStart)
  let afterYOut := Classical.run yOut afterYProduct
  have hcleanT4Stage1 := clean_of_preserved_outside
    hT4T3 hcleanT4 hstage1.1
  have hcleanT4Stage2 := clean_of_preserved_outside
    hT4T2 hcleanT4Stage1 hstage2.1
  have hcleanT4XD := clean_of_preserved_outside
    hT4T0 hcleanT4Stage2 hxd.2
  have hcleanT4YP := clean_of_preserved_outside
    hT4T1 hcleanT4XD hyp.2
  have hcleanAddXD := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT0 workStart) hT0)
    hcleanAddStage2 hxd.2
  have hcleanAddYP := clean_of_preserved_outside
    (pointAddEngine_field_disjoint workStart
      Secp256k1Instance.secpAddLayout.allWires
      (pointAddT1 workStart) hT1)
    hcleanAddXD hyp.2
  have hyT3 : ModExp.Schedule.WireDisjoint
      (pointAddY workStart) (pointAddT3 workStart) := by
    simpa [pointAddY, pointAddT3] using
      pointAddFieldAt_disjoint workStart 1 5 (by norm_num)
  have hyStage1 := regValue_of_preserved_outside hyT3 hstage1.1
  have hyStage2 := regValue_of_preserved_outside hYT2 hstage2.1
  have hyXD := regValue_of_preserved_outside hYT0 hxd.2
  have hyYP := regValue_of_preserved_outside hYT1 hyp.2
  have hyo := fieldSub_correct workStart
    (pointAddT1 workStart) (pointAddY workStart)
    (pointAddT4 workStart) hT1 hY hT4
    (by
      simpa [pointAddT4, pointAddT1] using
        pointAddFieldAt_ne workStart 6 3 (by norm_num))
    (by
      simpa [pointAddT4, pointAddY] using
        pointAddFieldAt_ne workStart 6 1 (by norm_num))
    afterYProduct hcleanT4YP
    (clean_fieldSubEngine_of_addEngine workStart afterYProduct hcleanAddYP)
    (by rw [hypVal]; exact
      (doubleSlope xR yR * (xR - doubleX xR yR)).val_lt)
    (by rw [hyYP, hyXD, hyStage2, hyStage1, hyReg]; exact yR.val_lt)
  dsimp only at hyo
  change regValue (pointAddT4 workStart) afterYOut =
      (regValue (pointAddT1 workStart) afterYProduct + p -
        regValue (pointAddY workStart) afterYProduct) % p ∧
    ∀ w, w ∉ pointAddT4 workStart →
      afterYOut w = afterYProduct w at hyo
  have hyoVal : regValue (pointAddT4 workStart) afterYOut =
      (doubleY xR yR).val := by
    calc
      regValue (pointAddT4 workStart) afterYOut =
          ((doubleSlope xR yR *
              (xR - doubleX xR yR)).val + p - yR.val) % p := by
        simpa [hypVal, hyYP, hyXD, hyStage2, hyStage1, hyReg] using hyo.1
      _ = (doubleSlope xR yR *
          (xR - doubleX xR yR) - yR).val := fieldSubVal _ _
      _ = (doubleY xR yR).val := by
        rfl
  have ht2XD := regValue_of_preserved_outside hT2T0 hxd.2
  have ht2YP := regValue_of_preserved_outside hT2T1 hyp.2
  have ht2YO := regValue_of_preserved_outside hT2T4 hyo.2
  have hfinalT2 : regValue (pointAddT2 workStart) afterYOut =
      (doubleX xR yR).val := by
    rw [ht2YO, ht2YP, ht2XD, hstage2T2]
  have hcleanCandidateStage1 := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT3 workStart) hT3)
    hcleanCandidate hstage1.1
  have hcleanCandidateStage2 := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT2 workStart) hT2)
    hcleanCandidateStage1 hstage2.1
  have hcleanCandidateXD := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT0 workStart) hT0)
    hcleanCandidateStage2 hxd.2
  have hcleanCandidateYP := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT1 workStart) hT1)
    hcleanCandidateXD hyp.2
  have hcleanCandidateYO := clean_of_preserved_outside
    (pointAddCandidate_field_disjoint workStart
      (pointAddT4 workStart) hT4)
    hcleanCandidateYP hyo.2
  have hdoubleRun :
      Classical.run (doublePointCompute workStart) st = afterYOut := by
    simp [doublePointCompute, preparation, xPreparation,
      stage1, stage2, numerator, denominator, inverse, slope,
      slopeSq, twoX, xOut, xDifference, yProduct, yOut,
      afterXDifference, afterYProduct, afterYOut, Classical.run_append,
      List.reverse_append, List.append_assoc]
  dsimp only
  rw [hdoubleRun]
  exact ⟨hfinalT2, hyoVal, hcleanCandidateYO⟩

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 300 in
private theorem packFinitePoint_correct
    (workStart : Wire) {x y : Fp}
    (hpoint : curve.toAffine.Nonsingular x y)
    (st : BasisState)
    (hx : regValue (pointAddT2 workStart) st = x.val)
    (hy : regValue (pointAddT4 workStart) st = y.val)
    (hclean : Clean (pointAddCandidate workStart) st) :
    regValue (pointAddCandidate workStart)
        (Classical.run
          (packFinitePoint
            (pointAddT2 workStart)
            (pointAddT4 workStart)
            (pointAddCandidate workStart)) st) =
      encodeNat (.some hpoint) := by
  let point := pointAddCandidate workStart
  let xSource := (pointAddT2 workStart).take 256
  let ySource := (pointAddT4 workStart).take 256
  let tag := PointRegister.tag point
  let xTarget := PointRegister.x point
  let yTarget := PointRegister.y point
  have hpointLength : point.length = pointWidth := by
    simp [point, pointAddCandidate]
  have hpointNodup : point.Nodup := by
    dsimp only [point, pointAddCandidate]
    exact List.nodup_range'
  have hslicesNodup : (tag ++ xTarget ++ yTarget).Nodup := by
    simpa [tag, xTarget, yTarget] using
      PointRegister.tag_x_y_nodup point hpointLength hpointNodup
  obtain ⟨htagxNodup, hyTargetNodup, htagxY⟩ :=
    List.nodup_append.mp hslicesNodup
  obtain ⟨htagNodup, hxTargetNodup, htagX⟩ :=
    List.nodup_append.mp htagxNodup
  have htagNotX : ∀ w ∈ tag, w ∉ xTarget := by
    intro w hw hwx
    exact htagX w hw w hwx rfl
  have hxNotTag : ∀ w ∈ xTarget, w ∉ tag := by
    intro w hw hwt
    exact htagX w hwt w hw rfl
  have hyNotTag : ∀ w ∈ yTarget, w ∉ tag := by
    intro w hw hwt
    exact htagxY w (List.mem_append_left _ hwt) w hw rfl
  have hyNotX : ∀ w ∈ yTarget, w ∉ xTarget := by
    intro w hw hwx
    exact htagxY w (List.mem_append_right _ hwx) w hw rfl
  have htagNotY : ∀ w ∈ tag, w ∉ yTarget := by
    intro w hw hwy
    exact htagxY w (List.mem_append_left _ hw) w hwy rfl
  have hxNotY : ∀ w ∈ xTarget, w ∉ yTarget := by
    intro w hw hwy
    exact htagxY w (List.mem_append_right _ hw) w hwy rfl
  have hcleanTag : Clean tag st := by
    intro w hw
    exact hclean w (by
      exact List.mem_of_mem_take hw)
  have hcleanXTarget : Clean xTarget st := by
    intro w hw
    exact hclean w (by
      exact List.mem_of_mem_drop (List.mem_of_mem_take hw))
  have hcleanYTarget : Clean yTarget st := by
    intro w hw
    exact hclean w (by
      exact List.mem_of_mem_drop (List.mem_of_mem_take hw))
  have hcandidateT2 := pointAddCandidate_field_disjoint workStart
    (pointAddT2 workStart) (by simp [IsPointAddFieldRegister])
  have hcandidateT4 := pointAddCandidate_field_disjoint workStart
    (pointAddT4 workStart) (by simp [IsPointAddFieldRegister])
  have hxSourceOutsidePoint : ∀ w ∈ xSource, w ∉ point := by
    intro w hw hpointMem
    exact hcandidateT2 w hpointMem w
      (List.mem_of_mem_take hw) rfl
  have hySourceOutsidePoint : ∀ w ∈ ySource, w ∉ point := by
    intro w hw hpointMem
    exact hcandidateT4 w hpointMem w
      (List.mem_of_mem_take hw) rfl
  have hxLow : regValue xSource st = x.val := by
    dsimp only [xSource]
    rw [regValue_take_mod, hx, Nat.mod_eq_of_lt]
    exact x.val_lt.trans (by norm_num [p])
  have hyLow : regValue ySource st = y.val := by
    dsimp only [ySource]
    rw [regValue_take_mod, hy, Nat.mod_eq_of_lt]
    exact y.val_lt.trans (by norm_num [p])

  let loadTag := loadConst tag 1
  let afterTag := Classical.run loadTag st
  have htagValue := loadConst_correct tag 1 st htagNodup hcleanTag (by
    rw [PointRegister.tag_length point hpointLength]
    norm_num)
  change regValue tag afterTag = 1 at htagValue
  have hcleanXAfterTag : Clean xTarget afterTag := by
    intro w hw
    change Classical.run loadTag st w = false
    rw [loadConst_other w tag 1 st (hxNotTag w hw)]
    exact hcleanXTarget w hw
  have hcleanYAfterTag : Clean yTarget afterTag := by
    intro w hw
    change Classical.run loadTag st w = false
    rw [loadConst_other w tag 1 st (hyNotTag w hw)]
    exact hcleanYTarget w hw
  have hxLowAfterTag : regValue xSource afterTag = x.val := by
    calc
      regValue xSource afterTag = regValue xSource st := by
        apply regValue_congr
        intro w hw
        change Classical.run loadTag st w = st w
        exact loadConst_other w tag 1 st (by
          intro htagMem
          exact hxSourceOutsidePoint w hw
            (List.mem_of_mem_take htagMem))
      _ = x.val := hxLow
  have hyLowAfterTag : regValue ySource afterTag = y.val := by
    calc
      regValue ySource afterTag = regValue ySource st := by
        apply regValue_congr
        intro w hw
        change Classical.run loadTag st w = st w
        exact loadConst_other w tag 1 st (by
          intro htagMem
          exact hySourceOutsidePoint w hw
            (List.mem_of_mem_take htagMem))
      _ = y.val := hyLow

  have hxCopyNodup : (xSource ++ xTarget).Nodup := by
    have h := range'_append_nodup_of_le
      (workStart + 4 * 257) 256
      (workStart + 3086 + 1) 256 (by omega)
    simpa [xSource, xTarget, point, pointAddT2,
      pointAddCandidate, PointRegister.x,
      fieldWidth, Secp256k1Instance.fieldWidth, candidateOffset,
      flagOffset, yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      List.take_range'_of_length_ge, List.drop_range'] using h
  let copyX := Arithmetic.copyReg xSource xTarget
  let afterX := Classical.run copyX afterTag
  have hxTargetValue := Arithmetic.copyReg_correct
    xSource xTarget afterTag (by
      simp [xSource, xTarget, point, pointAddT2, pointAddCandidate,
        PointRegister.x, pointWidth, fieldWidth,
        Secp256k1Instance.fieldWidth])
    hxCopyNodup hcleanXAfterTag
  change regValue xTarget afterX = regValue xSource afterTag at hxTargetValue
  have hxTargetValue' : regValue xTarget afterX = x.val :=
    hxTargetValue.trans hxLowAfterTag
  have htagAfterX : regValue tag afterX = 1 := by
    calc
      regValue tag afterX = regValue tag afterTag := by
        apply regValue_congr
        intro w hw
        change Classical.run copyX afterTag w = afterTag w
        exact Arithmetic.copyReg_other w xSource xTarget afterTag
          (htagNotX w hw)
      _ = 1 := htagValue
  have hcleanYAfterX : Clean yTarget afterX := by
    intro w hw
    change Classical.run copyX afterTag w = false
    rw [Arithmetic.copyReg_other w xSource xTarget afterTag
      (hyNotX w hw)]
    exact hcleanYAfterTag w hw
  have hyLowAfterX : regValue ySource afterX = y.val := by
    calc
      regValue ySource afterX = regValue ySource afterTag := by
        apply regValue_congr
        intro w hw
        change Classical.run copyX afterTag w = afterTag w
        exact Arithmetic.copyReg_other w xSource xTarget afterTag (by
          intro hxMem
          exact hySourceOutsidePoint w hw (by
            exact List.mem_of_mem_drop (List.mem_of_mem_take hxMem)))
      _ = y.val := hyLowAfterTag

  have hyCopyNodup : (ySource ++ yTarget).Nodup := by
    have h := range'_append_nodup_of_le
      (workStart + 6 * 257) 256
      (workStart + 3086 + 257) 256 (by omega)
    simpa [ySource, yTarget, point, pointAddT4,
      pointAddCandidate, PointRegister.y,
      fieldWidth, Secp256k1Instance.fieldWidth, candidateOffset,
      flagOffset, yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      List.take_range'_of_length_ge, List.drop_range'] using h
  let copyY := Arithmetic.copyReg ySource yTarget
  let afterY := Classical.run copyY afterX
  have hyTargetValue := Arithmetic.copyReg_correct
    ySource yTarget afterX (by
      simp [ySource, yTarget, point, pointAddT4, pointAddCandidate,
        PointRegister.y, pointWidth, fieldWidth,
        Secp256k1Instance.fieldWidth])
    hyCopyNodup hcleanYAfterX
  change regValue yTarget afterY = regValue ySource afterX at hyTargetValue
  have hyTargetValue' : regValue yTarget afterY = y.val :=
    hyTargetValue.trans hyLowAfterX
  have htagAfterY : regValue tag afterY = 1 := by
    calc
      regValue tag afterY = regValue tag afterX := by
        apply regValue_congr
        intro w hw
        change Classical.run copyY afterX w = afterX w
        exact Arithmetic.copyReg_other w ySource yTarget afterX
          (htagNotY w hw)
      _ = 1 := htagAfterX
  have hxTargetAfterY : regValue xTarget afterY = x.val := by
    calc
      regValue xTarget afterY = regValue xTarget afterX := by
        apply regValue_congr
        intro w hw
        change Classical.run copyY afterX w = afterX w
        exact Arithmetic.copyReg_other w ySource yTarget afterX
          (hxNotY w hw)
      _ = x.val := hxTargetValue'
  have hpackRun :
      Classical.run
        (packFinitePoint
          (pointAddT2 workStart)
          (pointAddT4 workStart)
          (pointAddCandidate workStart)) st = afterY := by
    simp [packFinitePoint, point, xSource, ySource, tag, xTarget,
      yTarget, loadTag, copyX, copyY, afterTag, afterX, afterY,
      Classical.run_append]
  rw [hpackRun]
  calc
    regValue (pointAddCandidate workStart) afterY =
        regValue tag afterY + 2 * regValue xTarget afterY +
          2 ^ 257 * regValue yTarget afterY := by
      simpa [point, tag, xTarget, yTarget] using
        PointRegister.regValue_decompose point afterY hpointLength
    _ = encodeNat (.some hpoint) := by
      simp [htagAfterY, hxTargetAfterY, hyTargetValue', encodeNat_some]

private theorem genericPointBranch_preserves_other_control
    (workStart : Wire) (xC yC : Fp)
    (index : Nat) (hindex : index < 6) (hother : index ≠ 3)
    (st : BasisState) :
    Classical.run (genericPointBranch workStart xC yC) st
        (workStart + flagOffset + index) =
      st (workStart + flagOffset + index) := by
  let active := genericPointCompute workStart xC yC ++
    packFinitePoint
      (pointAddT2 workStart)
      (pointAddT4 workStart)
      (pointAddCandidate workStart)
  let support := pointAddGenericFlag workStart ::
    (pointAddBranchActiveSupport workStart ++
      pointAddSelected workStart)
  have hactiveUses :
      CircuitUsesOnly (pointAddBranchActiveSupport workStart) active :=
    usesOnly_append
      (genericPointCompute_usesOnly workStart xC yC)
      (packFinitePoint_usesOnly_pointAdd workStart)
  have hactiveUses' : CircuitUsesOnly support active := by
    apply usesOnly_mono hactiveUses
    intro w hw
    simp [support, hw]
  have hcopyUses : CircuitUsesOnly support
      (controlledCopyReg
        (pointAddGenericFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart)) := by
    apply usesOnly_mono
      (controlledCopyReg_usesOnly
        (pointAddGenericFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart))
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with hleft | hselected
    · rcases hleft with hcontrol | hcandidate
      · simp [support, hcontrol]
      · simp [support, pointAddBranchActiveSupport, hcandidate]
    · simp [support, hselected]
  have hbranchUses : CircuitUsesOnly support
      (genericPointBranch workStart xC yC) := by
    simpa [genericPointBranch, active, List.append_assoc] using
      usesOnly_append
        (usesOnly_append hactiveUses' hcopyUses)
        (usesOnly_reverse hactiveUses')
  apply hbranchUses.preservesOutside
  simp only [support, List.mem_cons, List.mem_append, not_or]
  refine ⟨?_, pointAddControl_not_mem_activeSupport
    workStart index hindex, pointAddControl_not_mem_selected
      workStart index hindex⟩
  simp [pointAddGenericFlag]
  omega

private theorem doublePointBranch_preserves_other_control
    (workStart : Wire)
    (index : Nat) (hindex : index < 6) (hother : index ≠ 5)
    (st : BasisState) :
    Classical.run (doublePointBranch workStart) st
        (workStart + flagOffset + index) =
      st (workStart + flagOffset + index) := by
  let active := doublePointCompute workStart ++
    packFinitePoint
      (pointAddT2 workStart)
      (pointAddT4 workStart)
      (pointAddCandidate workStart)
  let support := pointAddDoubleFlag workStart ::
    (pointAddBranchActiveSupport workStart ++
      pointAddSelected workStart)
  have hactiveUses :
      CircuitUsesOnly (pointAddBranchActiveSupport workStart) active :=
    usesOnly_append
      (doublePointCompute_usesOnly workStart)
      (packFinitePoint_usesOnly_pointAdd workStart)
  have hactiveUses' : CircuitUsesOnly support active := by
    apply usesOnly_mono hactiveUses
    intro w hw
    simp [support, hw]
  have hcopyUses : CircuitUsesOnly support
      (controlledCopyReg
        (pointAddDoubleFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart)) := by
    apply usesOnly_mono
      (controlledCopyReg_usesOnly
        (pointAddDoubleFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart))
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with hleft | hselected
    · rcases hleft with hcontrol | hcandidate
      · simp [support, hcontrol]
      · simp [support, pointAddBranchActiveSupport, hcandidate]
    · simp [support, hselected]
  have hbranchUses : CircuitUsesOnly support
      (doublePointBranch workStart) := by
    simpa [doublePointBranch, active, List.append_assoc] using
      usesOnly_append
        (usesOnly_append hactiveUses' hcopyUses)
        (usesOnly_reverse hactiveUses')
  apply hbranchUses.preservesOutside
  simp only [support, List.mem_cons, List.mem_append, not_or]
  refine ⟨?_, pointAddControl_not_mem_activeSupport
    workStart index hindex, pointAddControl_not_mem_selected
      workStart index hindex⟩
  simp [pointAddDoubleFlag]
  omega

/--
When the generic flag is the unique active branch, the branch circuit
computes the generic affine point

    genericAdd hR hC hx

and writes its canonical encoding into `selected`.

This is the lemma that must prove the correctness of
`genericPointCompute`.
-/
theorem pointAddBranches_generic_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (hC : curve.toAffine.Nonsingular xC yC)
    (hx : xR ≠ xC)
    (st : BasisState)
    (hxReg :
      regValue (pointAddX workStart) st = xR.val)
    (hyReg :
      regValue (pointAddY workStart) st = yR.val)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = true)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (genericAdd hR hC hx) := by
  have hselectedClean : Clean (pointAddSelected workStart) st := by
    apply Arithmetic.Clean.mono hclean
    intro w hw
    simp [pointAddBranchWork, hw]
  have hselected := genericPointBranch_selectedValue
    workStart xC yC st hgeneric hselectedClean
  let afterCompute := Classical.run
    (genericPointCompute workStart xC yC) st
  have hcompute := genericPointCompute_correct
    workStart xR yR xC yC hx st hxReg hyReg hclean
  dsimp only at hcompute
  change regValue (pointAddT2 workStart) afterCompute =
      (genericX xR yR xC yC).val ∧
    regValue (pointAddT4 workStart) afterCompute =
      (genericY xR yR xC yC).val ∧
    Clean (pointAddCandidate workStart) afterCompute at hcompute
  have hpacked := packFinitePoint_correct workStart
    (generic_nonsingular hR hC hx) afterCompute
    hcompute.1 hcompute.2.1 hcompute.2.2
  have hcandidateValue :
      regValue (pointAddCandidate workStart)
          (Classical.run
            (genericPointCompute workStart xC yC ++
              packFinitePoint
                (pointAddT2 workStart)
                (pointAddT4 workStart)
                (pointAddCandidate workStart)) st) =
        encodeNat (genericAdd hR hC hx) := by
    rw [Classical.run_append]
    set_option exponentiation.threshold 300 in
      simpa [afterCompute, genericAdd] using hpacked
  let afterGeneric := Classical.run
    (genericPointBranch workStart xC yC) st
  have hdoubleAfter :
      afterGeneric (pointAddDoubleFlag workStart) = false := by
    change Classical.run (genericPointBranch workStart xC yC) st
        (workStart + flagOffset + 5) = false
    rw [genericPointBranch_preserves_other_control
      workStart xC yC 5 (by norm_num) (by norm_num) st]
    simpa [pointAddDoubleFlag] using hdouble
  have hinfinityAfter :
      afterGeneric (pointAddInfinityFlag workStart) = false := by
    change Classical.run (genericPointBranch workStart xC yC) st
        (workStart + flagOffset + 0) = false
    rw [genericPointBranch_preserves_other_control
      workStart xC yC 0 (by norm_num) (by norm_num) st]
    simpa [pointAddInfinityFlag] using hinfinity
  have hdoubleIdentity :
      Classical.run (doublePointBranch workStart) afterGeneric =
        afterGeneric :=
    doublePointBranch_false workStart afterGeneric hdoubleAfter
  have hinfinityIdentity :
      Classical.run (infinityPointBranch workStart (.some hC))
          afterGeneric = afterGeneric :=
    infinityPointBranch_false workStart (.some hC)
      afterGeneric hinfinityAfter
  have hbranchesRun :
      Classical.run (pointAddBranches workStart hC) st =
        afterGeneric := by
    simp [pointAddBranches, afterGeneric, Classical.run_append,
      hdoubleIdentity, hinfinityIdentity]
  rw [hbranchesRun]
  exact hselected.trans hcandidateValue

/--
When the doubling flag is the unique active branch, the branch circuit
computes the secp256k1 doubling formulas and writes that point into
`selected`.
-/
theorem pointAddBranches_double_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (hC : curve.toAffine.Nonsingular xC yC)
    (hx : xR = xC)
    (hinv : yR ≠ -yC)
    (st : BasisState)
    (hxReg :
      regValue (pointAddX workStart) st = xR.val)
    (hyReg :
      regValue (pointAddY workStart) st = yR.val)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = true)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat
        (doublePoint hR
          (self_not_inverse_of_x_eq_of_not_inverse
            hR hC hx hinv)) := by
  let hySelf := self_not_inverse_of_x_eq_of_not_inverse
    hR hC hx hinv
  have hselectedClean : Clean (pointAddSelected workStart) st := by
    apply Arithmetic.Clean.mono hclean
    intro w hw
    simp [pointAddBranchWork, hw]
  have hselected := doublePointBranch_selectedValue
    workStart st hdouble hselectedClean
  let afterCompute := Classical.run (doublePointCompute workStart) st
  have hcompute := doublePointCompute_correct
    workStart xR yR hySelf st hxReg hyReg hclean
  dsimp only at hcompute
  change regValue (pointAddT2 workStart) afterCompute =
      (doubleX xR yR).val ∧
    regValue (pointAddT4 workStart) afterCompute =
      (doubleY xR yR).val ∧
    Clean (pointAddCandidate workStart) afterCompute at hcompute
  have hpacked := packFinitePoint_correct workStart
    (double_nonsingular hR hySelf) afterCompute
    hcompute.1 hcompute.2.1 hcompute.2.2
  have hcandidateValue :
      regValue (pointAddCandidate workStart)
          (Classical.run
            (doublePointCompute workStart ++
              packFinitePoint
                (pointAddT2 workStart)
                (pointAddT4 workStart)
                (pointAddCandidate workStart)) st) =
        encodeNat (doublePoint hR hySelf) := by
    rw [Classical.run_append]
    set_option exponentiation.threshold 300 in
      simpa [afterCompute, doublePoint] using hpacked
  have hgenericIdentity :
      Classical.run (genericPointBranch workStart xC yC) st = st :=
    genericPointBranch_false workStart xC yC st hgeneric
  let afterDouble := Classical.run (doublePointBranch workStart) st
  have hinfinityAfter :
      afterDouble (pointAddInfinityFlag workStart) = false := by
    change Classical.run (doublePointBranch workStart) st
        (workStart + flagOffset + 0) = false
    rw [doublePointBranch_preserves_other_control
      workStart 0 (by norm_num) (by norm_num) st]
    simpa [pointAddInfinityFlag] using hinfinity
  have hinfinityIdentity :
      Classical.run (infinityPointBranch workStart (.some hC))
          afterDouble = afterDouble :=
    infinityPointBranch_false workStart (.some hC)
      afterDouble hinfinityAfter
  have hbranchesRun :
      Classical.run (pointAddBranches workStart hC) st =
        afterDouble := by
    simp [pointAddBranches, afterDouble, Classical.run_append,
      hgenericIdentity, hinfinityIdentity]
  rw [hbranchesRun]
  simpa only [hySelf] using hselected.trans hcandidateValue

theorem pointAddFiniteCompute_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat R)
    (hclean :
      Clean (pointAddWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddFiniteCompute pointReg workStart hC)
          st) =
      encodeNat (affineAdd R (.some hC)) := by

  rw [pointAddFiniteCompute, Classical.run_append]

  let setupState :=
    Classical.run
      (pointAddSetup pointReg workStart xC yC)
      st

  change
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          setupState) =
      encodeNat (affineAdd R (.some hC))

  cases R with

  | zero =>
      have hsetup :=
        pointAddSetup_zero_correct
          pointReg outReg workStart
          (xC := xC) (yC := yC)
          st hpointLength hnodup hpoint hclean

      change
        setupState (pointAddInfinityFlag workStart) = true ∧
          setupState (pointAddGenericFlag workStart) = false ∧
          setupState (pointAddDoubleFlag workStart) = false ∧
          Clean (pointAddBranchWork workStart) setupState
        at hsetup

      rcases hsetup with
        ⟨hinfinity, hgeneric, hdouble, hbranchClean⟩

      have hbranches :=
        pointAddBranches_infinity_correct
          workStart hC setupState
          hinfinity hgeneric hdouble hbranchClean

      simpa only [affineAdd_zero_left] using hbranches

  | some hR =>
      rename_i xR yR

      have hsetup :=
        pointAddSetup_some_correct
          pointReg outReg workStart
          (xC := xC) (yC := yC)
          hR st
          hpointLength hnodup hpoint hclean

      change
        regValue (pointAddX workStart) setupState = xR.val ∧
          regValue (pointAddY workStart) setupState = yR.val ∧
          setupState (pointAddInfinityFlag workStart) = false ∧
          setupState (pointAddGenericFlag workStart) =
            decide (xR ≠ xC) ∧
          setupState (pointAddDoubleFlag workStart) =
            decide (xR = xC ∧ yR ≠ -yC) ∧
          Clean (pointAddBranchWork workStart) setupState
        at hsetup

      rcases hsetup with
        ⟨hxReg, hyReg, hinfinity,
         hgeneric, hdouble, hbranchClean⟩

      by_cases hx : xR = xC

      · by_cases hinv : yR = -yC

        ·
          have hgeneric' :
              setupState
                (pointAddGenericFlag workStart) = false := by
            simpa [hx] using hgeneric

          have hdouble' :
              setupState
                (pointAddDoubleFlag workStart) = false := by
            simpa [hx, hinv] using hdouble

          have hbranches :=
            pointAddBranches_inverse_correct
              workStart hC setupState
              hinfinity hgeneric' hdouble' hbranchClean

          rw [affineAdd_inverse hR hC hx hinv]

          exact hbranches

        ·
          have hgeneric' :
              setupState
                (pointAddGenericFlag workStart) = false := by
            simpa [hx] using hgeneric

          have hdouble' :
              setupState
                (pointAddDoubleFlag workStart) = true := by
            simpa [hx, hinv] using hdouble

          have hbranches :=
            pointAddBranches_double_correct
              workStart hR hC hx hinv setupState
              hxReg hyReg
              hinfinity hgeneric' hdouble'
              hbranchClean

          have haff :
              affineAdd (.some hR) (.some hC) =
                doublePoint hR
                  (self_not_inverse_of_x_eq_of_not_inverse
                    hR hC hx hinv) := by
            unfold affineAdd
            simp [hx, hinv]

          rw [haff]

          exact hbranches

      ·
        have hgeneric' :
            setupState
              (pointAddGenericFlag workStart) = true := by
          simpa [hx] using hgeneric

        have hdouble' :
            setupState
              (pointAddDoubleFlag workStart) = false := by
          simpa [hx] using hdouble

        have hbranches :=
          pointAddBranches_generic_correct
            workStart hR hC hx setupState
            hxReg hyReg
            hinfinity hgeneric' hdouble'
            hbranchClean

        rw [affineAdd_generic hR hC hx]

        exact hbranches

private theorem pointAddFlagWork_mem_work
    (workStart : Wire) :
    ∀ w ∈ pointAddFlagWork workStart,
      w ∈ pointAddWork workStart := by
  intro w hw
  rw [pointAddWork]
  apply List.mem_append_left
  apply List.mem_range'_1.mpr
  simp only [pointAddFlagWork, pointAddConst,
    pointAddZeroHistory, pointAddXDifference,
    pointAddXHistory, pointAddYDifference,
    pointAddYHistory, pointAddInfinityFlag,
    pointAddXEqFlag, pointAddYNegFlag,
    pointAddGenericFlag, pointAddPairFlag,
    pointAddDoubleFlag, List.mem_append, List.mem_cons,
    List.mem_range'_1] at hw
  rw [localWorkSize_eq]
  norm_num [constOffset, zeroHistoryOffset, xDifferenceOffset,
    xHistoryOffset, yDifferenceOffset, yHistoryOffset,
    flagOffset, fieldAreaSize, fieldWidth,
    Secp256k1Instance.fieldWidth] at hw ⊢
  rcases hw with
      (((((h0 | h1) | h2) | h3) | h4) | h5) |
        (h6 | h7 | h8 | h9 | h10 | h11)
  · omega
  · subst w; omega
  · omega
  · omega
  · omega
  · omega
  · subst w; omega
  · subst w; omega
  · subst w; omega
  · subst w; omega
  · subst w; omega
  · subst w; omega

private theorem pointAddSelected_mem_work
    (workStart : Wire) :
    ∀ w ∈ pointAddSelected workStart,
      w ∈ pointAddWork workStart := by
  intro w hw
  rw [pointAddWork]
  apply List.mem_append_left
  apply List.mem_range'_1.mpr
  have hbounds := List.mem_range'_1.mp hw
  rw [localWorkSize_eq]
  norm_num [pointAddSelected, selectedOffset, candidateOffset,
    flagOffset, yHistoryOffset, yDifferenceOffset,
    xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
    constOffset, fieldAreaSize, fieldWidth,
    Secp256k1Instance.fieldWidth, pointWidth] at hbounds ⊢
  omega

private theorem pointAddCoordinateCopies_wellFormed
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup) :
    CircuitWellFormed
      (pointAddCoordinateCopies pointReg workStart) := by
  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup
  have hxSourceNodup : (PointRegister.x pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 1)).trans
        (List.drop_sublist 1 pointReg))
    exact hpointNodup
  have hySourceNodup : (PointRegister.y pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 257)).trans
        (List.drop_sublist 257 pointReg))
    exact hpointNodup
  have hxDestinationNodup :
      ((pointAddX workStart).take 256).Nodup := by
    exact List.Nodup.sublist
      (List.take_sublist 256 (pointAddX workStart))
      (pointAddFieldRegister_nodup workStart _
        (by simp [IsPointAddFieldRegister]))
  have hyDestinationNodup :
      ((pointAddY workStart).take 256).Nodup := by
    exact List.Nodup.sublist
      (List.take_sublist 256 (pointAddY workStart))
      (pointAddFieldRegister_nodup workStart _
        (by simp [IsPointAddFieldRegister]))
  have hxDestinationWork :
      ∀ w ∈ (pointAddX workStart).take 256,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    have hbounds := List.mem_range'_1.mp
      (List.mem_of_mem_take hw)
    simp only [fieldWidth,
      Secp256k1Instance.fieldWidth] at hbounds
    rw [localWorkSize_eq]
    exact ⟨hbounds.1, hbounds.2.trans_le (by omega)⟩
  have hyDestinationWork :
      ∀ w ∈ (pointAddY workStart).take 256,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    have hbounds := List.mem_range'_1.mp
      (List.mem_of_mem_take hw)
    rw [localWorkSize_eq]
    simp only [fieldWidth,
      Secp256k1Instance.fieldWidth] at hbounds
    exact ⟨(Nat.le_add_right workStart 257).trans hbounds.1,
      hbounds.2.trans_le (by omega)⟩
  have hxNodup :
      (PointRegister.x pointReg ++
        (pointAddX workStart).take 256).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hxSourceNodup, hxDestinationNodup, ?_⟩
    intro a ha b hb
    exact hpublicWork a
      (List.mem_append_left outReg
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
      b (hxDestinationWork b hb)
  have hyNodup :
      (PointRegister.y pointReg ++
        (pointAddY workStart).take 256).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hySourceNodup, hyDestinationNodup, ?_⟩
    intro a ha b hb
    exact hpublicWork a
      (List.mem_append_left outReg
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
      b (hyDestinationWork b hb)
  rw [pointAddCoordinateCopies, circuitWellFormed_append]
  exact ⟨Arithmetic.copyReg_wellFormed _ _ hxNodup,
    Arithmetic.copyReg_wellFormed _ _ hyNodup⟩

private theorem pointAddFlags_wellFormed
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup) :
    CircuitWellFormed
      (pointAddFlags pointReg workStart xC yC) := by
  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup
  have htagMem :
      ∀ w ∈ PointRegister.tag pointReg, w ∈ pointReg := by
    intro w hw
    exact List.mem_of_mem_take hw
  have hxMem :
      ∀ w ∈ PointRegister.x pointReg, w ∈ pointReg := by
    intro w hw
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have hyMem :
      ∀ w ∈ PointRegister.y pointReg, w ∈ pointReg := by
    intro w hw
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have htagNodup : (PointRegister.tag pointReg).Nodup := by
    exact List.Nodup.sublist (List.take_sublist 1 pointReg)
      hpointNodup
  have hxNodup : (PointRegister.x pointReg).Nodup := by
    exact List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 1)).trans
        (List.drop_sublist 1 pointReg)) hpointNodup
  have hyNodup : (PointRegister.y pointReg).Nodup := by
    exact List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 257)).trans
        (List.drop_sublist 257 pointReg)) hpointNodup
  have hzeroInternalMem :
      ∀ w ∈
          (pointAddInfinityFlag workStart ::
            pointAddZeroHistory workStart),
        w ∈ pointAddFlagWork workStart := by
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp [pointAddFlagWork]
    · simp [pointAddFlagWork, hw]
  have hxInternalMem :
      ∀ w ∈
          ((pointAddConst workStart ++
              pointAddXDifference workStart) ++
            pointAddXEqFlag workStart ::
              pointAddXHistory workStart),
        w ∈ pointAddFlagWork workStart := by
    intro w hw
    simp only [List.mem_append, List.mem_cons] at hw
    rcases hw with (hconst | hdifference) | hflag | hhistory
    · simp [pointAddFlagWork, hconst]
    · simp [pointAddFlagWork, hdifference]
    · subst w; simp [pointAddFlagWork]
    · simp [pointAddFlagWork, hhistory]
  have hyInternalMem :
      ∀ w ∈
          ((pointAddConst workStart ++
              pointAddYDifference workStart) ++
            pointAddYNegFlag workStart ::
              pointAddYHistory workStart),
        w ∈ pointAddFlagWork workStart := by
    intro w hw
    simp only [List.mem_append, List.mem_cons] at hw
    rcases hw with (hconst | hdifference) | hflag | hhistory
    · simp [pointAddFlagWork, hconst]
    · simp [pointAddFlagWork, hdifference]
    · subst w; simp [pointAddFlagWork]
    · simp [pointAddFlagWork, hhistory]
  have hzeroNodup :
      (zeroFlagWires
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart)).Nodup := by
    rw [zeroFlagWires]
    apply List.nodup_append.mpr
    refine ⟨htagNodup, pointAddZeroFlagWork_nodup workStart, ?_⟩
    intro a ha b hb
    exact hpublicWork a
      (List.mem_append_left outReg (htagMem a ha)) b
      (pointAddFlagWork_mem_work workStart b
        (hzeroInternalMem b hb))
  have hxEqualNodup :
      (equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart)).Nodup := by
    simp only [equalFlagWires, List.append_assoc]
    apply List.nodup_append.mpr
    refine ⟨hxNodup, ?_, ?_⟩
    · simpa only [List.append_assoc] using
        pointAddXEqualWork_nodup workStart
    · intro a ha b hb
      exact hpublicWork a
        (List.mem_append_left outReg (hxMem a ha)) b
        (pointAddFlagWork_mem_work workStart b
          (hxInternalMem b (by
            simpa only [List.append_assoc] using hb)))
  have hyEqualNodup :
      (equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart)).Nodup := by
    simp only [equalFlagWires, List.append_assoc]
    apply List.nodup_append.mpr
    refine ⟨hyNodup, ?_, ?_⟩
    · simpa only [List.append_assoc] using
        pointAddYEqualWork_nodup workStart
    · intro a ha b hb
      exact hpublicWork a
        (List.mem_append_left outReg (hyMem a ha)) b
        (pointAddFlagWork_mem_work workStart b
          (hyInternalMem b (by
            simpa only [List.append_assoc] using hb)))
  have hzeroWellFormed := zeroFlag_wellFormed
    (PointRegister.tag pointReg)
    (pointAddInfinityFlag workStart)
    (pointAddZeroHistory workStart) hzeroNodup
  have hxWellFormed := equalFlag_wellFormed
    (PointRegister.x pointReg)
    (pointAddConst workStart)
    (pointAddXEqFlag workStart)
    (pointAddXDifference workStart)
    (pointAddXHistory workStart) hxEqualNodup
  have hyWellFormed := equalFlag_wellFormed
    (PointRegister.y pointReg)
    (pointAddConst workStart)
    (pointAddYNegFlag workStart)
    (pointAddYDifference workStart)
    (pointAddYHistory workStart) hyEqualNodup
  simp only [pointAddFlags, circuitWellFormed_append,
    circuitWellFormed_cons, circuitWellFormed_nil,
    hzeroWellFormed, hxWellFormed, hyWellFormed,
    loadConst_wellFormed]
  simp [Gate.WellFormed,
    pointAddInfinityFlag, pointAddXEqFlag,
    pointAddYNegFlag, pointAddGenericFlag,
    pointAddPairFlag, pointAddDoubleFlag]

private theorem genericPointBranch_wellFormed
    (workStart : Wire) (xC yC : Fp) :
    CircuitWellFormed
      (genericPointBranch workStart xC yC) := by
  have hcompute := genericPointCompute_wellFormed workStart xC yC
  have hpack := packFinitePoint_wellFormed workStart
  have hcopy : CircuitWellFormed
      (controlledCopyReg
        (pointAddGenericFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart)) := by
    apply controlledCopyReg_wellFormed
    simpa [pointAddGenericFlag, Nat.add_assoc] using
      pointAddControl_candidateSelected_nodup
        workStart 3 (by norm_num)
  simp only [genericPointBranch, circuitWellFormed_append,
    hcompute, hpack, hcopy, Arithmetic.wellFormed_reverse,
    and_self]

private theorem doublePointBranch_wellFormed
    (workStart : Wire) :
    CircuitWellFormed (doublePointBranch workStart) := by
  have hcompute := doublePointCompute_wellFormed workStart
  have hpack := packFinitePoint_wellFormed workStart
  have hcopy : CircuitWellFormed
      (controlledCopyReg
        (pointAddDoubleFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart)) := by
    apply controlledCopyReg_wellFormed
    simpa [pointAddDoubleFlag, Nat.add_assoc] using
      pointAddControl_candidateSelected_nodup
        workStart 5 (by norm_num)
  simp only [doublePointBranch, circuitWellFormed_append,
    hcompute, hpack, hcopy, Arithmetic.wellFormed_reverse,
    and_self]

private theorem infinityPointBranch_wellFormed
    (workStart : Wire) (C : Point) :
    CircuitWellFormed (infinityPointBranch workStart C) := by
  have hload := loadConst_wellFormed
    (pointAddCandidate workStart) (encode C).val
  have hcopy : CircuitWellFormed
      (controlledCopyReg
        (pointAddInfinityFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart)) := by
    apply controlledCopyReg_wellFormed
    simpa [pointAddInfinityFlag, Nat.add_assoc] using
      pointAddControl_candidateSelected_nodup
        workStart 0 (by norm_num)
  simp only [infinityPointBranch, circuitWellFormed_append,
    hload, hcopy, and_self]

private theorem pointAddBranches_wellFormed
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    CircuitWellFormed (pointAddBranches workStart hC) := by
  have hgeneric := genericPointBranch_wellFormed workStart xC yC
  have hdouble := doublePointBranch_wellFormed workStart
  have hinfinity := infinityPointBranch_wellFormed
    workStart (.some hC)
  simp only [pointAddBranches, circuitWellFormed_append,
    hgeneric, hdouble, hinfinity, and_self]

private theorem pointAddFieldRegister_mem_work
    (workStart : Wire) (register : List Wire)
    (hregister : IsPointAddFieldRegister workStart register) :
    ∀ w ∈ register, w ∈ pointAddWork workStart := by
  intro w hw
  rw [pointAddWork]
  apply List.mem_append_left
  apply List.mem_range'_1.mpr
  rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hbounds := List.mem_range'_1.mp hw
    rw [localWorkSize_eq]
    norm_num [pointAddX, pointAddY, pointAddT0,
      pointAddT1, pointAddT2, pointAddT3, pointAddT4,
      fieldWidth, Secp256k1Instance.fieldWidth] at hbounds ⊢
    omega

private theorem pointAddCandidate_mem_work
    (workStart : Wire) :
    ∀ w ∈ pointAddCandidate workStart,
      w ∈ pointAddWork workStart := by
  intro w hw
  rw [pointAddWork]
  apply List.mem_append_left
  apply List.mem_range'_1.mpr
  have hbounds := List.mem_range'_1.mp hw
  rw [localWorkSize_eq]
  norm_num [pointAddCandidate, candidateOffset, flagOffset,
    yHistoryOffset, yDifferenceOffset, xHistoryOffset,
    xDifferenceOffset, zeroHistoryOffset, constOffset,
    fieldAreaSize, fieldWidth, Secp256k1Instance.fieldWidth,
    pointWidth] at hbounds ⊢
  omega

private theorem pointAddControl_mem_work
    (workStart index : Wire) (hindex : index < 6) :
    workStart + flagOffset + index ∈
      pointAddWork workStart := by
  apply pointAddFlagWork_mem_work workStart
  interval_cases index <;>
    simp [pointAddFlagWork, pointAddInfinityFlag, pointAddXEqFlag,
    pointAddYNegFlag, pointAddGenericFlag,
    pointAddPairFlag, pointAddDoubleFlag]

private theorem pointAddBranchActiveSupport_mem_work
    (workStart : Wire) :
    ∀ w ∈ pointAddBranchActiveSupport workStart,
      w ∈ pointAddWork workStart := by
  intro w hw
  simp only [pointAddBranchActiveSupport,
    List.mem_append] at hw
  rcases hw with hx | hy | ht0 | ht1 | ht2 | ht3 | ht4 |
      hcandidate | hadd | hmul | hinv
  · exact pointAddFieldRegister_mem_work workStart _
      (by simp [IsPointAddFieldRegister]) w hx
  · exact pointAddFieldRegister_mem_work workStart _
      (by simp [IsPointAddFieldRegister]) w hy
  · exact pointAddFieldRegister_mem_work workStart _
      (by simp [IsPointAddFieldRegister]) w ht0
  · exact pointAddFieldRegister_mem_work workStart _
      (by simp [IsPointAddFieldRegister]) w ht1
  · exact pointAddFieldRegister_mem_work workStart _
      (by simp [IsPointAddFieldRegister]) w ht2
  · exact pointAddFieldRegister_mem_work workStart _
      (by simp [IsPointAddFieldRegister]) w ht3
  · exact pointAddFieldRegister_mem_work workStart _
      (by simp [IsPointAddFieldRegister]) w ht4
  · exact pointAddCandidate_mem_work workStart w hcandidate
  · rw [pointAddWork]
    apply List.mem_append_right
    simp only [pointAddArithmeticWork, List.mem_dedup,
      List.mem_append]
    exact Or.inl (Or.inl hadd)
  · rw [pointAddWork]
    apply List.mem_append_right
    simp only [pointAddArithmeticWork, List.mem_dedup,
      List.mem_append]
    exact Or.inl (Or.inr hmul)
  · rw [pointAddWork]
    apply List.mem_append_right
    simp only [pointAddArithmeticWork, List.mem_dedup,
      List.mem_append]
    exact Or.inr hinv

private theorem genericPointBranch_usesOnly_work
    (workStart : Wire) (xC yC : Fp) :
    CircuitUsesOnly (pointAddWork workStart)
      (genericPointBranch workStart xC yC) := by
  have hactive :
      ∀ w ∈ pointAddBranchActiveSupport workStart,
        w ∈ pointAddWork workStart :=
    pointAddBranchActiveSupport_mem_work workStart
  have hcompute := usesOnly_mono
    (genericPointCompute_usesOnly workStart xC yC) hactive
  have hpack := usesOnly_mono
    (packFinitePoint_usesOnly_pointAdd workStart) hactive
  have hcopy : CircuitUsesOnly (pointAddWork workStart)
      (controlledCopyReg
        (pointAddGenericFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart)) := by
    apply usesOnly_mono (controlledCopyReg_usesOnly _ _ _)
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with (hcontrol | hcandidate) | hselected
    · subst w
      simpa [pointAddGenericFlag, Nat.add_assoc] using
        pointAddControl_mem_work workStart 3 (by norm_num)
    · exact pointAddCandidate_mem_work workStart w hcandidate
    · exact pointAddSelected_mem_work workStart w hselected
  simp only [genericPointBranch, circuitUsesOnly_append_iff,
    circuitUsesOnly_reverse_iff]
  exact ⟨⟨⟨⟨hcompute, hpack⟩, hcopy⟩, hpack⟩, hcompute⟩

private theorem doublePointBranch_usesOnly_work
    (workStart : Wire) :
    CircuitUsesOnly (pointAddWork workStart)
      (doublePointBranch workStart) := by
  have hactive :
      ∀ w ∈ pointAddBranchActiveSupport workStart,
        w ∈ pointAddWork workStart :=
    pointAddBranchActiveSupport_mem_work workStart
  have hcompute := usesOnly_mono
    (doublePointCompute_usesOnly workStart) hactive
  have hpack := usesOnly_mono
    (packFinitePoint_usesOnly_pointAdd workStart) hactive
  have hcopy : CircuitUsesOnly (pointAddWork workStart)
      (controlledCopyReg
        (pointAddDoubleFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart)) := by
    apply usesOnly_mono (controlledCopyReg_usesOnly _ _ _)
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with (hcontrol | hcandidate) | hselected
    · subst w
      simpa [pointAddDoubleFlag, Nat.add_assoc] using
        pointAddControl_mem_work workStart 5 (by norm_num)
    · exact pointAddCandidate_mem_work workStart w hcandidate
    · exact pointAddSelected_mem_work workStart w hselected
  simp only [doublePointBranch, circuitUsesOnly_append_iff,
    circuitUsesOnly_reverse_iff]
  exact ⟨⟨⟨⟨hcompute, hpack⟩, hcopy⟩, hpack⟩, hcompute⟩

private theorem infinityPointBranch_usesOnly_work
    (workStart : Wire) (C : Point) :
    CircuitUsesOnly (pointAddWork workStart)
      (infinityPointBranch workStart C) := by
  have hload : CircuitUsesOnly (pointAddWork workStart)
      (loadConst (pointAddCandidate workStart) (encode C).val) := by
    apply usesOnly_mono (loadConst_usesOnly _ _)
    exact pointAddCandidate_mem_work workStart
  have hcopy : CircuitUsesOnly (pointAddWork workStart)
      (controlledCopyReg
        (pointAddInfinityFlag workStart)
        (pointAddCandidate workStart)
        (pointAddSelected workStart)) := by
    apply usesOnly_mono (controlledCopyReg_usesOnly _ _ _)
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with (hcontrol | hcandidate) | hselected
    · subst w
      simpa [pointAddInfinityFlag] using
        pointAddControl_mem_work workStart 0 (by norm_num)
    · exact pointAddCandidate_mem_work workStart w hcandidate
    · exact pointAddSelected_mem_work workStart w hselected
  simp only [infinityPointBranch, circuitUsesOnly_append_iff]
  exact ⟨⟨hload, hcopy⟩, hload⟩

private theorem pointAddBranches_usesOnly_work
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    CircuitUsesOnly (pointAddWork workStart)
      (pointAddBranches workStart hC) := by
  have hgeneric := genericPointBranch_usesOnly_work
    workStart xC yC
  have hdouble := doublePointBranch_usesOnly_work workStart
  have hinfinity := infinityPointBranch_usesOnly_work
    workStart (.some hC)
  simp only [pointAddBranches, circuitUsesOnly_append_iff]
  exact ⟨⟨hgeneric, hdouble⟩, hinfinity⟩

private theorem pointAddCoordinateCopies_usesOnly
    (pointReg : List Wire) (workStart : Wire) :
    CircuitUsesOnly
      (pointReg ++ pointAddWork workStart)
      (pointAddCoordinateCopies pointReg workStart) := by
  have hx : CircuitUsesOnly
      (pointReg ++ pointAddWork workStart)
      (pointAddCopyX pointReg workStart) := by
    rw [pointAddCopyX]
    apply Arithmetic.copyReg_usesOnly
    · intro w hw
      apply List.mem_append_left
      exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
    · intro w hw
      apply List.mem_append_right
      exact pointAddFieldRegister_mem_work workStart _
        (by simp [IsPointAddFieldRegister]) w
        (List.mem_of_mem_take hw)
  have hy : CircuitUsesOnly
      (pointReg ++ pointAddWork workStart)
      (pointAddCopyY pointReg workStart) := by
    rw [pointAddCopyY]
    apply Arithmetic.copyReg_usesOnly
    · intro w hw
      apply List.mem_append_left
      exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
    · intro w hw
      apply List.mem_append_right
      exact pointAddFieldRegister_mem_work workStart _
        (by simp [IsPointAddFieldRegister]) w
        (List.mem_of_mem_take hw)
  rw [pointAddCoordinateCopies]
  exact usesOnly_append hx hy

private theorem pointAddSetup_usesOnly
    (pointReg : List Wire) (workStart : Wire)
    (xC yC : Fp) :
    CircuitUsesOnly
      (pointReg ++ pointAddWork workStart)
      (pointAddSetup pointReg workStart xC yC) := by
  have hcopies := pointAddCoordinateCopies_usesOnly
    pointReg workStart
  have hflags : CircuitUsesOnly
      (pointReg ++ pointAddWork workStart)
      (pointAddFlags pointReg workStart xC yC) := by
    apply usesOnly_mono
      (pointAddFlags_usesOnly pointReg workStart xC yC)
    intro w hw
    simp only [List.mem_append] at hw ⊢
    rcases hw with hpoint | hflag
    · exact Or.inl hpoint
    · exact Or.inr
        (pointAddFlagWork_mem_work workStart w hflag)
  rw [pointAddSetup]
  exact usesOnly_append hcopies hflags

/--
Structural facts needed to reverse `pointAddFiniteCompute`.

Unlike `pointAddFiniteCompute_correct`, this theorem contains no curve
arithmetic.  Its proof is obtained by composing the `HPFree`,
`wellFormed`, and `usesOnly` theorems for:

* `copyReg`,
* `loadConst`,
* `zeroFlag`,
* `equalFlag`,
* `fieldAdd`,
* `fieldSub`,
* `fieldMul`,
* `fieldInv`,
* `controlledCopyReg`.

The last conjunct records that `selected` really belongs to the declared
PointAdd workspace.
-/
theorem pointAddFiniteCompute_structural
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup) :
    let compute :=
      pointAddFiniteCompute pointReg workStart hC
    Classical.HPFree compute ∧
      CircuitWellFormed compute ∧
      CircuitUsesOnly
        (pointReg ++ pointAddWork workStart)
        compute ∧
      (∀ w ∈ pointAddSelected workStart,
        w ∈ pointAddWork workStart) := by
  dsimp only
  have hcopiesFree : Classical.HPFree
      (pointAddCoordinateCopies pointReg workStart) := by
    simp [pointAddCoordinateCopies, pointAddCopyX, pointAddCopyY,
      Arithmetic.copyReg_HPFree]
  have hflagsFree : Classical.HPFree
      (pointAddFlags pointReg workStart xC yC) := by
    simp [pointAddFlags, zeroFlag_HPFree, equalFlag_HPFree,
      loadConst_HPFree]
  have hsetupFree : Classical.HPFree
      (pointAddSetup pointReg workStart xC yC) := by
    rw [pointAddSetup, Classical.hpFree_append]
    exact ⟨hcopiesFree, hflagsFree⟩
  have hgenericFree : Classical.HPFree
      (genericPointBranch workStart xC yC) := by
    simp [genericPointBranch, genericPointCompute_HPFree,
      packFinitePoint_HPFree, controlledCopyReg_HPFree,
      Arithmetic.hpFree_reverse]
  have hdoubleFree : Classical.HPFree
      (doublePointBranch workStart) := by
    simp [doublePointBranch, doublePointCompute_HPFree,
      packFinitePoint_HPFree, controlledCopyReg_HPFree,
      Arithmetic.hpFree_reverse]
  have hinfinityFree : Classical.HPFree
      (infinityPointBranch workStart (.some hC)) := by
    rw [infinityPointBranch, Classical.hpFree_append,
      Classical.hpFree_append]
    exact ⟨⟨loadConst_HPFree _ _, controlledCopyReg_HPFree _ _ _⟩,
      loadConst_HPFree _ _⟩
  have hbranchesFree : Classical.HPFree
      (pointAddBranches workStart hC) := by
    simp only [pointAddBranches, Classical.hpFree_append]
    exact ⟨⟨hgenericFree, hdoubleFree⟩, hinfinityFree⟩
  have hfree : Classical.HPFree
      (pointAddFiniteCompute pointReg workStart hC) := by
    rw [pointAddFiniteCompute, Classical.hpFree_append]
    exact ⟨hsetupFree, hbranchesFree⟩
  have hsetupWellFormed : CircuitWellFormed
      (pointAddSetup pointReg workStart xC yC) := by
    rw [pointAddSetup, circuitWellFormed_append]
    exact ⟨pointAddCoordinateCopies_wellFormed
        pointReg outReg workStart hnodup,
      pointAddFlags_wellFormed
        pointReg outReg workStart xC yC hnodup⟩
  have hbranchesWellFormed : CircuitWellFormed
      (pointAddBranches workStart hC) :=
    pointAddBranches_wellFormed workStart hC
  have hwellFormed : CircuitWellFormed
      (pointAddFiniteCompute pointReg workStart hC) := by
    rw [pointAddFiniteCompute, circuitWellFormed_append]
    exact ⟨hsetupWellFormed, hbranchesWellFormed⟩
  have hsetupUses : CircuitUsesOnly
      (pointReg ++ pointAddWork workStart)
      (pointAddSetup pointReg workStart xC yC) :=
    pointAddSetup_usesOnly pointReg workStart xC yC
  have hbranchesUses : CircuitUsesOnly
      (pointReg ++ pointAddWork workStart)
      (pointAddBranches workStart hC) := by
    apply usesOnly_mono
      (pointAddBranches_usesOnly_work workStart hC)
    intro w hw
    exact List.mem_append_right pointReg hw
  have huses : CircuitUsesOnly
      (pointReg ++ pointAddWork workStart)
      (pointAddFiniteCompute pointReg workStart hC) := by
    rw [pointAddFiniteCompute]
    exact usesOnly_append hsetupUses hbranchesUses
  exact ⟨hfree, hwellFormed, huses,
    pointAddSelected_mem_work workStart⟩

private theorem copyReg_eq_writeReg_of_value_disjoint
    (src dst : List Wire)
    (st : BasisState)
    (value : Nat)
    (hlen : dst.length = src.length)
    (hdstNodup : dst.Nodup)
    (hdisjoint : ModExp.Schedule.WireDisjoint src dst)
    (hclean : Clean dst st)
    (hvalue : regValue src st = value)
    (_hbound : value < 2 ^ dst.length) :
    Classical.run (Arithmetic.copyReg src dst) st =
      writeReg dst value st := by
  have aux :
      ∀ (src dst : List Wire) (st : BasisState),
        dst.length = src.length →
        dst.Nodup →
        ModExp.Schedule.WireDisjoint src dst →
        Clean dst st →
        Classical.run (Arithmetic.copyReg src dst) st =
          writeReg dst (regValue src st) st := by
    intro source
    induction source with
    | nil =>
        intro destination state hlength _ _ _
        have hdestination : destination = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using hlength
        subst destination
        rfl
    | cons sourceHead sourceTail ih =>
        intro destination state hlength hdestinationNodup
          hsourceDestination hdestinationClean
        cases destination with
        | nil =>
            simp at hlength
        | cons destinationHead destinationTail =>
            have hlengthTail :
                destinationTail.length = sourceTail.length := by
              simpa using hlength
            obtain ⟨hdestinationHead, hdestinationTailNodup⟩ :=
              List.nodup_cons.mp hdestinationNodup
            have htailDisjoint :
                ModExp.Schedule.WireDisjoint
                  sourceTail destinationTail := by
              intro a ha b hb
              exact hsourceDestination a
                (List.mem_cons_of_mem sourceHead ha) b
                (List.mem_cons_of_mem destinationHead hb)
            have hdestinationNotSource :
                destinationHead ∉ sourceTail := by
              intro hmem
              exact (hsourceDestination destinationHead
                (List.mem_cons_of_mem sourceHead hmem)
                destinationHead (List.mem_cons_self)) rfl
            let nextState :=
              Classical.applyGate
                (Gate.CX sourceHead destinationHead) state
            have hcleanTail : Clean destinationTail nextState := by
              intro w hw
              change
                state[destinationHead ↦
                  Bool.xor (state destinationHead)
                    (state sourceHead)] w = false
              have hne : w ≠ destinationHead := by
                intro heq
                subst w
                exact hdestinationHead hw
              rw [upd_other _ _ _ hne]
              exact hdestinationClean w
                (List.mem_cons_of_mem destinationHead hw)
            have hsourceKeep :
                regValue sourceTail nextState =
                  regValue sourceTail state := by
              change
                regValue sourceTail
                    (state[destinationHead ↦
                      Bool.xor (state destinationHead)
                        (state sourceHead)]) =
                  regValue sourceTail state
              exact regValue_upd_not_mem sourceTail state
                destinationHead _ hdestinationNotSource
            have hheadBit :
                (regValue (sourceHead :: sourceTail) state).testBit 0 =
                  state sourceHead := by
              rw [regValue_cons, Nat.testBit_zero]
              cases hsourceHead : state sourceHead <;>
                simp [Nat.add_mod]
            have htailValue :
                regValue (sourceHead :: sourceTail) state / 2 =
                  regValue sourceTail state := by
              rw [regValue_cons]
              cases hsourceHead : state sourceHead <;> simp ; omega
            have hnextState :
                nextState =
                  state[destinationHead ↦
                    (regValue
                      (sourceHead :: sourceTail) state).testBit 0] := by
              simp only [nextState, Classical.applyGate]
              rw [hdestinationClean destinationHead
                (List.mem_cons_self)]
              simp [hheadBit]
            have htailRun := ih destinationTail nextState
              hlengthTail hdestinationTailNodup
              htailDisjoint hcleanTail
            rw [Arithmetic.copyReg, Classical.run_cons]
            change
              Classical.run
                  (Arithmetic.copyReg sourceTail destinationTail)
                  nextState =
                writeReg (destinationHead :: destinationTail)
                  (regValue (sourceHead :: sourceTail) state) state
            rw [htailRun, hsourceKeep, writeReg,
              htailValue, ← hnextState]
  calc
    Classical.run (Arithmetic.copyReg src dst) st =
        writeReg dst (regValue src st) st :=
      aux src dst st hlen hdstNodup hdisjoint hclean
    _ = writeReg dst value st := by rw [hvalue]

private theorem writeReg_other
    (ws : List Wire) (value : Nat) (st : BasisState)
    {w : Wire} (hw : w ∉ ws) :
    writeReg ws value st w = st w := by
  induction ws generalizing value st with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at hw
      simp only [writeReg]
      rw [ih (value := value / 2)
        (st := st[head ↦ value.testBit 0]) hw.2]
      exact upd_other st head _ hw.1

private theorem writeReg_agreesOn_register
    (ws : List Wire) (value : Nat)
    (left right : BasisState)
    (hnodup : ws.Nodup) :
    AgreesOn ws
      (writeReg ws value left)
      (writeReg ws value right) := by
  induction ws generalizing value left right with
  | nil =>
      intro w hw
      simp at hw
  | cons head tail ih =>
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      intro w hw
      simp only [writeReg]
      rcases List.mem_cons.mp hw with hwh | hw
      · subst w
        rw [writeReg_other tail (value / 2)
            (left[head ↦ value.testBit 0]) hhead,
          writeReg_other tail (value / 2)
            (right[head ↦ value.testBit 0]) hhead,
          upd_same, upd_same]
      · exact ih (value / 2)
          (left[head ↦ value.testBit 0])
          (right[head ↦ value.testBit 0])
          htail w hw

private theorem run_writeReg_commute
    (circuit : Circuit)
    (active out : List Wire)
    (value : Nat) (st : BasisState)
    (huses : CircuitUsesOnly active circuit)
    (hdisjoint : ModExp.Schedule.WireDisjoint active out)
    (houtNodup : out.Nodup) :
    Classical.run circuit (writeReg out value st) =
      writeReg out value (Classical.run circuit st) := by
  have hwriteActive :
      ∀ w ∈ active, writeReg out value st w = st w := by
    intro w hw
    apply writeReg_other
    intro hout
    exact (hdisjoint w hw w hout) rfl
  have hrunActive :
      ∀ w ∈ active,
        Classical.run circuit (writeReg out value st) w =
          Classical.run circuit st w :=
    CircuitUsesOnly.run_congr huses hwriteActive
  funext w
  by_cases hactive : w ∈ active
  · rw [hrunActive w hactive,
      writeReg_other out value (Classical.run circuit st)]
    intro hout
    exact (hdisjoint w hactive w hout) rfl
  · rw [huses.preservesOutside (writeReg out value st) w hactive]
    by_cases hout : w ∈ out
    · exact (writeReg_agreesOn_register out value st
        (Classical.run circuit st) houtNodup w hout).symm
    · rw [writeReg_other out value st hout,
        writeReg_other out value
          (Classical.run circuit st) hout,
        huses.preservesOutside st w hactive]

/--
Generic Bennett copy-out lemma.

Suppose `compute`

    |input⟩ |0_work⟩
        ↦
    |history⟩

and the register `src`, which lies inside `work`, contains `value` after
the forward computation.

If we do

    compute;
    copyReg src out;
    compute.reverse

then the forward history is erased while the copied value survives in
the disjoint public output register.

Hence the complete state is exactly

    writeReg out value st.

This theorem is completely independent of elliptic curves.
-/
theorem bennett_copyReg_eq_writeReg
    (compute : Circuit)
    (input src out work : List Wire)
    (st : BasisState)
    (value : Nat)
    (hfree : Classical.HPFree compute)
    (hwf : CircuitWellFormed compute)
    (huses :
      CircuitUsesOnly (input ++ work) compute)
    (hsrc :
      ∀ w ∈ src, w ∈ work)
    (hnodup :
      (input ++ out ++ work).Nodup)
    (hlen :
      out.length = src.length)
    (hclean :
      Clean out st)
    (hvalue :
      regValue src (Classical.run compute st) = value)
    (hbound :
      value < 2 ^ out.length) :
    Classical.run
        (circuit! {
          compute;
          Arithmetic.copyReg src out;
          compute.reverse
        })
        st =
      writeReg out value st := by
  obtain ⟨hinputOutNodup, hworkNodup, hinputOutWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨_hinputNodup, houtNodup, hinputOut⟩ :=
    List.nodup_append.mp hinputOutNodup
  have hactiveOut : ModExp.Schedule.WireDisjoint
      (input ++ work) out := by
    intro active hactive output houtput
    rcases List.mem_append.mp hactive with hinput | hwork
    · exact hinputOut active hinput output houtput
    · intro heq
      exact hinputOutWork output
        (List.mem_append_right input houtput)
        active hwork heq.symm
  have hsrcOut : ModExp.Schedule.WireDisjoint src out := by
    intro source hsource output houtput
    exact hactiveOut source
      (List.mem_append_right input (hsrc source hsource))
      output houtput
  let mid := Classical.run compute st
  have hcleanMid : Clean out mid := by
    intro w hw
    calc
      mid w = st w := by
        apply huses.preservesOutside
        intro hactive
        exact (hactiveOut w hactive w hw) rfl
      _ = false := hclean w hw
  have hcopy :
      Classical.run (Arithmetic.copyReg src out) mid =
        writeReg out value mid :=
    copyReg_eq_writeReg_of_value_disjoint
      src out mid value hlen houtNodup hsrcOut
      hcleanMid hvalue hbound
  have hreverseUses :
      CircuitUsesOnly (input ++ work) compute.reverse :=
    usesOnly_reverse huses
  have hcommute :
      Classical.run compute.reverse (writeReg out value mid) =
        writeReg out value
          (Classical.run compute.reverse mid) :=
    run_writeReg_commute compute.reverse (input ++ work)
      out value mid hreverseUses hactiveOut houtNodup
  have hcancel :
      Classical.run compute.reverse mid = st := by
    simpa only [mid] using
      run_reverse_cancel compute st hfree hwf
  simp only [Classical.run_append]
  rw [hcopy, hcommute, hcancel]

theorem pointAddFiniteCompute_agrees_pointReg_core
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean : Clean (pointAddWork workStart) st) :
      AgreesOn pointReg st
        (Classical.run
          (pointAddFiniteCompute pointReg workStart hC) st) := by
  let copied :=
    Classical.run
      (pointAddCoordinateCopies pointReg workStart) st

  have hcopies :=
    pointAddCoordinateCopies_correct
      pointReg outReg workStart st
      hpointLength hnodup hclean

  change
    AgreesOn pointReg st copied ∧
      regValue (pointAddX workStart) copied =
        regValue (PointRegister.x pointReg) st ∧
      regValue (pointAddY workStart) copied =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) copied ∧
      Clean (pointAddBranchWork workStart) copied
    at hcopies

  have hflags :=
    pointAddFlags_semantics
      pointReg outReg workStart
      (xC := xC) (yC := yC)
      copied
      hpointLength hnodup
      hcopies.2.2.2.1
      hcopies.2.2.2.2

  let setup :=
    Classical.run
      (pointAddFlags pointReg workStart xC yC) copied

  change
    AgreesOn pointReg copied setup ∧
      regValue (pointAddX workStart) setup =
        regValue (pointAddX workStart) copied ∧
      regValue (pointAddY workStart) setup =
        regValue (pointAddY workStart) copied ∧
      setup (pointAddInfinityFlag workStart) =
        decide (regValue (PointRegister.tag pointReg) copied = 0) ∧
      setup (pointAddGenericFlag workStart) =
        decide (
          regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
          regValue (PointRegister.x pointReg) copied ≠ xC.val) ∧
      setup (pointAddDoubleFlag workStart) =
        decide (
          regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
          regValue (PointRegister.x pointReg) copied = xC.val ∧
          regValue (PointRegister.y pointReg) copied ≠ (-yC).val) ∧
      Clean (pointAddBranchWork workStart) setup
    at hflags

  have hsetupAgree : AgreesOn pointReg st setup := by
    intro w hw
    exact (hflags.1 w hw).trans (hcopies.1 w hw)

  have hbranchUses :
      CircuitUsesOnly
        (pointAddWork workStart)
        (pointAddBranches workStart hC) :=
    pointAddBranches_usesOnly_work workStart hC

  have hpointWork :
      ∀ w ∈ pointReg, w ∉ pointAddWork workStart := by
    obtain ⟨_, _, hcross⟩ :=
      List.nodup_append.mp hnodup
    intro w hw hww
    exact
      (hcross
        w
        (List.mem_append_left outReg hw)
        w
        hww) rfl

  rw [pointAddFiniteCompute, Classical.run_append]
  intro w hw
  calc
    Classical.run
        (pointAddBranches workStart hC)
        (Classical.run
          (pointAddSetup pointReg workStart xC yC) st) w =
      Classical.run
        (pointAddSetup pointReg workStart xC yC) st w := by
        exact
          hbranchUses.preservesOutside
            (Classical.run
              (pointAddSetup pointReg workStart xC yC) st)
            w
            (hpointWork w hw)
    _ = setup w := by
      simp [pointAddSetup, Classical.run_append, setup, copied]
    _ = st w := hsetupAgree w hw

/-! -------------------------------------------------------------------------
    Final PointAdd correctness
------------------------------------------------------------------------- -/

theorem pointAdd_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C R : Point)
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (houtLength :
      outReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat R)
    (hclean :
      Clean (outReg ++ pointAddWork workStart) st) :
    Classical.run
        (pointAdd pointReg outReg workStart C)
        st =
      writeReg
        outReg
        (encode (R + C)).val
        st := by
  cases C with
  | zero =>
      have hlen : outReg.length = pointReg.length := by
        calc
          outReg.length = pointWidth := houtLength
          _ = pointReg.length := hpointLength.symm

      have hcleanOut : Clean outReg st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_left _ hw)

      have hbound : encodeNat R < 2 ^ outReg.length := by
        rw [houtLength]
        exact encodeNat_lt R

      have hcopy :=
        copyReg_eq_writeReg_of_value
          pointReg
          outReg
          (pointAddWork workStart)
          st
          (encodeNat R)
          hlen
          hnodup
          hcleanOut
          hpoint
          hbound

      change
        Classical.run (Arithmetic.copyReg pointReg outReg) st =
          writeReg outReg (encode (R + 0)).val st
      have henc : (encode (R + 0)).val = encodeNat R := by
        rw [add_zero, encode_val]
      rw [henc]
      exact hcopy

  | some hC =>
      rename_i xC yC

      let compute :=
        pointAddFiniteCompute pointReg workStart hC

      have hcleanWork :
          Clean (pointAddWork workStart) st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_right outReg hw)

      have hcleanOut : Clean outReg st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_left _ hw)

      have hforward :
          regValue
              (pointAddSelected workStart)
              (Classical.run compute st) =
            encodeNat (affineAdd R (.some hC)) := by
        simpa [compute] using
          pointAddFiniteCompute_correct
            pointReg
            outReg
            workStart
            hC
            R
            st
            hpointLength
            hnodup
            hpoint
            hcleanWork

      obtain ⟨hfree, hwf, huses, hselected⟩ :=
        pointAddFiniteCompute_structural
          pointReg
          outReg
          workStart
          hC
          hnodup

      have hlen :
          outReg.length =
            (pointAddSelected workStart).length := by
        simp [pointAddSelected, houtLength, pointWidth]

      have hbound :
          encodeNat (affineAdd R (.some hC)) <
            2 ^ outReg.length := by
        rw [houtLength]
        exact encodeNat_lt (affineAdd R (.some hC))

      have hbennett :=
        bennett_copyReg_eq_writeReg
          compute
          pointReg
          (pointAddSelected workStart)
          outReg
          (pointAddWork workStart)
          st
          (encodeNat (affineAdd R (.some hC)))
          hfree
          hwf
          huses
          hselected
          hnodup
          hlen
          hcleanOut
          hforward
          hbound

      rw [affineAdd_correct] at hbennett
      change
        Classical.run
            (circuit! {
              compute;
              Arithmetic.copyReg
                (pointAddSelected workStart)
                outReg;
              compute.reverse
            })
            st =
          writeReg outReg (encode (R + .some hC)).val st
      have henc :
          (encode (R + .some hC)).val =
            encodeNat (R + .some hC) := by
        rw [encode_val]
      rw [henc]
      simpa only [compute] using hbennett

end Secp256k1
end ShorECDLP
