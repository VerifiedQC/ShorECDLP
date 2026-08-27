import ShorECDLP.Submission.Arithmetic.Controlled_PointAdd
import ShorECDLP.Submission.EllipticCurve.Precompute

namespace ShorECDLP
namespace Secp256k1

open Classical
open Arithmetic
open scoped ArithmeticNotation

variable [Fact (Nat.Prime p)]

/-!
# Controlled scalar multiplication

This file builds scalar multiplication from the verified controlled point-addition
circuit.

Suppose the scalar register contains the binary expansion

    a = a₀ + 2 a₁ + 4 a₂ + ...

where `a₀` is the first wire of `scalarReg`.

For a fixed classical elliptic-curve point `P`, precomputation gives the table

    P, 2P, 4P, 8P, ...

The quantum circuit then performs

    if a₀ = 1: R ← R + P
    if a₁ = 1: R ← R + 2P
    if a₂ = 1: R ← R + 4P
    ...

Therefore the final accumulator is

    R + a • P.

The important implementation fact is that every `controlledPointAdd` restores its
workspace. Hence all scalar bits can reuse one copy of `controlledPointAddWork`;
we do not need a separate point-add workspace for every scalar bit.
-/

/-! ## Workspace -/

/--
The scalar-multiplication circuit reuses exactly the workspace required by one
controlled point addition.

Every invocation of `controlledPointAdd` cleans this workspace before returning,
so it is safe to reuse for the next scalar bit.
-/
def scalarMulWork (workStart : Wire) : List Wire :=
  controlledPointAddWork workStart

/-! ## Generic controlled-add loop -/

/--
`scalarMulCore` applies a sequence of controlled constant-point translations.

The two input lists are interpreted in parallel:

    controls = [c₀, c₁, ..., cₙ]
    points   = [P₀, P₁, ..., Pₙ]

and the circuit performs

    R ← R + c₀ P₀
    R ← R + c₁ P₁
    ...
    R ← R + cₙ Pₙ.

Here `cᵢ Pᵢ` means `Pᵢ` when the control bit is `1`, and the identity point
when the control bit is `0`.

This definition is intentionally generic. The actual scalar-multiplication
circuit below specializes `points` to

    [P, 2P, 4P, 8P, ...].
-/
def scalarMulCore
    (pointReg : List Wire)
    (workStart : Wire) :
    List Wire → List Point → Circuit
  | control :: controls, C :: Cs =>
      controlledPointAdd control pointReg workStart C ++
        scalarMulCore pointReg workStart controls Cs
  | _, _ =>
      []

/-! ## Classical doubling table -/

/--
The classical points used by scalar multiplication.

For a scalar register of width `n`, this contains

    [P, 2P, 4P, ..., 2^(n-1) P].

These are classical constants used when constructing the circuit; no quantum
point-doubling circuit is required.
-/
def scalarMulTable
    (scalarReg : List Wire)
    (P : Point) : List Point :=
  Precompute.doublingTable scalarReg.length P

/-! ## Scalar-multiplication circuit -/

/--
In-place scalar multiplication/addition.

If the scalar register contains `a` and the point register contains `R`, then
the intended action is

    |a⟩ |R⟩ |0work⟩
        ↦
    |a⟩ |R + a • P⟩ |0work⟩.

The scalar register is never modified. It is used only as the collection of
control wires for the calls to `controlledPointAdd`.
-/
def scalarMul
    (scalarReg pointReg : List Wire)
    (workStart : Wire)
    (P : Point) : Circuit :=
  scalarMulCore
    pointReg
    workStart
    scalarReg
    (scalarMulTable scalarReg P)

/--
The point obtained by selecting each classical point whose corresponding
control wire is `true`.

For example,

  controlledPointSum [c₀, c₁] [P₀, P₁] st
    = (if st c₀ then P₀ else 0) +
      (if st c₁ then P₁ else 0).
-/
def controlledPointSum :
    List Wire → List Point → BasisState → Point
  | c :: cs, P :: Ps, st =>
      (if st c then P else 0) + controlledPointSum cs Ps st
  | _, _, _ => 0

set_option linter.unusedSectionVars false in

/--
Writing the value already represented by a register leaves the basis state
unchanged.
-/
theorem writeReg_eq_self_of_regValue
    (reg : List Wire)
    (value : Nat)
    (st : BasisState)
    (hnodup : reg.Nodup)
    (hvalue : regValue reg st = value) :
    writeReg reg value st = st := by
  induction reg generalizing value st with
  | nil =>
      simp at hvalue
      subst value
      rfl
  | cons w ws ih =>
      have hw : w ∉ ws :=
        (List.nodup_cons.mp hnodup).1
      have hws : ws.Nodup :=
        (List.nodup_cons.mp hnodup).2

      have hbit :
          value.testBit 0 = st w := by
        rw [← hvalue, regValue_cons, Nat.testBit_zero]
        cases st w <;> simp [Nat.add_mod]

      have hdiv :
          value / 2 = regValue ws st := by
        rw [← hvalue, regValue_cons]
        cases st w
        · simp
        · simp
          omega

      have hsame :
          st[w ↦ st w] = st := by
        funext i
        by_cases hi : i = w
        · subst i
          simp [upd]
        · simp [upd, hi]

      simp only [writeReg]
      rw [hbit, hdiv, hsame]
      exact ih (regValue ws st) st hws rfl

/--
The genuine induction step for `scalarMulCore`.

The first controlled addition changes

  R ↦ controlledPointResult (st control) R C,

after which the induction hypothesis is applied to the remaining controls and
points. Since `controlledPointAdd_correct` changes only `pointReg`, the
remaining control bits and the clean workspace are preserved.
-/
theorem scalarMulCore_cons_step
    (control : Wire)
    (controls pointReg : List Wire)
    (C : Point)
    (points : List Point)
    (workStart : Wire)
    (R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      ((control :: controls) ++
        pointReg ++ scalarMulWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean : Clean (scalarMulWork workStart) st)
    (htail :
      ∀ (R' : Point) (st' : BasisState),
        (controls ++ pointReg ++ scalarMulWork workStart).Nodup →
        regValue pointReg st' = encodeNat R' →
        Clean (scalarMulWork workStart) st' →
        Classical.run
            (scalarMulCore pointReg workStart controls points) st' =
          writeReg pointReg
            (encode
              (R' + controlledPointSum controls points st')).val
            st') :
    Classical.run
        (scalarMulCore pointReg workStart
          (control :: controls) (C :: points)) st =
      writeReg pointReg
        (encode
          (R +
            controlledPointSum
              (control :: controls) (C :: points) st)).val
        st := by
  have writeReg_other_local :
      ∀ (ws : List Wire) (n : Nat) (s : BasisState) (i : Wire),
        i ∉ ws → writeReg ws n s i = s i := by
    intro ws
    induction ws with
    | nil => intros; rfl
    | cons w ws ih =>
        intro n s i h
        simp only [List.mem_cons, not_or] at h
        simp only [writeReg]
        rw [ih (n / 2) (s[w ↦ n.testBit 0]) i h.2]
        exact upd_other s w (n.testBit 0) h.1

  have writeReg_upd_not_mem_local :
      ∀ (ws : List Wire) (n : Nat) (s : BasisState)
        (i : Wire) (b : Bool),
        i ∉ ws →
        writeReg ws n (s[i ↦ b]) =
          (writeReg ws n s)[i ↦ b] := by
    intro ws
    induction ws with
    | nil => intros; rfl
    | cons w ws ih =>
        intro n s i b h
        simp only [List.mem_cons, not_or] at h
        simp only [writeReg]
        have hcomm :
            (s[i ↦ b])[w ↦ n.testBit 0] =
              (s[w ↦ n.testBit 0])[i ↦ b] := by
          funext j
          by_cases hji : j = i <;>
            by_cases hjw : j = w <;>
              simp [upd, hji, hjw, h.1, Ne.symm h.1]
        rw [hcomm]
        exact ih (n / 2) (s[w ↦ n.testBit 0]) i b h.2

  have writeReg_overwrite_local :
      ∀ (ws : List Wire) (n m : Nat) (s : BasisState),
        ws.Nodup →
        writeReg ws n (writeReg ws m s) = writeReg ws n s := by
    intro ws
    induction ws with
    | nil => intros; rfl
    | cons w ws ih =>
        intro n m s hnd
        have hw := (List.nodup_cons.mp hnd).1
        have hnd' := (List.nodup_cons.mp hnd).2
        simp only [writeReg]
        rw [← writeReg_upd_not_mem_local
          ws (m / 2) (s[w ↦ m.testBit 0]) w (n.testBit 0) hw]
        have hover :
            (s[w ↦ m.testBit 0])[w ↦ n.testBit 0] =
              s[w ↦ n.testBit 0] := by
          funext j
          by_cases hj : j = w <;> simp [upd, hj]
        rw [hover]
        exact ih (n / 2) (m / 2) (s[w ↦ n.testBit 0]) hnd'

  have regValue_writeReg_local :
      ∀ (ws : List Wire) (n : Nat) (s : BasisState),
        ws.Nodup →
        n < 2 ^ ws.length →
        regValue ws (writeReg ws n s) = n := by
    intro ws
    induction ws with
    | nil =>
        intro n s hnd hn
        simp at hn
        subst n
        rfl
    | cons w ws ih =>
        intro n s hnd hn
        have hw := (List.nodup_cons.mp hnd).1
        have hnd' := (List.nodup_cons.mp hnd).2
        have hn2 : n < 2 ^ ws.length * 2 := by
          simpa [pow_succ] using hn
        have hn' : n / 2 < 2 ^ ws.length := by omega

        simp only [writeReg, regValue_cons]
        rw [writeReg_other_local
          ws (n / 2) (s[w ↦ n.testBit 0]) w hw]
        rw [upd_same, ih (n / 2) (s[w ↦ n.testBit 0]) hnd' hn']

        have hbit :
            (if n.testBit 0 then 1 else 0) = n % 2 := by
          cases hb : n.testBit 0 with
          | false =>
              have hm : n % 2 = 0 :=
                (Nat.mod_two_eq_zero_iff_testBit_zero).2 hb
              simp [hm]
          | true =>
              have hm : n % 2 = 1 :=
                (Nat.mod_two_eq_one_iff_testBit_zero).2 hb
              simp [ hm]

        rw [hbit]
        have hsplit := Nat.mod_add_div n 2
        omega

  have controlledPointSum_congr_local :
      ∀ (cs : List Wire) (Ps : List Point)
        (s₁ s₂ : BasisState),
        (∀ w ∈ cs, s₁ w = s₂ w) →
        controlledPointSum cs Ps s₁ =
          controlledPointSum cs Ps s₂ := by
    intro cs
    induction cs with
    | nil =>
      intro Ps s₁ s₂ h
      cases Ps <;> rfl
    | cons c cs ih =>
      intro Ps s₁ s₂ h
      cases Ps with
      | nil => rfl
      | cons P Ps =>
          change
            (if s₁ c then P else 0) +
                controlledPointSum cs Ps s₁ =
              (if s₂ c then P else 0) +
                controlledPointSum cs Ps s₂
          rw [h c (List.mem_cons_self)]
          rw [ih Ps s₁ s₂]
          intro w hw
          exact h w (List.mem_cons_of_mem c hw)

  have hndRight :
      ((control :: controls) ++
        (pointReg ++ scalarMulWork workStart)).Nodup := by
    simpa [List.append_assoc] using hnodup

  obtain ⟨hcontrolsAllNd, hrestNd, hcontrolsRestCross⟩ :=
    List.nodup_append.mp hndRight

  have hcontrolsNd : controls.Nodup :=
    (List.nodup_cons.mp hcontrolsAllNd).2

  obtain ⟨hpointNd, hworkNd, hpointWorkCross⟩ :=
    List.nodup_append.mp hrestNd

  have hcontrolRest :
      control ∉ pointReg ++ scalarMulWork workStart := by
    intro h
    exact
      (hcontrolsRestCross
        control (List.mem_cons_self)
        control h) rfl

  have hcontrolsRest :
      ∀ w ∈ controls,
        ∀ u ∈ pointReg ++ scalarMulWork workStart,
          w ≠ u := by
    intro w hw u hu
    exact
      hcontrolsRestCross
        w (List.mem_cons_of_mem control hw) u hu

  have hfirstNd :
      ([control] ++ pointReg ++ scalarMulWork workStart).Nodup := by
    have h :
        (control ::
          (pointReg ++ scalarMulWork workStart)).Nodup :=
      List.nodup_cons.mpr ⟨hcontrolRest, hrestNd⟩
    simpa [List.append_assoc] using h

  have htailNd :
      (controls ++ pointReg ++ scalarMulWork workStart).Nodup := by
    have h :
        (controls ++
          (pointReg ++ scalarMulWork workStart)).Nodup := by
      apply List.nodup_append.mpr
      exact ⟨hcontrolsNd, hrestNd, hcontrolsRest⟩
    simpa [List.append_assoc] using h

  let R' := controlledPointResult (st control) R C
  let st' := writeReg pointReg (encodeNat R') st

  have hfirst :
      Classical.run
          (controlledPointAdd control pointReg workStart C) st =
        st' := by
    have h :=
      controlledPointAdd_correct
        control pointReg workStart C R st
        hpointLength
        (by simpa [scalarMulWork] using hfirstNd)
        hpoint
        (by simpa [scalarMulWork] using hclean)
    rw [encode_val] at h
    change
      Classical.run
          (controlledPointAdd control pointReg workStart C) st =
        st'
      at h
    exact h

  have hR'Bound : encodeNat R' < 2 ^ pointReg.length := by
    rw [hpointLength]
    exact encodeNat_lt R'

  have hpoint' :
      regValue pointReg st' = encodeNat R' := by
    exact regValue_writeReg_local
      pointReg (encodeNat R') st hpointNd hR'Bound

  have hworkOutside :
      ∀ w ∈ scalarMulWork workStart, w ∉ pointReg := by
    intro w hw hp
    exact (hpointWorkCross w hp w hw) rfl

  have hclean' :
      Clean (scalarMulWork workStart) st' := by
    intro w hw
    change writeReg pointReg (encodeNat R') st w = false
    rw [writeReg_other_local
      pointReg (encodeNat R') st w (hworkOutside w hw)]
    exact hclean w hw

  have hcontrolsOutside :
      ∀ w ∈ controls, w ∉ pointReg := by
    intro w hw hp
    exact
      (hcontrolsRest w hw
        w (List.mem_append_left _ hp)) rfl

  have hcontrolsAgree :
      ∀ w ∈ controls, st' w = st w := by
    intro w hw
    change writeReg pointReg (encodeNat R') st w = st w
    exact writeReg_other_local
      pointReg (encodeNat R') st w (hcontrolsOutside w hw)

  have hsum :
      controlledPointSum controls points st' =
        controlledPointSum controls points st :=
    controlledPointSum_congr_local
      controls points st' st hcontrolsAgree

  have htailRun :=
    htail R' st' htailNd hpoint' hclean'

  rw [hsum] at htailRun

  have hpointExpr :
      R' + controlledPointSum controls points st =
        R + controlledPointSum
          (control :: controls) (C :: points) st := by
    rw [show
      controlledPointSum
          (control :: controls) (C :: points) st =
        (if st control then C else 0) +
          controlledPointSum controls points st by rfl]
    cases hc : st control
    · dsimp [R', controlledPointResult]
      rw [hc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [zero_add]
    · dsimp [R', controlledPointResult]
      rw [hc]
      simp only [↓reduceIte]
      rw [add_assoc]

  rw [hpointExpr] at htailRun

  have hoverwrite :
      writeReg pointReg
          (encode
            (R + controlledPointSum
              (control :: controls) (C :: points) st)).val
          st' =
        writeReg pointReg
          (encode
            (R + controlledPointSum
              (control :: controls) (C :: points) st)).val
          st := by
    change
      writeReg pointReg
          (encode
            (R + controlledPointSum
              (control :: controls) (C :: points) st)).val
          (writeReg pointReg (encodeNat R') st) =
        _
    exact writeReg_overwrite_local
      pointReg
      (encode
        (R + controlledPointSum
          (control :: controls) (C :: points) st)).val
      (encodeNat R')
      st
      hpointNd

  simp only [scalarMulCore, Classical.run_append]
  rw [hfirst, htailRun]
  exact hoverwrite

theorem scalarMulCore_correct
    (controls pointReg : List Wire)
    (points : List Point)
    (workStart : Wire)
    (R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (controls ++ pointReg ++ scalarMulWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean : Clean (scalarMulWork workStart) st) :
    Classical.run
        (scalarMulCore pointReg workStart controls points) st =
      writeReg pointReg
        (encode (R + controlledPointSum controls points st)).val st := by
  induction controls generalizing points R st with
  | nil =>
      cases points with
      | nil =>
          change st =
            writeReg pointReg (encode (R + 0)).val st
          rw [add_zero, encode_val]
          have hpointNd : pointReg.Nodup := by
            exact (List.nodup_append.mp (by simpa using hnodup)).1
          exact
            (writeReg_eq_self_of_regValue
              pointReg (encodeNat R) st hpointNd hpoint).symm
      | cons _ _ =>
          change st =
            writeReg pointReg (encode (R + 0)).val st
          rw [add_zero, encode_val]
          have hpointNd : pointReg.Nodup := by
            exact (List.nodup_append.mp (by simpa using hnodup)).1
          exact
            (writeReg_eq_self_of_regValue
              pointReg (encodeNat R) st hpointNd hpoint).symm

  | cons control controls ih =>
      cases points with
      | nil =>
          change st =
            writeReg pointReg (encode (R + 0)).val st
          rw [add_zero, encode_val]
          have hpointNd : pointReg.Nodup := by
            obtain ⟨hprefix, _, _⟩ :=
              List.nodup_append.mp hnodup
            exact (List.nodup_append.mp hprefix).2.1
          exact
            (writeReg_eq_self_of_regValue
              pointReg (encodeNat R) st hpointNd hpoint).symm

      | cons C points =>
          apply scalarMulCore_cons_step
            control controls pointReg C points workStart R st
            hpointLength hnodup hpoint hclean

          intro R' st' hnodup' hpoint' hclean'
          exact ih points R' st' hnodup' hpoint' hclean'

theorem scalarMulTable_cons
    (w : Wire)
    (ws : List Wire)
    (P : Point) :
    scalarMulTable (w :: ws) P =
      P :: scalarMulTable ws (2 • P) := by
  simp [scalarMulTable, Precompute.doublingTable]
  funext i
  rw [Nat.pow_succ, two_nsmul, nsmul_add,
    ← add_nsmul, Nat.mul_two]

theorem controlledPointSum_scalarMulTable
    (scalarReg : List Wire)
    (P : Point)
    (st : BasisState) :
    controlledPointSum
        scalarReg
        (scalarMulTable scalarReg P)
        st =
      (regValue scalarReg st) • P := by
  induction scalarReg generalizing P with
  | nil =>
      change 0 = (0 : Nat) • P
      rw [zero_nsmul]

  | cons w ws ih =>
      rw [scalarMulTable_cons]
      change
        (if st w then P else 0) +
            controlledPointSum ws (scalarMulTable ws (2 • P)) st =
          ((if st w then 1 else 0) + 2 * regValue ws st) • P
      rw [ih (P := 2 • P)]
      cases hw : st w
      · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        rw [two_nsmul, nsmul_add, ← add_nsmul, Nat.two_mul]
      · simp only [↓reduceIte]
        rw [two_nsmul, nsmul_add, ← add_nsmul, Nat.two_mul]
        conv_rhs => rw [add_nsmul, one_nsmul]

/-! ## Exact T-count -/

private theorem scalarMulCore_tCount_of_all_ne_zero
    (controls pointReg : List Wire)
    (points : List Point)
    (workStart : Wire)
    (hpointLength : pointReg.length = pointWidth)
    (hlength : points.length = controls.length)
    (hnonzero : ∀ C ∈ points, C ≠ 0) :
    tCount (scalarMulCore pointReg workStart controls points) =
      1644262771060 * controls.length := by
  induction controls generalizing points with
  | nil =>
      simp [scalarMulCore]
  | cons control controls ih =>
      cases points with
      | nil => simp at hlength
      | cons C points =>
          have hC : C ≠ 0 := hnonzero C (by simp)
          have htail : ∀ D ∈ points, D ≠ 0 := by
            intro D hD
            exact hnonzero D (by simp [hD])
          have hlengthTail : points.length = controls.length := by
            simpa using hlength
          rw [scalarMulCore, tCount_append,
            controlledPointAdd_tCount_of_ne_zero
              control pointReg workStart C hC hpointLength,
            ih points hlengthTail htail]
          simp only [List.length_cons]
          omega

/--
Exact T-count of scalar multiplication when every precomputed classical
doubling-table entry is finite.
-/
theorem scalarMul_tCount_of_table_ne_zero
    (scalarReg pointReg : List Wire)
    (workStart : Wire)
    (P : Point)
    (hpointLength : pointReg.length = pointWidth)
    (hnonzero : ∀ C ∈ scalarMulTable scalarReg P, C ≠ 0) :
    tCount (scalarMul scalarReg pointReg workStart P) =
      1644262771060 * scalarReg.length := by
  exact scalarMulCore_tCount_of_all_ne_zero
    scalarReg pointReg (scalarMulTable scalarReg P) workStart
    hpointLength (by simp [scalarMulTable]) hnonzero

/-! ## Structural lemmas -/

omit [Fact (Nat.Prime p)] in
/-- Every generic scalar-fold circuit is H/P-free. -/
private theorem scalarMulCore_HPFree
    (controls pointReg : List Wire)
    (points : List Point)
    (workStart : Wire) :
    Classical.HPFree
      (scalarMulCore pointReg workStart controls points) := by
  induction controls generalizing points with
  | nil =>
      cases points <;> simp [scalarMulCore]
  | cons control controls ih =>
      cases points with
      | nil => simp [scalarMulCore]
      | cons C points =>
          simp [scalarMulCore, controlledPointAdd_HPFree, ih]

omit [Fact (Nat.Prime p)] in
/--
Every generic scalar-fold circuit is well formed when all control wires, the
point register, and the shared controlled-add workspace are disjoint.
-/
private theorem scalarMulCore_wellFormed
    (controls pointReg : List Wire)
    (points : List Point)
    (workStart : Wire)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (controls ++ pointReg ++ scalarMulWork workStart).Nodup) :
    CircuitWellFormed
      (scalarMulCore pointReg workStart controls points) := by
  induction controls generalizing points with
  | nil =>
      cases points <;> simp [scalarMulCore]
  | cons control controls ih =>
      cases points with
      | nil => simp [scalarMulCore]
      | cons C points =>
          have h0 :
              (control ::
                (controls ++ pointReg ++ scalarMulWork workStart)).Nodup := by
            simpa [List.append_assoc] using hnodup
          have htail :
              (controls ++ pointReg ++ scalarMulWork workStart).Nodup :=
            (List.nodup_cons.mp h0).2
          have hrest :
              (pointReg ++ scalarMulWork workStart).Nodup := by
            have hassoc :
                (controls ++
                  (pointReg ++ scalarMulWork workStart)).Nodup := by
              simpa [List.append_assoc] using htail
            exact (List.nodup_append.mp hassoc).2.1
          have hcontrolNotRest :
              control ∉ pointReg ++ scalarMulWork workStart := by
            intro hw
            apply (List.nodup_cons.mp h0).1
            simpa [List.append_assoc] using
              (List.mem_append_right controls hw)
          have hhead :
              ([control] ++ pointReg ++ scalarMulWork workStart).Nodup := by
            have hc :
                (control ::
                  (pointReg ++ scalarMulWork workStart)).Nodup :=
              List.nodup_cons.mpr ⟨hcontrolNotRest, hrest⟩
            simpa [List.append_assoc] using hc
          rw [scalarMulCore, circuitWellFormed_append]
          exact ⟨controlledPointAdd_wellFormed
              control pointReg workStart C hpointLength
              (by simpa [scalarMulWork] using hhead),
            ih points htail⟩

/-- The concrete doubling-table scalar multiplication is H/P-free. -/
theorem scalarMul_HPFree
    (scalarReg pointReg : List Wire)
    (workStart : Wire)
    (P : Point) :
    Classical.HPFree
      (scalarMul scalarReg pointReg workStart P) := by
  exact scalarMulCore_HPFree
    scalarReg pointReg (scalarMulTable scalarReg P) workStart

/--
The concrete doubling-table scalar multiplication is well formed under the
same register-layout hypothesis used by `scalarMul_correct`.
-/
theorem scalarMul_wellFormed
    (scalarReg pointReg : List Wire)
    (workStart : Wire)
    (P : Point)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (scalarReg ++ pointReg ++ scalarMulWork workStart).Nodup) :
    CircuitWellFormed
      (scalarMul scalarReg pointReg workStart P) := by
  exact scalarMulCore_wellFormed
    scalarReg pointReg (scalarMulTable scalarReg P) workStart
    hpointLength hnodup
/-!
## Correctness theorem

This is the main theorem that `ECDLPOracle.lean` will use.

The assumptions have the same shape as `controlledPointAdd_correct`:

* `pointReg` has the correct width;
* the scalar register, point register, and workspace are disjoint;
* the point register initially encodes `R`;
* the reusable scalar-multiplication workspace starts clean.

The conclusion is deliberately a whole-state equality rather than merely a
statement about `regValue`.

Thus the theorem says simultaneously that:

* `pointReg` becomes `R + a • P`;
* `scalarReg` is unchanged;
* all workspace wires are returned to zero;
* every unrelated wire is unchanged.

The proof should proceed by induction through `scalarReg` and the doubling
table, applying `controlledPointAdd_correct` at each step.

The mathematical identity used by the induction is

    (a₀ + 2a') • P
      = a₀ • P + a' • (2 • P),

which matches the LSB-first definition of `regValue`.
-/
theorem scalarMul_correct
    (scalarReg pointReg : List Wire)
    (workStart : Wire)
    (P R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup : (scalarReg ++ pointReg ++ scalarMulWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean : Clean (scalarMulWork workStart) st) :
    Classical.run (scalarMul scalarReg pointReg workStart P) st
    =
    writeReg pointReg (encode (R + (regValue scalarReg st) • P)).val st := by
  change
    Classical.run
        (scalarMulCore pointReg workStart scalarReg
          (scalarMulTable scalarReg P)) st =
      writeReg pointReg
        (encode (R + (regValue scalarReg st) • P)).val st
  rw [← controlledPointSum_scalarMulTable scalarReg P st]
  exact scalarMulCore_correct scalarReg pointReg
    (scalarMulTable scalarReg P) workStart R st
    hpointLength hnodup hpoint hclean

end Secp256k1
end ShorECDLP
