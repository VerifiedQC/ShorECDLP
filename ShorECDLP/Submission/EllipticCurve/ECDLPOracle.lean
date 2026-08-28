import ShorECDLP.Submission.Arithmetic.ScalarMul
import ShorECDLP.Submission.OrderFinding.OracleRefinement

/-!
# Concrete secp256k1 ECDLP oracle

The oracle is the direct composition of two proved additive scalar-
multiplication circuits.  Starting from a point accumulator `R`, the first
call adds `a • P` and the second adds `b • Q`:

```text
R ↦ R + a • P ↦ R + a • P + b • Q.
```

Both calls reuse the same `scalarMulWork` register because each call restores
that workspace exactly.  The final theorem refines this classical whole-state
equation through `ECDLPOracleSpec.ofCircuit`; no additional quantum argument is
needed here.
-/

namespace ShorECDLP
namespace Secp256k1

open Classical

variable [Fact (Nat.Prime p)]

/-- Add `a • P + b • Q` to the encoded point accumulator. -/
def ecdlpOracle
    (aReg bReg pointReg : List Wire)
    (workStart : Wire)
    (P Q : Point) : Circuit :=
  scalarMul aReg pointReg workStart P ++
    scalarMul bReg pointReg workStart Q

/--
Exact T-count of the two-scalar-multiplication oracle when both classical
doubling tables contain only finite points.
-/
theorem ecdlpOracle_tCount_of_tables_ne_zero
    (aReg bReg pointReg : List Wire)
    (workStart : Wire)
    (P Q : Point)
    (hpointLength : pointReg.length = pointWidth)
    (hP : ∀ C ∈ scalarMulTable aReg P, C ≠ 0)
    (hQ : ∀ C ∈ scalarMulTable bReg Q, C ≠ 0) :
    tCount (ecdlpOracle aReg bReg pointReg workStart P Q) =
      1644262771060 * (aReg.length + bReg.length) := by
  rw [ecdlpOracle, tCount_append,
    scalarMul_tCount_of_table_ne_zero
      aReg pointReg workStart P hpointLength hP,
    scalarMul_tCount_of_table_ne_zero
      bReg pointReg workStart Q hpointLength hQ]
  omega

omit [Fact (Nat.Prime p)] in
private theorem writeReg_apply_not_mem
    (reg : List Wire) (value : Nat) (st : BasisState)
    {w : Wire} (hw : w ∉ reg) :
    writeReg reg value st w = st w := by
  induction reg generalizing value st with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.mem_cons, not_or] at hw
      simp only [writeReg]
      rw [ih (value := value / 2)
        (st := st[q ↦ value.testBit 0]) hw.2]
      exact upd_other st q _ hw.1

omit [Fact (Nat.Prime p)] in
private theorem regValue_writeReg_disjoint
    (readReg writeRegWires : List Wire)
    (value : Nat)
    (st : BasisState)
    (hdisjoint : List.Disjoint readReg writeRegWires) :
    regValue readReg (writeReg writeRegWires value st) =
      regValue readReg st := by
  induction readReg with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ writeRegWires := by
        intro hmem
        exact (List.disjoint_left.mp hdisjoint)
          (List.mem_cons_self) hmem
      have htail : List.Disjoint ws writeRegWires := by
        rw [List.disjoint_left]
        intro q hq hmem
        exact (List.disjoint_left.mp hdisjoint)
          (List.mem_cons_of_mem w hq) hmem
      rw [regValue_cons, regValue_cons]
      rw [writeReg_apply_not_mem writeRegWires value st hw]
      exact congrArg (fun n => (if st w then 1 else 0) + 2 * n)
        (ih htail)

omit [Fact (Nat.Prime p)] in
private theorem writeReg_upd_not_mem
    (reg : List Wire) (value : Nat) (st : BasisState)
    (w : Wire) (bit : Bool) (hw : w ∉ reg) :
    writeReg reg value st[w ↦ bit] =
      (writeReg reg value st)[w ↦ bit] := by
  have upd_comm
      (s : BasisState) (i j : Wire) (bi bj : Bool)
      (hij : i ≠ j) :
      (s[i ↦ bi])[j ↦ bj] = (s[j ↦ bj])[i ↦ bi] := by
    funext q
    by_cases hqi : q = i
    · subst q
      simp [upd, hij]
    · by_cases hqj : q = j
      · subst q
        simp [upd, hqi]
      · simp [upd, hqi, hqj]

  induction reg generalizing value st with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.mem_cons, not_or] at hw
      simp only [writeReg]
      rw [upd_comm st w q bit (value.testBit 0) hw.1]
      exact ih (value := value / 2)
        (st := st[q ↦ value.testBit 0]) hw.2

omit [Fact (Nat.Prime p)] in
private theorem writeReg_overwrite
    (reg : List Wire) (oldValue newValue : Nat)
    (st : BasisState)
    (hnodup : reg.Nodup) :
    writeReg reg newValue (writeReg reg oldValue st) =
      writeReg reg newValue st := by
  induction reg generalizing oldValue newValue st with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.mp hnodup).1
      have hws : ws.Nodup := (List.nodup_cons.mp hnodup).2
      simp only [writeReg]
      rw [← writeReg_upd_not_mem ws (oldValue / 2)
        (st[w ↦ oldValue.testBit 0]) w
        (newValue.testBit 0) hw]
      rw [ih (oldValue := oldValue / 2)
        (newValue := newValue / 2)
        (st := (st[w ↦ oldValue.testBit 0])
          [w ↦ newValue.testBit 0]) hws]
      congr 1
      funext q
      by_cases hq : q = w
      · subst q
        simp
      · simp [upd, hq]

omit [Fact (Nat.Prime p)] in
private theorem scalarCall_nodup
    (aReg bReg pointReg work : List Wire)
    (hnodup : (aReg ++ bReg ++ pointReg ++ work).Nodup) :
    (aReg ++ pointReg ++ work).Nodup ∧
      (bReg ++ pointReg ++ work).Nodup := by
  have hfull :
      (aReg ++ (bReg ++ (pointReg ++ work))).Nodup := by
    simpa only [List.append_assoc] using hnodup
  constructor
  · have hsub :
        (aReg ++ (pointReg ++ work)).Sublist
          (aReg ++ (bReg ++ (pointReg ++ work))) :=
      (List.Sublist.refl aReg).append
        ((List.nil_sublist bReg).append_right (pointReg ++ work))
    have h := List.Nodup.sublist hsub hfull
    simpa only [List.append_assoc] using h
  · have hsub :
        (bReg ++ (pointReg ++ work)).Sublist
          (aReg ++ (bReg ++ (pointReg ++ work))) :=
      (List.nil_sublist aReg).append_right
        (bReg ++ (pointReg ++ work))
    have h := List.Nodup.sublist hsub hfull
    simpa only [List.append_assoc] using h

/--
The exact classical action of the two-call ECDLP oracle.  This whole-state
equality also states that both scalar registers, the shared workspace, and
every wire outside `pointReg` are restored.
-/
theorem ecdlpOracle_correct
    (aReg bReg pointReg : List Wire)
    (workStart : Wire)
    (P Q R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean : Clean (scalarMulWork workStart) st) :
    Classical.run
        (ecdlpOracle aReg bReg pointReg workStart P Q) st =
      writeReg pointReg
        (encode
          (R + ecdlpFunction P Q
            (regValue aReg st) (regValue bReg st))).val st := by
  let work := scalarMulWork workStart
  let afterFirst :=
    writeReg pointReg
      (encode (R + (regValue aReg st) • P)).val st

  obtain ⟨haNodup, hbNodup⟩ :=
    scalarCall_nodup aReg bReg pointReg work hnodup

  have hpointWorkNodup : (pointReg ++ work).Nodup := by
    have hright :
        (bReg ++ (pointReg ++ work)).Nodup := by
      simpa only [List.append_assoc] using hbNodup
    exact (List.nodup_append.mp hright).2.1

  obtain ⟨hpointNodup, _, hpointWorkDisjoint⟩ :=
    List.nodup_append.mp hpointWorkNodup

  have hbPointDisjoint : List.Disjoint bReg pointReg := by
    have hright :
        (bReg ++ (pointReg ++ work)).Nodup := by
      simpa only [List.append_assoc] using hbNodup
    have hcross := (List.nodup_append.mp hright).2.2
    rw [List.disjoint_left]
    intro w hwB hwPoint
    exact hcross w hwB w (List.mem_append_left work hwPoint) rfl

  have hworkPointDisjoint : List.Disjoint work pointReg := by
    rw [List.disjoint_left]
    intro w hwWork hwPoint
    exact hpointWorkDisjoint w hwPoint w hwWork rfl

  have hfirst :
      Classical.run (scalarMul aReg pointReg workStart P) st =
        afterFirst := by
    exact scalarMul_correct aReg pointReg workStart P R st
      hpointLength (by simpa [work] using haNodup) hpoint hclean

  have hpointAfterFirst :
      regValue pointReg afterFirst =
        encodeNat (R + (regValue aReg st) • P) := by
    dsimp [afterFirst]
    exact PointRegister.regValue_write_encode
      pointReg (R + (regValue aReg st) • P) st
      hpointLength hpointNodup

  have hbAfterFirst :
      regValue bReg afterFirst = regValue bReg st := by
    dsimp [afterFirst]
    exact regValue_writeReg_disjoint
      bReg pointReg
      (encode (R + (regValue aReg st) • P)).val st
      hbPointDisjoint

  have hcleanAfterFirst : Clean work afterFirst := by
    intro w hw
    dsimp [afterFirst]
    rw [writeReg_apply_not_mem pointReg
      (encodeNat (R + (regValue aReg st) • P)) st
      ((List.disjoint_left.mp hworkPointDisjoint) hw)]
    exact hclean w (by simpa [work] using hw)

  have hsecond :
      Classical.run (scalarMul bReg pointReg workStart Q) afterFirst =
        writeReg pointReg
          (encode
            ((R + (regValue aReg st) • P) +
              (regValue bReg st) • Q)).val afterFirst := by
    have h :=
      scalarMul_correct bReg pointReg workStart Q
        (R + (regValue aReg st) • P) afterFirst
        hpointLength
        (by simpa [work] using hbNodup)
        hpointAfterFirst
        (by simpa [work] using hcleanAfterFirst)
    rw [hbAfterFirst] at h
    exact h

  rw [ecdlpOracle, Classical.run_append, hfirst, hsecond]
  rw [writeReg_overwrite pointReg
    (encode (R + (regValue aReg st) • P)).val
    (encode
      ((R + (regValue aReg st) • P) +
        (regValue bReg st) • Q)).val st hpointNodup]
  simp only [ecdlpFunction, add_assoc]

/-- The two-call oracle stays inside its two scalar registers, point
accumulator, and shared scalar-multiplication workspace. -/
theorem ecdlpOracle_usesOnly
    (aReg bReg pointReg : List Wire)
    (workStart : Wire)
    (P Q : Point) :
    CircuitUsesOnly
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart)
      (ecdlpOracle aReg bReg pointReg workStart P Q) := by
  rw [ecdlpOracle]
  apply Arithmetic.usesOnly_append
  · apply Arithmetic.usesOnly_mono
      (scalarMul_usesOnly aReg pointReg workStart P)
    intro w hw
    simp only [List.mem_append] at hw ⊢
    rcases hw with (ha | hpoint) | hwork
    · exact Or.inl (Or.inl (Or.inl ha))
    · exact Or.inl (Or.inr hpoint)
    · exact Or.inr hwork
  · apply Arithmetic.usesOnly_mono
      (scalarMul_usesOnly bReg pointReg workStart Q)
    intro w hw
    simp only [List.mem_append] at hw ⊢
    rcases hw with (hb | hpoint) | hwork
    · exact Or.inl (Or.inl (Or.inr hb))
    · exact Or.inl (Or.inr hpoint)
    · exact Or.inr hwork

/-- The exact concrete oracle circuit is H/P-free. -/
theorem ecdlpOracle_HPFree
    (aReg bReg pointReg : List Wire)
    (workStart : Wire)
    (P Q : Point) :
    Classical.HPFree
      (ecdlpOracle aReg bReg pointReg workStart P Q) := by
  rw [ecdlpOracle, Classical.hpFree_append]
  exact ⟨scalarMul_HPFree aReg pointReg workStart P,
    scalarMul_HPFree bReg pointReg workStart Q⟩

/-- The exact concrete oracle circuit is well formed on a disjoint layout. -/
theorem ecdlpOracle_wellFormed
    (aReg bReg pointReg : List Wire)
    (workStart : Wire)
    (P Q : Point)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup) :
    CircuitWellFormed
      (ecdlpOracle aReg bReg pointReg workStart P Q) := by
  obtain ⟨haNodup, hbNodup⟩ :=
    scalarCall_nodup aReg bReg pointReg
      (scalarMulWork workStart) hnodup
  rw [ecdlpOracle, circuitWellFormed_append]
  exact ⟨
    scalarMul_wellFormed aReg pointReg workStart P
      hpointLength
      (by simpa using haNodup),
    scalarMul_wellFormed bReg pointReg workStart Q
      hpointLength
      (by simpa using hbNodup)
  ⟩

/-- Refine the concrete circuit into the oracle specification used by order finding. -/
theorem ecdlpOracle_spec
    (aReg bReg pointReg : List Wire)
    (workStart : Wire)
    (P Q : Point)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup) :
    ECDLPOracleSpec pointEncoding
      (Quantum.run (ecdlpOracle aReg bReg pointReg workStart P Q))
      P Q aReg bReg pointReg (scalarMulWork workStart) := by
  apply ECDLPOracleSpec.ofCircuit
  · exact hpointLength
  · exact hnodup
  · exact ecdlpOracle_HPFree aReg bReg pointReg workStart P Q
  · exact ecdlpOracle_wellFormed
      aReg bReg pointReg workStart P Q hpointLength hnodup
  · intro st a b R ha hb hpoint hclean
    have h := ecdlpOracle_correct
      aReg bReg pointReg workStart P Q R st
      hpointLength hnodup
      (by simpa only [pointEncoding_encode_val] using hpoint)
      hclean
    rw [ha, hb] at h
    simpa only [pointEncoding_encode_val, encode_val] using h

end Secp256k1
end ShorECDLP
