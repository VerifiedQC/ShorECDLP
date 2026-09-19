import ShorECDLP.Submission.«2607_13816».Window.RawScalar
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

private theorem end_append (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (as bs : List Nat)
    (A : Point) (s : BasisState) :
    rawAlgebraicEnd x y hc (as++bs) A s=rawAlgebraicEnd x y hc bs (rawAlgebraicEnd x y hc as A s) s := by
  induction as generalizing A with
  | nil => rfl
  | cons j js ih => simp only [List.cons_append,rawAlgebraicEnd,ih]

private theorem end_congr (x y u v : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a))
    (hd : ∀ j a, curve.toAffine.Nonsingular (u j a) (v j a)) (js : List Nat)
    (s : BasisState) (he : ∀ j∈js, preparedWindowDelta x y hc j s=preparedWindowDelta u v hd j s)
    (A : Point) : rawAlgebraicEnd x y hc js A s=rawAlgebraicEnd u v hd js A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih =>
    simp only [rawAlgebraicEnd,he j (by simp)]
    exact ih (fun k hk => he k (by simp [hk])) _

private theorem end_range (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat)
    (A : Point) (s : BasisState) :
    rawAlgebraicEnd x y hc (List.range' j n) A s=A+preparedWindowSum x y hc n j s := by
  induction n generalizing j A with
  | zero => simp [rawAlgebraicEnd,preparedWindowSum]
  | succ n ih => simp only [List.range'_succ,rawAlgebraicEnd,ih,preparedWindowSum,add_assoc]

private theorem table_valid (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (j a : Nat) :
    curve.toAffine.Nonsingular (reducedRawX P Q j a) (reducedRawY P Q j a) := by
  unfold reducedRawX reducedRawY
  split
  · exact oddWindowTable_valid P hP hrP j a
  · exact oddWindowTable_valid Q hQ hrQ (j-17) a

private theorem end_two_axes (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    reducedRawEnd P Q hP hQ hrP hrQ s =
      reducedRawInitialPoint P Q s+
        preparedWindowSum (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
          (fun k => oddWindowTable_valid P hP hrP (k-0)) 15 1 s+
        preparedWindowSum (fun k => oddWindowX Q (k-17)) (fun k => oddWindowY Q (k-17))
          (fun k => oddWindowTable_valid Q hQ hrQ (k-17)) 13 17 s := by
  let hc := table_valid P Q hP hQ hrP hrQ
  have ep := end_congr (reducedRawX P Q) (reducedRawY P Q)
    (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0)) hc
    (fun k => oddWindowTable_valid P hP hrP (k-0)) (List.range' 1 15) s (by
      intro j hj
      have hj' : j<17 := by simp only [List.mem_range'_1] at hj; omega
      simp only [preparedWindowDelta,windowPointDelta,reducedRawX,reducedRawY,if_pos hj',Nat.sub_zero])
  have eq := end_congr (reducedRawX P Q) (reducedRawY P Q)
    (fun k => oddWindowX Q (k-17)) (fun k => oddWindowY Q (k-17)) hc
    (fun k => oddWindowTable_valid Q hQ hrQ (k-17)) (List.range' 17 13) s (by
      intro j hj
      have hj' : ¬j<17 := by simp only [List.mem_range'_1] at hj; omega
      simp only [preparedWindowDelta,windowPointDelta,reducedRawX,reducedRawY,if_neg hj'])
  change rawAlgebraicEnd _ _ hc (List.range' 1 15++List.range' 17 13) _ s=_
  rw [end_append,ep,eq,end_range,end_range]

/-- The concrete algebraic walk equals the two physical scalar registers.
This identity does not assert that the raw circuit is valid on every input. -/
theorem reducedRawEnd_registers (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) (hs : PointInitializeValid s) :
    reducedRawEnd P Q hP hQ hrP hrQ s=
      scalarRegisterValue 16 0 s • P+scalarRegisterValue 13 17 s • Q := by
  let A := axisWindowOffset P 16+axisWindowOffset Q 13
  let I := reducedRawInitialPoint P Q s
  let xp := fun k => oddWindowX P (k-0)
  let yp := fun k => oddWindowY P (k-0)
  let cp := fun k => oddWindowTable_valid P hP hrP (k-0)
  let xq := fun k => oddWindowX Q (k-17)
  let yq := fun k => oddWindowY Q (k-17)
  let cq := fun k => oddWindowTable_valid Q hQ hrQ (k-17)
  have hv := (rawInitialState_ready A P s hs).1
  change PointLookupValid (pointWrite I s) at hv
  have hp := preparedWindowScheduleState_correct xp yp cp 15 1 I (pointWrite I s)
    hv (pointWrite_coordinates I s)
  rw [preparedWindowSum_pointWrite,pointWrite_overwrite] at hp
  have hvp := (preparedWindowScheduleState_ready xp yp cp 15 1 (pointWrite I s)
    ⟨hv,I,pointWrite_coordinates I s⟩).1
  rw [hp] at hvp
  have hq := preparedWindowScheduleState_correct xq yq cq 13 17
    (I+preparedWindowSum xp yp cp 15 1 s) _ hvp (pointWrite_coordinates _ s)
  rw [preparedWindowSum_pointWrite,pointWrite_overwrite] at hq
  have hstate : reducedScalarState P Q hP hQ hrP hrQ s=
      pointWrite (reducedRawEnd P Q hP hQ hrP hrQ s) s := by
    change axisWindowState Q hQ hrQ 17 13 (axisWindowState P hP hrP 0 16 (pointWrite A s))=_
    rw [axisWindowState_split P hP hrP 15,firstWindowState_correct A P hP hrP s hs]
    change preparedWindowScheduleState xq yq cq 13 17
      (preparedWindowScheduleState xp yp cp 15 1 (pointWrite I s))=_
    rw [hp,hq,end_two_axes]
  apply pointWrite_injective s
  exact hstate.symm.trans (reducedScalarState_registers P Q hP hQ hrP hrQ s hs)

/-- The repair-free circuit computes the physical scalar-register expression
coherently on clean inputs satisfying the explicit path exclusions. -/
theorem reducedRaw_registers_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (reducedRawProgram P Q)
      (Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q))
      (fun s => PointInitializeValid s ∧ reducedRawExclusions P Q hP hQ hrP hrQ s) := by
  apply (reducedRaw_coherent P Q hP hQ hrP hrQ).congrIdeal
  intro s hs
  simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,
    reducedRawEnd_registers P Q hP hQ hrP hrQ s hs.1,reducedScalarOutput]

end
end ShorECDLP.Paper2607_13816
