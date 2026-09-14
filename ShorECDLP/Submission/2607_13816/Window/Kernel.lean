import ShorECDLP.Submission.«2607_13816».Window.Uniform
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem clear_apply (ws : List Wire) (s : BasisState) (w : Wire) :
    fourierClear ws s w=if w∈ws then false else s w := by
  induction ws generalizing s with
  | nil => rfl
  | cons v vs ih =>
    rw [fourierClear,ih]
    by_cases hv : w=v
    · subst w; simp [upd]
    · simp [hv,upd]

private theorem kernel_ket (dir : PhaseDir) (ws : List Wire) (bs : List Bool) (s : BasisState) :
    measuredFourierKernel dir ws bs (ket s)=
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^ws.length)*
        dyadicFourierKernel dir ws.length (fourierWordMSB (ws.map s)) (fourierWordLSB bs)) •
      ket (fourierClear ws s) := by
  simp [measuredFourierKernel,ket]

private theorem right_after_left (s : BasisState) :
    scalarFourierRight.map (fourierClear scalarFourierLeft s)=scalarFourierRight.map s := by
  apply List.map_congr_left
  intro w hw
  rw [clear_apply,if_neg]
  simp only [scalarFourierRight,List.mem_reverse,List.mem_range'_1] at hw
  simp only [scalarFourierLeft,List.mem_reverse,List.mem_range'_1]
  omega

theorem scalarFourierKernel_ket (a b : List Bool) (s : BasisState) :
    measuredFourierKernel .inverse scalarFourierRight b
      (measuredFourierKernel .inverse scalarFourierLeft a (ket s))=
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^514)*
        dyadicFourierKernel .inverse 257 (fourierWordMSB (scalarFourierLeft.map s)) (fourierWordLSB a)*
        dyadicFourierKernel .inverse 257 (fourierWordMSB (scalarFourierRight.map s)) (fourierWordLSB b)) •
      ket (fourierClear scalarFourierRight (fourierClear scalarFourierLeft s)) := by
  rw [kernel_ket,map_smul,kernel_ket,smul_smul,right_after_left]
  have hl : scalarFourierLeft.length=257 := by simp [scalarFourierLeft]
  have hr : scalarFourierRight.length=257 := by simp [scalarFourierRight]
  rw [hl,hr]
  apply congrArg (fun c : ℂ => c • ket (fourierClear scalarFourierRight (fourierClear scalarFourierLeft s)))
  rw [show 514=257+257 from rfl,pow_add]
  ring
private theorem point_bound (w : Wire) (hw : w∈pointLogicalWires) : w<839 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at hw
  dsimp only [Wire] at *
  omega

/-- The two measurements clear every phase bit and retain only the encoded point. -/
theorem scalarFourierClear_point (R : Point) (bits : List Bool) :
    fourierClear scalarFourierRight (fourierClear scalarFourierLeft
      (pointWrite R (phaseWordState scalarPhaseWires bits zeroBasisState)))=
    pointWrite R zeroBasisState := by
  funext w
  simp only [clear_apply]
  by_cases hp : w∈pointLogicalWires
  · have hbound := point_bound w hp
    have hl : w∉scalarFourierLeft := by simp only [scalarFourierLeft,List.mem_reverse,List.mem_range'_1]; dsimp only [Wire] at *; omega
    have hr : w∉scalarFourierRight := by simp only [scalarFourierRight,List.mem_reverse,List.mem_range'_1]; dsimp only [Wire] at *; omega
    simp [hl,hr,pointWrite,hp]
  · by_cases hr : w∈scalarFourierRight
    · simp [hr,pointWrite,hp,zeroBasisState]
    · by_cases hl : w∈scalarFourierLeft
      · simp [hl,hr,pointWrite,hp,zeroBasisState]
      · have hw : w∉scalarPhaseWires := by
          simpa only [scalarPhaseWires,List.mem_append,scalarFourierLeft,scalarFourierRight,
            List.mem_reverse,not_or] using And.intro hl hr
        simp only [if_neg hr,if_neg hl,pointWrite,if_neg hp,
          phaseWordState_frame _ _ _ _ hw]

private theorem msb_append (a b : List Bool) :
    fourierWordMSB (a++b)=2^b.length*fourierWordMSB a+fourierWordMSB b := by
  induction a with
  | nil => simp [fourierWordMSB]
  | cons x xs ih => simp [fourierWordMSB,ih,pow_add]; ring

theorem fourierWordMSB_reverse (bs : List Bool) :
    fourierWordMSB bs.reverse=boolWordToNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.reverse_cons,msb_append,List.length_singleton,fourierWordMSB,
      List.length_nil,pow_zero,Nat.one_mul,Nat.add_zero,ih,boolWordToNat]
    omega

private theorem phase_assignment_words (a b : List Bool) (ha : a.length=257) (hb : b.length=257)
    (s : BasisState) :
    wireValues (List.range' 855 257) (phaseWordState scalarPhaseWires (a++b) s)=a ∧
    wireValues (List.range' 1127 257) (phaseWordState scalarPhaseWires (a++b) s)=b := by
  rw [show scalarPhaseWires=List.range' 855 257++List.range' 1127 257 from rfl,
    phaseWordState_append _ _ a b (by simpa using ha)]
  constructor
  · calc
      _ = wireValues (List.range' 855 257) (phaseWordState (List.range' 855 257) a s) := by
        apply List.map_congr_left
        intro w hw
        apply phaseWordState_frame
        simp only [List.mem_range'_1] at hw ⊢
        omega
      _ = a := phaseWordState_word _ List.nodup_range' a (by simpa using ha) s
  · exact phaseWordState_word _ List.nodup_range' b (by simpa using hb) _

private theorem phase_point_word (R : Point) (s : BasisState) (start : Nat) (hstart : 839≤start) :
    wireValues (List.range' start 257) (pointWrite R s)=wireValues (List.range' start 257) s := by
  apply List.map_congr_left
  intro w hw
  apply pointWrite_frame
  intro hp
  have hb := point_bound w hp
  simp only [List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem scalarFourierKernel_assigned (P Q : Point) (a b x y : List Bool)
    (ha : a.length=257) (hb : b.length=257) :
    measuredFourierKernel .inverse scalarFourierRight y
      (measuredFourierKernel .inverse scalarFourierLeft x
        (ket (scalarRegisterOutput P Q (phaseWordState scalarPhaseWires (a++b) zeroBasisState))))=
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^514)*
        dyadicFourierKernel .inverse 257 (boolWordToNat a) (fourierWordLSB x)*
        dyadicFourierKernel .inverse 257 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • P+boolWordToNat b • Q) zeroBasisState) := by
  have hv := scalarPhaseWord_inputs a b ha hb zeroBasisState
  have hw := phase_assignment_words a b ha hb zeroBasisState
  rw [scalarRegisterOutput,hv.1,hv.2,scalarFourierKernel_ket,scalarFourierClear_point]
  have hl : scalarFourierLeft.map
      (pointWrite (boolWordToNat a • P+boolWordToNat b • Q)
        (phaseWordState scalarPhaseWires (a++b) zeroBasisState))=a.reverse := by
    rw [scalarFourierLeft,List.map_reverse]
    change (wireValues (List.range' 855 257) _).reverse=_
    rw [phase_point_word _ _ _ (by decide),hw.1]
  have hr : scalarFourierRight.map
      (pointWrite (boolWordToNat a • P+boolWordToNat b • Q)
        (phaseWordState scalarPhaseWires (a++b) zeroBasisState))=b.reverse := by
    rw [scalarFourierRight,List.map_reverse]
    change (wireValues (List.range' 1127 257) _).reverse=_
    rw [phase_point_word _ _ _ (by decide),hw.2]
  rw [hl,hr,fourierWordMSB_reverse,fourierWordMSB_reverse]

private theorem linear_sum (L : State →ₗ[ℂ] State) (xs : List State) : L xs.sum=(xs.map L).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Explicit point-valued double Fourier sum for each observed pair. -/
theorem windowTrialOutputMass_point_sum (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (x y : List Bool)
    (hx : x.length=257) (hy : y.length=257) :
    windowTrialOutputMass P Q hP hQ hrP hrQ x y=
      normSq ((((((Real.sqrt 2)⁻¹:ℝ):ℂ))^514) •
        ((fourierOutcomes 257).map (fun a =>
          ((fourierOutcomes 257).map (fun b =>
            (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^514)*
              dyadicFourierKernel .inverse 257 (boolWordToNat a) (fourierWordLSB x)*
              dyadicFourierKernel .inverse 257 (boolWordToNat b) (fourierWordLSB y)) •
            ket (pointWrite (boolWordToNat a • P+boolWordToNat b • Q) zeroBasisState))).sum)).sum) := by
  rw [windowTrialOutputMass_kernel P Q hP hQ hrP hrQ x y hx hy,scalarPhasePrepare_uniform]
  have hsplit := phaseUniformSum_append (List.range' 855 257) (List.range' 1127 257) zeroBasisState
  change phaseUniformSum scalarPhaseWires zeroBasisState=_ at hsplit
  rw [hsplit]
  simp only [map_smul,linear_sum,phaseUniformSum,List.map_map,List.length_range']
  apply congrArg normSq
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^514) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  dsimp only [Function.comp_apply]
  simp only [linear_sum,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  have halen := (fourierOutcomes_mem _ _).mp ha
  have hblen := (fourierOutcomes_mem _ _).mp hb
  have hassign := phaseWordState_append (List.range' 855 257) (List.range' 1127 257) a b
    (by simpa using halen) zeroBasisState
  change phaseWordState scalarPhaseWires (a++b) zeroBasisState=_ at hassign
  dsimp only [Function.comp_apply]
  rw [←hassign]
  simpa only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single] using
    scalarFourierKernel_assigned P Q a b x y halen hblen

end
end ShorECDLP.Paper2607_13816
