import ShorECDLP.Submission.«2607_13816».Window.ReducedUniform
import ShorECDLP.Submission.«2607_13816».Window.Kernel
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem right_after_left (s : BasisState) :
    reducedFourierRight.map (fourierClear reducedFourierLeft s)=reducedFourierRight.map s := by
  apply List.map_congr_left
  intro w hw
  rw [fourierClear_apply,if_neg]
  simp only [reducedFourierRight,List.mem_reverse,List.mem_range'_1] at hw
  simp only [reducedFourierLeft,List.mem_reverse,List.mem_range'_1]
  omega

theorem reducedFourierKernel_ket (a b : List Bool) (s : BasisState) :
    measuredFourierKernel .inverse reducedFourierRight b
      (measuredFourierKernel .inverse reducedFourierLeft a (ket s))=
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^464)*
        dyadicFourierKernel .inverse 256 (fourierWordMSB (reducedFourierLeft.map s)) (fourierWordLSB a)*
        dyadicFourierKernel .inverse 208 (fourierWordMSB (reducedFourierRight.map s)) (fourierWordLSB b)) •
      ket (fourierClear reducedFourierRight (fourierClear reducedFourierLeft s)) := by
  rw [measuredFourierKernel_ket,map_smul,measuredFourierKernel_ket,smul_smul,right_after_left]
  have hl : reducedFourierLeft.length=256 := by simp [reducedFourierLeft]
  have hr : reducedFourierRight.length=208 := by simp [reducedFourierRight]
  rw [hl,hr]
  apply congrArg (fun c : ℂ => c • ket (fourierClear reducedFourierRight (fourierClear reducedFourierLeft s)))
  rw [show 464=256+208 from rfl,pow_add]
  ring
/-- The two measurements clear every phase bit and retain only the encoded point. -/
theorem reducedFourierClear_point (R : Point) (bits : List Bool) :
    fourierClear reducedFourierRight (fourierClear reducedFourierLeft
      (pointWrite R (phaseWordState reducedPhaseWires bits zeroBasisState)))=
    pointWrite R zeroBasisState := by
  funext w
  simp only [fourierClear_apply]
  by_cases hp : w∈pointLogicalWires
  · have hbound := pointLogicalWires_bound w hp
    have hl : w∉reducedFourierLeft := by simp only [reducedFourierLeft,List.mem_reverse,List.mem_range'_1]; dsimp only [Wire] at *; omega
    have hr : w∉reducedFourierRight := by simp only [reducedFourierRight,List.mem_reverse,List.mem_range'_1]; dsimp only [Wire] at *; omega
    simp [hl,hr,pointWrite,hp]
  · by_cases hr : w∈reducedFourierRight
    · simp [hr,pointWrite,hp,zeroBasisState]
    · by_cases hl : w∈reducedFourierLeft
      · simp [hl,hr,pointWrite,hp,zeroBasisState]
      · have hw : w∉reducedPhaseWires := by
          simpa only [reducedPhaseWires,List.mem_append,reducedFourierLeft,reducedFourierRight,
            List.mem_reverse,not_or] using And.intro hl hr
        simp only [if_neg hr,if_neg hl,pointWrite,if_neg hp,
          phaseWordState_frame _ _ _ _ hw]

private theorem phase_assignment_words (a b : List Bool) (ha : a.length=256) (hb : b.length=208)
    (s : BasisState) :
    wireValues (List.range' 855 256) (phaseWordState reducedPhaseWires (a++b) s)=a ∧
    wireValues (List.range' 1127 208) (phaseWordState reducedPhaseWires (a++b) s)=b := by
  rw [show reducedPhaseWires=List.range' 855 256++List.range' 1127 208 from rfl,
    phaseWordState_append _ _ a b (by simpa using ha)]
  constructor
  · calc
      _ = wireValues (List.range' 855 256) (phaseWordState (List.range' 855 256) a s) := by
        apply List.map_congr_left
        intro w hw
        apply phaseWordState_frame
        simp only [List.mem_range'_1] at hw ⊢
        omega
      _ = a := phaseWordState_word _ List.nodup_range' a (by simpa using ha) s
  · exact phaseWordState_word _ List.nodup_range' b (by simpa using hb) _

theorem reducedFourierKernel_assigned (P Q : Point) (a b x y : List Bool)
    (ha : a.length=256) (hb : b.length=208) :
    measuredFourierKernel .inverse reducedFourierRight y
      (measuredFourierKernel .inverse reducedFourierLeft x
        (ket (reducedScalarOutput P Q (phaseWordState reducedPhaseWires (a++b) zeroBasisState))))=
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^464)*
        dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x)*
        dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • P+boolWordToNat b • Q) zeroBasisState) := by
  have hv := reducedPhaseWord_inputs a b ha hb zeroBasisState
  have hw := phase_assignment_words a b ha hb zeroBasisState
  rw [reducedScalarOutput,hv.1,hv.2,reducedFourierKernel_ket,reducedFourierClear_point]
  have hl : reducedFourierLeft.map
      (pointWrite (boolWordToNat a • P+boolWordToNat b • Q)
        (phaseWordState reducedPhaseWires (a++b) zeroBasisState))=a.reverse := by
    rw [reducedFourierLeft,List.map_reverse]
    change (wireValues (List.range' 855 256) _).reverse=_
    rw [pointWrite_phase_word _ _ _ _ (by decide),hw.1]
  have hr : reducedFourierRight.map
      (pointWrite (boolWordToNat a • P+boolWordToNat b • Q)
        (phaseWordState reducedPhaseWires (a++b) zeroBasisState))=b.reverse := by
    rw [reducedFourierRight,List.map_reverse]
    change (wireValues (List.range' 1127 208) _).reverse=_
    rw [pointWrite_phase_word _ _ _ _ (by decide),hw.2]
  rw [hl,hr,fourierWordMSB_reverse,fourierWordMSB_reverse]

/-- Explicit point-valued double Fourier sum for each observed pair. -/
theorem reducedWindowTrialOutputMass_point_sum (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (x y : List Bool)
    (hx : x.length=256) (hy : y.length=208) :
    reducedWindowTrialOutputMass P Q hP hQ hrP hrQ x y=
      normSq ((((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) •
        ((fourierOutcomes 256).map (fun a =>
          ((fourierOutcomes 208).map (fun b =>
            (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^464)*
              dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x)*
              dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
            ket (pointWrite (boolWordToNat a • P+boolWordToNat b • Q) zeroBasisState))).sum)).sum) := by
  rw [reducedWindowTrialOutputMass_kernel P Q hP hQ hrP hrQ x y hx hy,reducedPhasePrepare_uniform]
  have hsplit := phaseUniformSum_append (List.range' 855 256) (List.range' 1127 208) zeroBasisState
  change phaseUniformSum reducedPhaseWires zeroBasisState=_ at hsplit
  rw [hsplit]
  simp only [map_smul,stateLinear_list_sum,phaseUniformSum,List.map_map,List.length_range']
  apply congrArg normSq
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  dsimp only [Function.comp_apply]
  simp only [stateLinear_list_sum,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  have halen := (fourierOutcomes_mem _ _).mp ha
  have hblen := (fourierOutcomes_mem _ _).mp hb
  have hassign := phaseWordState_append (List.range' 855 256) (List.range' 1127 208) a b
    (by simpa using halen) zeroBasisState
  change phaseWordState reducedPhaseWires (a++b) zeroBasisState=_ at hassign
  dsimp only [Function.comp_apply]
  rw [←hassign]
  simpa only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single] using
    reducedFourierKernel_assigned P Q a b x y halen hblen

end
end ShorECDLP.Paper2607_13816
