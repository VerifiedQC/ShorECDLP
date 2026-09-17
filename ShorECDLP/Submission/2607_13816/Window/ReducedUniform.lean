import ShorECDLP.Submission.«2607_13816».Window.ReducedOutcomes
import ShorECDLP.Submission.«2607_13816».Window.Uniform
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
theorem reducedPhasePrepare_uniform : Quantum.run reducedPhasePrepare (ket zeroBasisState)=
    (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) • phaseUniformSum reducedPhaseWires zeroBasisState := by
  have hz := reducedWindowTrial_zero_initial.2
  have h := phaseHadamards_uniform reducedPhaseWires (by decide +kernel) zeroBasisState hz
  simpa only [reducedPhaseWires,List.length_append,List.length_range'] using h
/-- An explicit finite amplitude sum, with interference retained inside each Fourier row. -/
theorem reducedWindowTrialOutputMass_uniform (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=256) (hb : b.length=208) :
    reducedWindowTrialOutputMass P Q hP hQ hrP hrQ a b=
      normSq ((((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) •
        (((fourierOutcomes 464).map (fun bits =>
          measuredFourierKernel .inverse reducedFourierRight b
            (measuredFourierKernel .inverse reducedFourierLeft a
              (ket (reducedScalarOutput P Q (phaseWordState reducedPhaseWires bits zeroBasisState)))))).sum)) := by
  rw [reducedWindowTrialOutputMass_kernel P Q hP hQ hrP hrQ a b ha hb,reducedPhasePrepare_uniform]
  simp only [map_smul,phaseUniformSum,stateLinear_list_sum,List.map_map]
  apply congrArg normSq
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) • ψ)
  have hl : reducedPhaseWires.length=464 := by
    simp only [reducedPhaseWires,List.length_append,List.length_range']
  rw [hl]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bits _
  simp [Function.comp_def,ket]

/-- The two input registers receive their actual emitted assignment words. -/
theorem reducedPhaseWord_inputs (a b : List Bool) (ha : a.length=256) (hb : b.length=208)
    (s : BasisState) :
    scalarRegisterValue 16 0 (phaseWordState reducedPhaseWires (a++b) s)=boolWordToNat a ∧
    scalarRegisterValue 13 17 (phaseWordState reducedPhaseWires (a++b) s)=boolWordToNat b := by
  have hsplit := phaseWordState_append (List.range' 855 256) (List.range' 1127 208) a b
    (by simpa using ha) s
  change phaseWordState reducedPhaseWires (a++b) s=_ at hsplit
  rw [hsplit]
  have hleft : wireValues (List.range' 855 256)
      (phaseWordState (List.range' 1127 208) b (phaseWordState (List.range' 855 256) a s))=a := by
    calc
      _ = wireValues (List.range' 855 256) (phaseWordState (List.range' 855 256) a s) := by
        apply List.map_congr_left
        intro w hw
        apply phaseWordState_frame
        simp only [List.mem_range'_1] at hw ⊢
        omega
      _ = a := phaseWordState_word _ (List.nodup_range') a (by simpa using ha) s
  have hright := phaseWordState_word (List.range' 1127 208) (List.nodup_range') b
    (by simpa using hb) (phaseWordState (List.range' 855 256) a s)
  constructor
  · change boolWordToNat (wireValues (List.range' 855 256) _)=_
    rw [hleft]
  · change boolWordToNat (wireValues (List.range' 1127 208) _)=_
    rw [hright]

end
end ShorECDLP.Paper2607_13816
