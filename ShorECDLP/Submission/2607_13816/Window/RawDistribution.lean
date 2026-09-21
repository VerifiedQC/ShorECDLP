import ShorECDLP.Submission.«2607_13816».Window.RawRoot
import ShorECDLP.Submission.«2607_13816».Window.ReducedSuccess
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem outcome_sum (n : Nat) (f : List Bool → ℝ) :
    ((fourierOutcomes n).map f).sum=∑ v : Fin (2^n), f (paperOutcomeBits n v) := by
  rw [←List.sum_toFinset _ (fourierOutcomes_nodup n)]
  symm
  apply Finset.sum_bij (fun v _ => paperOutcomeBits n v)
  · intro v _
    exact List.mem_toFinset.mpr ((fourierOutcomes_mem n _).mpr (paperOutcomeBits_length n v))
  · intro a _ b _ h
    exact paperOutcomeBits_injective n h
  · intro bs hbs
    have hl := (fourierOutcomes_mem n bs).mp (List.mem_toFinset.mp hbs)
    have hv : fourierWordLSB bs < 2^n := by simpa [hl] using fourierWordLSB_lt bs
    refine ⟨⟨fourierWordLSB bs,hv⟩,Finset.mem_univ _,?_⟩
    apply fourierWordLSB_injective _ _
    · rw [paperOutcomeBits_length,hl]
    · exact paperOutcomeBits_word n _
  · intro _ _; rfl

private theorem filtered_flat_mass {α : Type} (xs : List α) (f : α → Instrument)
    (p : InstrumentBranch → Bool) (ψ : State) :
    Instrument.bornMass ((xs.flatMap f).filter p) ψ =
      (xs.map (fun x => Instrument.bornMass ((f x).filter p) ψ)).sum := by
  induction xs with
  | nil => simp [Instrument.bornMass]
  | cons a xs ih =>
    simpa [Instrument.bornMass, List.filter_append] using
      congrArg (Instrument.bornMass ((f a).filter p) ψ + ·) ih

/-- Partition selected actual Fourier histories into the finite output pairs. -/
theorem reducedFourierSelection_partition (accept : List Bool × List Bool → Bool) (ψ : State) :
    (reducedFourierSelection accept).bornMass ψ =
    ∑ out : Fin (2^256) × Fin (2^208),
      if accept (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) then
        (reducedFourierSlice (paperOutcomeBits 256 out.1) (paperOutcomeBits 208 out.2)).bornMass ψ
      else 0 := by
  unfold reducedFourierSelection
  rw [reducedFourierProgram_run, filtered_flat_mass]
  simp_rw [filtered_flat_mass, outcome_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hd : decodeReducedFourier (paperOutcomeBits 256 a ++ paperOutcomeBits 208 b)=
      (paperOutcomeBits 256 a,paperOutcomeBits 208 b) := by
    unfold decodeReducedFourier
    have h (xs ys : List Bool) : (List.take xs.length (xs++ys),List.drop xs.length (xs++ys))=(xs,ys) := by simp
    simpa only [paperOutcomeBits_length] using h (paperOutcomeBits 256 a) (paperOutcomeBits 208 b)
  by_cases h : accept (paperOutcomeBits 256 a,paperOutcomeBits 208 b)=true <;>
    simp [reducedFourierSlice, Instrument.bornMass, hd, h]

/-- Full ideal accepted mass is the existing physical Fourier distribution, with the same event. -/
theorem reducedRawIdealFourierEventMass_distribution (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (accept : List Bool × List Bool → Bool) :
    reducedRawIdealFourierEventMass P Q accept =
    ∑ out : Fin (2^256) × Fin (2^208),
      if accept (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) then
        reducedWindowTrialFiniteOutputMass P Q hP hQ hrP hrQ out else 0 := by
  rw [reducedRawIdealFourierEventMass_root, reducedFourierSelection_partition]
  apply Finset.sum_congr rfl
  intro out _
  split_ifs
  · unfold reducedWindowTrialFiniteOutputMass
    rw [reducedWindowTrialOutputMass_kernel P Q hP hQ hrP hrQ _ _
      (paperOutcomeBits_length _ _) (paperOutcomeBits_length _ _)]
    simp only [reducedFourierSlice, Instrument.bornMass, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, LinearMap.comp_apply]
    rw [fourierBranch_eq_kernel, fourierBranch_eq_kernel] <;>
      simp [reducedFourierLeft, reducedFourierRight, List.nodup_range']
  · rfl
/-- Public decoder acceptance is precisely verified success for the promised public point. -/
theorem reducedRawIdealDecoder_eq (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    reducedRawIdealFourierEventMass G Q (reducedRawDecoderAccept Q)=
      reducedPhysicalVerifiedMass Q hG hQ hrQ d := by
  rw [reducedRawIdealFourierEventMass_distribution G Q hG hQ generator_nsmul_eq_zero hrQ]
  unfold reducedPhysicalVerifiedMass
  apply Finset.sum_congr rfl
  intro out _
  have he : reducedRawDecoderAccept Q (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2)=true ↔
      reducedVerifiedCandidate Q out=some (d:ZMod order) := by
    rw [reducedRawDecoderAccept_correct Q d hQd]
    simp [reducedRawPublicDecode]
  simp only [he]

end
end ShorECDLP.Paper2607_13816
