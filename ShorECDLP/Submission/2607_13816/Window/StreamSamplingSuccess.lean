import ShorECDLP.Submission.«2607_13816».Window.StreamAssignedKernel
import ShorECDLP.Submission.«2607_13816».Window.RawSuccess
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
open scoped BigOperators
noncomputable section
theorem streamFourierKernel_point_sum (P Q : Point) (x y : List Bool) :
    measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) y
      (measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) x
        (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q) (streamPreparedEntry P Q))) =
      ((((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) •
        ((fourierOutcomes 256).map (fun a =>
          ((fourierOutcomes 208).map (fun b =>
            (((((Real.sqrt 2)⁻¹:ℝ):ℂ)^464)*
              dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x)*
              dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
            ket (pointWrite (boolWordToNat a • P+boolWordToNat b • Q)
              (scalarRootFlip zeroBasisState)))).sum)).sum) := by
  rw [streamPreparedEntry_uniform,phaseUniformSum_append]
  have hl : (streamScalarWires 16 1).reverse.length=256 := by decide +kernel
  have hr : (streamScalarWires 13 17).reverse.length=208 := by decide +kernel
  simp only [map_smul,phaseUniformSum,stateLinear_list_sum,List.map_map,hl,hr]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^464) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  dsimp only [Function.comp_apply]
  simp only [stateLinear_list_sum,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  have halen := (fourierOutcomes_mem 256 a).mp ha
  have hblen := (fourierOutcomes_mem 208 b).mp hb
  have hassign := phaseWordState_append (streamScalarWires 16 1).reverse
    (streamScalarWires 13 17).reverse a b (halen.trans hl.symm) (scalarRootFlip zeroBasisState)
  dsimp only [Function.comp_apply]
  rw [← hassign]
  simpa only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single] using
    streamFourierKernel_assigned P Q a b x y halen hblen
theorem streamFourierKernel_outputMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (x y : List Bool)
    (hx : x.length=256) (hy : y.length=208) :
    normSq (measuredFourierKernel .inverse
      (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) y
      (measuredFourierKernel .inverse
        (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) x
        (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q) (streamPreparedEntry P Q)))) =
      reducedWindowTrialOutputMass P Q hP hQ hrP hrQ x y := by
  rw [streamFourierKernel_point_sum,reducedWindowTrialOutputMass_point_sum P Q hP hQ hrP hrQ x y hx hy]
  symm
  rw [← scalarRootFlip_normSq]
  apply congrArg normSq
  simp only [map_smul,stateLinear_list_sum,List.map_map,Function.comp_def]
  simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,scalarRootFlip_pointWrite]

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


theorem streamIdealFourierEventMass_eq (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (accept : List Bool × List Bool → Bool) :
    streamFourierKernelEventMass P Q accept
      (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q) (streamPreparedEntry P Q)) =
      reducedRawIdealFourierEventMass P Q accept := by
  rw [streamFourierKernelEventMass,
    reducedRawIdealFourierEventMass_distribution P Q hP hQ hrP hrQ]
  simp_rw [outcome_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact streamFourierKernel_outputMass P Q hP hQ hrP hrQ _ _
      (paperOutcomeBits_length _ _) (paperOutcomeBits_length _ _)
  · rfl

theorem streamRawDecoder_success (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (2:ℝ)/25 ≤ streamRawFourierEventMass G Q (reducedRawDecoderAccept Q) := by
  have hb := streamRawFourierEventMass_ideal_lower G Q hG hQ generator_nsmul_eq_zero hrQ
    (reducedRawDecoderAccept Q)
  rw [streamIdealFourierEventMass_eq G Q hG hQ generator_nsmul_eq_zero hrQ,
    reducedRawIdealDecoder_eq Q hG hQ hrQ d hQd] at hb
  have hi := secpSuccessBound_numeric.trans (reducedPhysicalVerifiedMass_lower Q hG hQ hrQ d hQd)
  linarith

theorem streamRawPublicDecode_success (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (2:ℝ)/25 ≤ Instrument.bornMass ((streamRawTrial G Q).run.filter
      (fun b => (streamRawPublicDecode Q b.history).isSome)) (ket zeroBasisState) := by
  rw [streamRawPublicDecode_eventMass]
  exact streamRawDecoder_success Q hG hQ hrQ d hQd

theorem streamRawTrial_success_certificate (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (streamRawTrial G Q).qubitCount ≤ 855 ∧
    (streamRawTrial G Q).measurementCount = 847701655 ∧
    (2:ℝ)/25 ≤ Instrument.bornMass ((streamRawTrial G Q).run.filter
      (fun b => (streamRawPublicDecode Q b.history).isSome)) (ket zeroBasisState) ∧
    (∀ hist c, streamRawPublicDecode Q hist=some c → c=(d:ZMod order)) :=
  ⟨streamRawTrial_qubitCount G Q,streamRawTrial_measurementCount G Q,
    streamRawPublicDecode_success Q hG hQ hrQ d hQd,streamRawPublicDecode_sound Q d hQd⟩

private theorem row_mass (ws : List Wire) (hw : ws.Nodup) (ψ : State) :
    ((fourierOutcomes ws.length).map (fun bs =>
      normSq (measuredFourierKernel .inverse ws bs ψ))).sum = normSq ψ := by
  have h := semiclassicalFourier_bornMass .inverse ws ([] : List Bool) ψ
  rw [semiclassicalFourier_run_kernel .inverse ws hw] at h
  simpa only [Instrument.bornMass,List.map_map,Function.comp_def] using h
private theorem indexed_nodup (start : Nat) (cs : List AdaptiveCircuit) :
    ((indexedStreamCalls start cs).map Prod.fst).Nodup := by
  simp only [indexedStreamCalls,List.map_map,Function.comp_def,Prod.fst_swap,List.zipIdx_map_snd]
  exact List.nodup_range'

theorem streamSelectedFourier_total (P Q : Point) (ψ : State) :
    (streamSelectedFourier P Q (fun _ => true)).bornMass ψ=normSq ψ := by
  rw [streamSelectedFourier_mass,streamFourierKernelEventMass]
  simp only [ite_true]
  rw [← (streamRawKernel_precisions P Q).1,← (streamRawKernel_precisions P Q).2]
  simp_rw [row_mass _ (streamFourierWires_nodup _ (indexed_nodup _ _))]

theorem streamRawTrial_total (P Q : Point) : (streamRawTrial P Q).run.bornMass (ket zeroBasisState)=1 := by
  have he : streamRawFourierEventMass P Q (fun _ => true)=
      (streamRawTrial P Q).run.bornMass (ket zeroBasisState) := by
    unfold streamRawFourierEventMass
    apply congrArg (fun I : Instrument => I.bornMass (ket zeroBasisState))
    apply List.filter_eq_self.mpr
    intro b hb
    obtain ⟨l,r,hd,_,_⟩ := streamRawTrial_decode P Q b hb
    simp [streamRawHistoryAccept,hd]
  rw [← he,streamRawFourierEventMass_terminal]
  rw [instrumentMass_seq_preserving _ _ _ (streamSelectedFourier_total P Q),
    AdaptiveCircuit.run_preservesBornMass _ (streamPreparedArithmeticCleanup_wellFormed P Q)]
  change normSq (streamPreparedEntry P Q)=1
  rw [streamPreparedEntry,streamRawPreparation_eq,
    normSq_run _ (by
      intro g hg
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg
      trivial),normSq_ket]

end
end ShorECDLP.Paper2607_13816
