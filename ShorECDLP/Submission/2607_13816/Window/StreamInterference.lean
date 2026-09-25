import ShorECDLP.Submission.«2607_13816».Window.StreamGoodFourier
import ShorECDLP.Submission.«2607_13816».Window.PreparedWeight
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section
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
theorem streamSelectedFourier_contractive (P Q : Point) (accept : List Bool × List Bool → Bool) (ψ : State) :
    (streamSelectedFourier P Q accept).bornMass ψ ≤ normSq ψ := by
  rw [streamSelectedFourier_mass,streamFourierKernelEventMass]
  have hr := (streamRawKernel_precisions P Q).2
  have hl := (streamRawKernel_precisions P Q).1
  calc
    _ ≤ ((fourierOutcomes 256).map (fun ls =>
      ((fourierOutcomes 208).map (fun rs => normSq (measuredFourierKernel .inverse
        (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) rs
        (measuredFourierKernel .inverse
          (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) ls ψ)))).sum)).sum := by
      apply List.sum_le_sum
      intro x hx
      apply List.sum_le_sum
      intro y hy
      split
      · rfl
      · have h := (normSq_interference (0 : State) (measuredFourierKernel .inverse
          (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) y
          (measuredFourierKernel .inverse
            (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) x ψ))).2
        simp only [zero_add] at h
        have hz : normSq (0 : State)=0 := by simp [normSq]
        rw [hz] at h
        linarith
    _ = normSq ψ := by
      rw [← hr,← hl]
      simp_rw [row_mass _ (streamFourierWires_nodup _ (indexed_nodup _ _))]

theorem streamPreparedArithmeticCleanup_wellFormed (P Q : Point) :
    (((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q)).seq
      (.unitary [.X 836] .done)).WellFormed := by
  have hl := initializedRawProgram_wellFormed
    (axisWindowOffset P 16 + axisWindowOffset Q 13) ((2^(16*15)) • P)
    (fun _ _ => 0) (fun _ _ => 0) ([] : List Nat)
  simp only [initializedRawProgram,rawWindowSchedule,circuit_seq_done] at hl
  have hp : (streamPreparedLookup P Q).WellFormed := by
    simpa only [streamPreparedLookup,AdaptiveCircuit.relabel_wellFormed] using hl
  exact (hp.seq (rawWindowSchedule_wellFormed _ _ _)).seq
    (by simp [AdaptiveCircuit.WellFormed,CircuitWellFormed,Gate.WellFormed])
theorem streamPreparedFourierTerminal_contractive (P Q : Point) (accept : List Bool × List Bool → Bool) (ψ : State) :
    (((((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q)).seq
      (.unitary [.X 836] .done)).run).seq (streamSelectedFourier P Q accept)).bornMass ψ ≤ normSq ψ := by
  exact (Instrument.seq_bornMass_le _ _ (streamSelectedFourier_contractive P Q accept) ψ).trans_eq
    (AdaptiveCircuit.run_preservesBornMass _ (streamPreparedArithmeticCleanup_wellFormed P Q) ψ)

theorem streamRawFourierEventMass_good_lower (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0)
    (accept : List Bool × List Bool → Bool) :
    (3/4:ℝ)*streamFourierKernelEventMass P Q accept
      (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q)
        (streamPreparedGoodEntry P Q hP hQ hrP hrQ)) - 21/4096 ≤
    streamRawFourierEventMass P Q accept := by
  classical
  let bad : State := (streamPreparedEntry P Q).filter
    (fun s => ¬streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire))
  let I := ((((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q)).seq
    (.unitary [.X 836] .done)).run).seq (streamSelectedFourier P Q accept)
  have hd : streamPreparedGoodEntry P Q hP hQ hrP hrQ + bad = streamPreparedEntry P Q :=
    Finsupp.filter_pos_add_filter_neg _ _
  have hb : I.bornMass bad ≤ (7:ℝ)/4096 :=
    (streamPreparedFourierTerminal_contractive P Q accept bad).trans
      (streamRawPrepared_excluded_mass P Q hP hQ hrP hrQ)
  have hi := (I.bornMass_interference (streamPreparedGoodEntry P Q hP hQ hrP hrQ) bad).1
  rw [hd] at hi
  have hg := streamPreparedGoodEntry_fourierMass P Q hP hQ hrP hrQ accept
  have ha := streamRawFourierEventMass_terminal P Q accept
  change I.bornMass (streamPreparedGoodEntry P Q hP hQ hrP hrQ) = _ at hg
  change streamRawFourierEventMass P Q accept = I.bornMass (streamPreparedEntry P Q) at ha
  rw [hg,← ha] at hi
  linarith

private theorem output_injective (P Q : Point) :
    Set.InjOn (streamPreparedScalarOutput P Q) {s | PointInitializeValid s} := by
  intro s hs t ht he
  funext w
  by_cases hw : w∈pointLogicalWires
  · have hz (u : BasisState) (hu : PointInitializeValid u) : u w=false := by
      have hm : u w∈wireValues pointLogicalWires u := List.mem_map.mpr ⟨w, hw, rfl⟩
      rw [hu.2] at hm
      exact List.eq_of_mem_replicate hm
    rw [hz s hs, hz t ht]
  · have hh := congrFun he w
    simpa only [streamPreparedScalarOutput, pointWrite_frame _ _ _ hw] using hh

theorem streamPreparedScalarOutput_normSq (P Q : Point) (ψ : State)
    (hψ : SupportedOn PointInitializeValid ψ) :
    normSq ((Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q)) ψ) = normSq ψ := by
  apply normSq_mapDomain
  intro s hs t ht he
  exact output_injective P Q (hψ s (Finsupp.mem_support_iff.mp hs))
    (hψ t (Finsupp.mem_support_iff.mp ht)) he

private theorem filtered_support (V : BasisState → Prop) (ψ : State)
    (h : SupportedOn V ψ) (p : BasisState → Prop) [DecidablePred p] :
    SupportedOn V (ψ.filter p) := by
  intro s hs
  rw [Finsupp.filter_apply] at hs
  split_ifs at hs
  · exact h s hs
  · exact False.elim (hs rfl)

/-- Actual full-record acceptance is bounded against the full ideal input.
The error term accounts for both coherent interference comparisons. A positive
success bound still requires a numerical lower bound for the ideal event. -/
theorem streamRawFourierEventMass_ideal_lower (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0)
    (accept : List Bool × List Bool → Bool) :
    (9/16:ℝ)*streamFourierKernelEventMass P Q accept
      (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q) (streamPreparedEntry P Q))
      - 147/16384 ≤ streamRawFourierEventMass P Q accept := by
  classical
  let bad : State := (streamPreparedEntry P Q).filter
    (fun s => ¬streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire))
  let good := streamPreparedGoodEntry P Q hP hQ hrP hrQ
  let ideal := Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q)
  have hd : good+bad=streamPreparedEntry P Q := Finsupp.filter_pos_add_filter_neg _ _
  have hs : SupportedOn PointInitializeValid bad :=
    filtered_support _ _ (by simpa only [streamPreparedEntry] using streamPreparedEntry_supported P Q) _
  have hb : (streamSelectedFourier P Q accept).bornMass (ideal bad) ≤ (7:ℝ)/4096 := by
    apply (streamSelectedFourier_contractive P Q accept _).trans
    rw [streamPreparedScalarOutput_normSq P Q bad hs]
    exact streamRawPrepared_excluded_mass P Q hP hQ hrP hrQ
  have he : ideal (streamPreparedEntry P Q) + -(ideal bad) = ideal good := by
    rw [← hd,map_add]
    abel
  have hi := ((streamSelectedFourier P Q accept).bornMass_interference
    (ideal (streamPreparedEntry P Q)) (-(ideal bad))).1
  rw [he,Instrument.bornMass_neg] at hi
  simp only [streamSelectedFourier_mass] at hi hb
  have ha := streamRawFourierEventMass_good_lower P Q hP hQ hrP hrQ accept
  change (3/4:ℝ)*streamFourierKernelEventMass P Q accept (ideal good)-21/4096 ≤ _ at ha
  linarith
end
end ShorECDLP.Paper2607_13816
