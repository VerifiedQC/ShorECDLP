import ShorECDLP.Submission.«2607_13816».Window.PhasePrepare
import ShorECDLP.Submission.«2607_13816».Fourier.Kernel
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

def scalarFourierLeft : List Wire := (List.range' 855 257).reverse
def scalarFourierRight : List Wire := (List.range' 1127 257).reverse

def scalarFourierProgram : AdaptiveCircuit :=
  (semiclassicalFourier .inverse scalarFourierLeft List.nil).seq
    (semiclassicalFourier .inverse scalarFourierRight List.nil)
def scalarFourierSlice (a b : List Bool) : Instrument :=
  [⟨a++b,(fourierBranch .inverse scalarFourierRight List.nil b).comp
    (fourierBranch .inverse scalarFourierLeft List.nil a)⟩]

def windowTrialProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (preparedScalarProgram P Q hP hQ hrP hrQ).seq scalarFourierProgram

def windowTrialSlice (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool) : Instrument :=
  Instrument.seq (preparedScalarProgram P Q hP hQ hrP hrQ).run (scalarFourierSlice a b)

theorem scalarFourierProgram_run : scalarFourierProgram.run=
    (fourierOutcomes 257).flatMap (fun a => (fourierOutcomes 257).flatMap (scalarFourierSlice a)) := by
  rw [scalarFourierProgram,AdaptiveCircuit.run_seq,semiclassicalFourier_run,semiclassicalFourier_run]
  simp only [scalarFourierLeft,scalarFourierRight,List.length_reverse,List.length_range',
    Instrument.seq,List.flatMap_map,List.map_map]
  apply List.flatMap_congr
  intro a ha
  simp only [List.flatMap,InstrumentBranch.seq]
  induction fourierOutcomes 257 with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,List.flatten_cons,scalarFourierSlice,List.singleton_append,ih]
    rfl

theorem scalarFourierProgram_measurements : scalarFourierProgram.measurementCount=514 := by
  rw [scalarFourierProgram,modularMeasurements_seq,semiclassicalFourier_measurements,
    semiclassicalFourier_measurements]
  simp only [scalarFourierLeft,scalarFourierRight,List.length_reverse,List.length_range']

theorem windowTrialProgram_measurements (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (windowTrialProgram P Q hP hQ hrP hrQ).measurementCount=
      (scalarWindowsProgram P Q hP hQ hrP hrQ).measurementCount+514 := by
  rw [windowTrialProgram,modularMeasurements_seq,preparedScalar_measurementCount,
    scalarFourierProgram_measurements]

private theorem trial_normSq_smul (c : ℂ) (ψ : State) :
    normSq (c • ψ) = Complex.normSq c * normSq ψ := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

private theorem aligned_terminal_mass (ideal : State →ₗ[ℂ] State) (Valid : BasisState → Prop)
    (ψ : State) (hψ : SupportedOn Valid ψ) (K : State →ₗ[ℂ] State) (bits : List Bool)
    {branches : Instrument} {cs : List ℂ} (ha : List.Forall₂ (BranchCoherentOn ideal Valid) branches cs) :
    (Instrument.seq branches (List.singleton ⟨bits,K⟩)).bornMass ψ=
      (cs.map Complex.normSq).sum*normSq (K (ideal ψ)) := by
  induction ha with
  | nil => simp [Instrument.seq,Instrument.bornMass]
  | @cons branch c branches cs hc ht ih =>
    simp only [List.singleton,Instrument.seq,List.flatMap_cons,List.map_cons,List.map_nil,List.singleton_append,
      Instrument.bornMass,List.sum_cons,InstrumentBranch.seq,LinearMap.comp_apply]
    rw [hc.on_supported hψ,map_smul,trial_normSq_smul]
    change Complex.normSq c*normSq (K (ideal ψ))+
      (Instrument.seq branches (List.singleton ⟨bits,K⟩)).bornMass ψ=_
    rw [ih]
    ring

private theorem coherent_terminal_mass {program : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop} (h : CoherentlyImplementsOn program ideal Valid)
    (ψ : State) (hψ : SupportedOn Valid ψ) (K : State →ₗ[ℂ] State) (bits : List Bool) :
    (Instrument.seq program.run (List.singleton ⟨bits,K⟩)).bornMass ψ=normSq (K (ideal ψ)) := by
  obtain ⟨cs,ha,hm⟩ := h
  rw [aligned_terminal_mass ideal Valid ψ hψ K bits ha,hm,one_mul]

theorem windowTrialSlice_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ψ : State) (hψ : SupportedOn ScalarPhaseInitial ψ) :
    (windowTrialSlice P Q hP hQ hrP hrQ a b).bornMass ψ=
      normSq (fourierBranch .inverse scalarFourierRight List.nil b
        (fourierBranch .inverse scalarFourierLeft List.nil a
          ((Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)) (Quantum.run scalarPhasePrepare ψ)))) := by
  simpa only [windowTrialSlice,scalarFourierSlice,LinearMap.comp_apply] using
    coherent_terminal_mass (preparedScalar_coherent P Q hP hQ hrP hrQ) ψ hψ
      ((fourierBranch .inverse scalarFourierRight List.nil b).comp
        (fourierBranch .inverse scalarFourierLeft List.nil a)) (a++b)
/-- The actual full instrument, including arithmetic histories before the two output strings. -/
theorem windowTrialProgram_run (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (windowTrialProgram P Q hP hQ hrP hrQ).run =
      Instrument.seq (preparedScalarProgram P Q hP hQ hrP hrQ).run
        ((fourierOutcomes 257).flatMap (fun a =>
          (fourierOutcomes 257).flatMap (scalarFourierSlice a))) := by
  rw [windowTrialProgram,AdaptiveCircuit.run_seq,scalarFourierProgram_run]

private theorem history_support (dir : PhaseDir) (t : Wire) (bs : List Bool) (k : Nat) :
    circuitWires (fourierHistoryRotations dir t bs k) ⊆ [t] := by
  induction bs generalizing k with
  | nil => simp [fourierHistoryRotations,circuitWires]
  | cons b bs ih =>
    intro w hw
    simp only [fourierHistoryRotations,circuitWires,List.flatMap_append,List.mem_append] at hw
    rcases hw with hw | hw
    · cases b with
      | false => simp [fourierFeedForward] at hw
      | true => simpa [fourierFeedForward,circuitWires,gateWires] using hw
    · exact ih (k+1) hw

private theorem fourier_support (dir : PhaseDir) (ws : List Wire) (prior : List Bool) :
    (semiclassicalFourier dir ws prior).wires ⊆ ws := by
  induction ws generalizing prior with
  | nil => simp [semiclassicalFourier,AdaptiveCircuit.wires]
  | cons w ws ih =>
    intro v hv
    simp only [semiclassicalFourier,AdaptiveCircuit.wires,List.mem_append,List.mem_cons] at hv
    rcases hv with hv | hv | hv | hv
    · have he := history_support dir w prior 2 hv
      exact List.mem_cons.mpr (Or.inl (by simpa using he))
    · exact List.mem_cons.mpr (Or.inl hv)
    · exact List.mem_cons.mpr (Or.inr (ih _ hv))
    · exact List.mem_cons.mpr (Or.inr (ih _ hv))

theorem scalarFourierProgram_support : scalarFourierProgram.wires ⊆ scalarPhaseWires := by
  intro w hw
  rw [scalarFourierProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · have h := fourier_support .inverse scalarFourierLeft List.nil hw
    exact List.mem_append_left _ (by simpa [scalarFourierLeft] using h)
  · have h := fourier_support .inverse scalarFourierRight List.nil hw
    exact List.mem_append_right _ (by simpa [scalarFourierRight] using h)

theorem windowTrialProgram_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (windowTrialProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 := by
  intro w hw
  rw [windowTrialProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · exact preparedScalar_support P Q hP hQ hrP hrQ hw
  · have h := scalarFourierProgram_support hw
    apply List.mem_append_right
    simp only [scalarPhaseWires,List.mem_append,List.mem_range'_1] at h
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *; omega

theorem windowTrialProgram_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (windowTrialProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (windowTrialProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (windowTrialProgram_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

/-- Both valid output strings correspond to measured Fourier rows, after summing every internal arithmetic history. -/
theorem windowTrialSlice_kernel_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=257) (hb : b.length=257)
    (ψ : State) (hψ : SupportedOn ScalarPhaseInitial ψ) :
    (windowTrialSlice P Q hP hQ hrP hrQ a b).bornMass ψ=
      normSq (measuredFourierKernel .inverse scalarFourierRight b
        (measuredFourierKernel .inverse scalarFourierLeft a
          ((Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)) (Quantum.run scalarPhasePrepare ψ)))) := by
  rw [windowTrialSlice_mass P Q hP hQ hrP hrQ a b ψ hψ,
    fourierBranch_eq_kernel .inverse scalarFourierRight (by simpa only [scalarFourierRight,List.nodup_reverse] using List.nodup_range' (s:=1127) (n:=257)) b
      (by simpa [scalarFourierRight] using hb),
    fourierBranch_eq_kernel .inverse scalarFourierLeft (by simpa only [scalarFourierLeft,List.nodup_reverse] using List.nodup_range' (s:=855) (n:=257)) a
      (by simpa [scalarFourierLeft] using ha)]

end
end ShorECDLP.Paper2607_13816
