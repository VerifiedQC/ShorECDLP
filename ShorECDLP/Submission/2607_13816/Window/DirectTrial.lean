import ShorECDLP.Submission.«2607_13816».Window.DirectPhase
import ShorECDLP.Submission.«2607_13816».Window.Trial
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
def directWindowTrialProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (directPreparedScalarProgram P Q hP hQ hrP hrQ).seq scalarFourierProgram

def directWindowTrialSlice (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool) : Instrument :=
  Instrument.seq (directPreparedScalarProgram P Q hP hQ hrP hrQ).run (scalarFourierSlice a b)


theorem directWindowTrialSlice_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ψ : State) (hψ : SupportedOn ScalarPhaseInitial ψ) :
    (directWindowTrialSlice P Q hP hQ hrP hrQ a b).bornMass ψ=
      normSq (fourierBranch .inverse scalarFourierRight List.nil b
        (fourierBranch .inverse scalarFourierLeft List.nil a
          ((Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)) (Quantum.run scalarPhasePrepare ψ)))) := by
  simpa only [directWindowTrialSlice,scalarFourierSlice,LinearMap.comp_apply] using
    coherentTerminalMass (directPreparedScalar_coherent P Q hP hQ hrP hrQ) ψ hψ
      ((fourierBranch .inverse scalarFourierRight List.nil b).comp
        (fourierBranch .inverse scalarFourierLeft List.nil a)) (a++b)
/-- The actual full instrument, including arithmetic histories before the two output strings. -/
theorem directWindowTrialProgram_run (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directWindowTrialProgram P Q hP hQ hrP hrQ).run =
      Instrument.seq (directPreparedScalarProgram P Q hP hQ hrP hrQ).run
        ((fourierOutcomes 257).flatMap (fun a =>
          (fourierOutcomes 257).flatMap (scalarFourierSlice a))) := by
  rw [directWindowTrialProgram,AdaptiveCircuit.run_seq,scalarFourierProgram_run]


theorem directWindowTrialProgram_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directWindowTrialProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 := by
  intro w hw
  rw [directWindowTrialProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · exact directPreparedScalar_support P Q hP hQ hrP hrQ hw
  · have h := scalarFourierProgram_support hw
    apply List.mem_append_right
    simp only [scalarPhaseWires,List.mem_append,List.mem_range'_1] at h
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *; omega

theorem directWindowTrialProgram_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directWindowTrialProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (directWindowTrialProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (directWindowTrialProgram_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

/-- Both valid output strings correspond to measured Fourier rows, after summing every internal arithmetic history. -/
theorem directWindowTrialSlice_kernel_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=257) (hb : b.length=257)
    (ψ : State) (hψ : SupportedOn ScalarPhaseInitial ψ) :
    (directWindowTrialSlice P Q hP hQ hrP hrQ a b).bornMass ψ=
      normSq (measuredFourierKernel .inverse scalarFourierRight b
        (measuredFourierKernel .inverse scalarFourierLeft a
          ((Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)) (Quantum.run scalarPhasePrepare ψ)))) := by
  rw [directWindowTrialSlice_mass P Q hP hQ hrP hrQ a b ψ hψ,
    fourierBranch_eq_kernel .inverse scalarFourierRight (by simpa only [scalarFourierRight,List.nodup_reverse] using List.nodup_range' (s:=1127) (n:=257)) b
      (by simpa [scalarFourierRight] using hb),
    fourierBranch_eq_kernel .inverse scalarFourierLeft (by simpa only [scalarFourierLeft,List.nodup_reverse] using List.nodup_range' (s:=855) (n:=257)) a
      (by simpa [scalarFourierLeft] using ha)]

theorem directWindowTrialSlice_eq_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ψ : State) (hψ : SupportedOn ScalarPhaseInitial ψ) :
    (directWindowTrialSlice P Q hP hQ hrP hrQ a b).bornMass ψ=
      (windowTrialSlice P Q hP hQ hrP hrQ a b).bornMass ψ := by
  rw [directWindowTrialSlice_mass P Q hP hQ hrP hrQ a b ψ hψ,
    windowTrialSlice_mass P Q hP hQ hrP hrQ a b ψ hψ]

theorem directWindowTrialProgram_tCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directWindowTrialProgram P Q hP hQ hrP hrQ).tCount+
      (preparedWindowCall (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
        (fun k => oddWindowTable_valid P hP hrP (k-0)) 0).tCount=
      (windowTrialProgram P Q hP hQ hrP hrQ).tCount+458745 := by
  have ht (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  rw [directWindowTrialProgram,windowTrialProgram,ht,ht]
  have h := directPreparedScalar_tCount P Q hP hQ hrP hrQ
  omega

theorem directWindowTrialProgram_measurementCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directWindowTrialProgram P Q hP hQ hrP hrQ).measurementCount+
      (preparedWindowCall (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
        (fun k => oddWindowTable_valid P hP hrP (k-0)) 0).measurementCount=
      (windowTrialProgram P Q hP hQ hrP hrQ).measurementCount+65535 := by
  rw [directWindowTrialProgram,windowTrialProgram,modularMeasurements_seq,modularMeasurements_seq]
  have h := directPreparedScalar_measurementCount P Q hP hQ hrP hrQ
  omega
end
end ShorECDLP.Paper2607_13816
