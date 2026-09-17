import ShorECDLP.Submission.«2607_13816».Window.ReducedPhase
import ShorECDLP.Submission.«2607_13816».Window.Trial
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
def reducedFourierLeft : List Wire := (List.range' 855 256).reverse
def reducedFourierRight : List Wire := (List.range' 1127 208).reverse

def reducedFourierProgram : AdaptiveCircuit :=
  (semiclassicalFourier .inverse reducedFourierLeft List.nil).seq
    (semiclassicalFourier .inverse reducedFourierRight List.nil)
def reducedFourierSlice (a b : List Bool) : Instrument :=
  [⟨a++b,(fourierBranch .inverse reducedFourierRight List.nil b).comp
    (fourierBranch .inverse reducedFourierLeft List.nil a)⟩]

theorem reducedFourierProgram_run : reducedFourierProgram.run=
    (fourierOutcomes 256).flatMap (fun a => (fourierOutcomes 208).flatMap (reducedFourierSlice a)) := by
  rw [reducedFourierProgram,AdaptiveCircuit.run_seq,semiclassicalFourier_run,semiclassicalFourier_run]
  simp only [reducedFourierLeft,reducedFourierRight,List.length_reverse,List.length_range',
    Instrument.seq,List.flatMap_map,List.map_map]
  apply List.flatMap_congr
  intro a ha
  simp only [List.flatMap,InstrumentBranch.seq]
  induction fourierOutcomes 208 with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,List.flatten_cons,reducedFourierSlice,List.singleton_append,ih]
    rfl

theorem reducedFourierProgram_measurements : reducedFourierProgram.measurementCount=464 := by
  rw [reducedFourierProgram,modularMeasurements_seq,semiclassicalFourier_measurements,
    semiclassicalFourier_measurements]
  simp only [reducedFourierLeft,reducedFourierRight,List.length_reverse,List.length_range']

theorem reducedFourierProgram_support : reducedFourierProgram.wires ⊆ reducedPhaseWires := by
  intro w hw
  rw [reducedFourierProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · have h := semiclassicalFourier_support .inverse reducedFourierLeft List.nil hw
    exact List.mem_append_left _ (by simpa [reducedFourierLeft] using h)
  · have h := semiclassicalFourier_support .inverse reducedFourierRight List.nil hw
    exact List.mem_append_right _ (by simpa [reducedFourierRight] using h)

def reducedWindowTrialProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (reducedPreparedScalarProgram P Q hP hQ hrP hrQ).seq reducedFourierProgram

def reducedWindowTrialSlice (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool) : Instrument :=
  Instrument.seq (reducedPreparedScalarProgram P Q hP hQ hrP hrQ).run (reducedFourierSlice a b)


theorem reducedWindowTrialSlice_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ψ : State) (hψ : SupportedOn ReducedPhaseInitial ψ) :
    (reducedWindowTrialSlice P Q hP hQ hrP hrQ a b).bornMass ψ=
      normSq (fourierBranch .inverse reducedFourierRight List.nil b
        (fourierBranch .inverse reducedFourierLeft List.nil a
          ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) (Quantum.run reducedPhasePrepare ψ)))) := by
  simpa only [reducedWindowTrialSlice,reducedFourierSlice,LinearMap.comp_apply] using
    coherentTerminalMass (reducedPreparedScalar_coherent P Q hP hQ hrP hrQ) ψ hψ
      ((fourierBranch .inverse reducedFourierRight List.nil b).comp
        (fourierBranch .inverse reducedFourierLeft List.nil a)) (a++b)
/-- The actual full instrument, including arithmetic histories before the two output strings. -/
theorem reducedWindowTrialProgram_run (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (reducedWindowTrialProgram P Q hP hQ hrP hrQ).run =
      Instrument.seq (reducedPreparedScalarProgram P Q hP hQ hrP hrQ).run
        ((fourierOutcomes 256).flatMap (fun a =>
          (fourierOutcomes 208).flatMap (reducedFourierSlice a))) := by
  rw [reducedWindowTrialProgram,AdaptiveCircuit.run_seq,reducedFourierProgram_run]


theorem reducedWindowTrialProgram_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (reducedWindowTrialProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++reducedPhaseWires := by
  intro w hw
  rw [reducedWindowTrialProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · exact reducedPreparedScalar_support P Q hP hQ hrP hrQ hw
  · exact List.mem_append_right _ (reducedFourierProgram_support hw)

theorem reducedWindowTrialProgram_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (reducedWindowTrialProgram P Q hP hQ hrP hrQ).qubitCount≤1303 := by
  have hs : (reducedWindowTrialProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++reducedPhaseWires).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (reducedWindowTrialProgram_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,reducedPhaseWires,List.length_append,List.length_range,List.length_range'] using hc

/-- Both valid output strings correspond to measured Fourier rows, after summing every internal arithmetic history. -/
theorem reducedWindowTrialSlice_kernel_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=256) (hb : b.length=208)
    (ψ : State) (hψ : SupportedOn ReducedPhaseInitial ψ) :
    (reducedWindowTrialSlice P Q hP hQ hrP hrQ a b).bornMass ψ=
      normSq (measuredFourierKernel .inverse reducedFourierRight b
        (measuredFourierKernel .inverse reducedFourierLeft a
          ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) (Quantum.run reducedPhasePrepare ψ)))) := by
  rw [reducedWindowTrialSlice_mass P Q hP hQ hrP hrQ a b ψ hψ,
    fourierBranch_eq_kernel .inverse reducedFourierRight (by simpa only [reducedFourierRight,List.nodup_reverse] using List.nodup_range' (s:=1127) (n:=208)) b
      (by simpa [reducedFourierRight] using hb),
    fourierBranch_eq_kernel .inverse reducedFourierLeft (by simpa only [reducedFourierLeft,List.nodup_reverse] using List.nodup_range' (s:=855) (n:=256)) a
      (by simpa [reducedFourierLeft] using ha)]

end
end ShorECDLP.Paper2607_13816
