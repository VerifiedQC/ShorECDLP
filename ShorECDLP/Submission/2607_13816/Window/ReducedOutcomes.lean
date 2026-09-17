import ShorECDLP.Submission.«2607_13816».Window.ReducedTrial
import ShorECDLP.Submission.«2607_13816».Window.Outcomes
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
def decodeReducedFourier (hist : List Bool) : List Bool × List Bool :=
  (hist.take 256,hist.drop 256)

theorem reducedFourierSlice_filter (a b : List Bool) (ha : a.length=256) (hb : b.length=208) :
    reducedFourierSlice a b=reducedFourierProgram.run.filter
      (fun branch => decodeReducedFourier branch.history==(a,b)) := by
  have hfirst : a.length=reducedFourierLeft.length := by simpa [reducedFourierLeft] using ha
  have hsecond : b.length=reducedFourierRight.length := by simpa [reducedFourierRight] using hb
  have hslice : reducedFourierSlice a b =
      Instrument.seq (List.singleton ⟨a,fourierBranch .inverse reducedFourierLeft List.nil a⟩)
        (List.singleton ⟨b,fourierBranch .inverse reducedFourierRight List.nil b⟩) := rfl
  rw [hslice]
  simp only [List.singleton]
  rw [←semiclassicalFourier_filter .inverse _ _ hfirst,←semiclassicalFourier_filter .inverse _ _ hsecond,
    reducedFourierProgram,AdaptiveCircuit.run_seq]
  apply instrumentFilter_pair
  intro first hf second _
  have hlen : first.history.length=256 := by
    simpa [reducedFourierLeft] using semiclassicalFourier_history_length .inverse reducedFourierLeft first hf
  simp [decodeReducedFourier,InstrumentBranch.seq,←hlen]
  rfl

def decodeReducedWindowTrial (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) :=
  (consumeAdaptiveHistory (reducedPreparedScalarProgram P Q hP hQ hrP hrQ) hist).map decodeReducedFourier

theorem reducedWindowTrialSlice_filter (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=256) (hb : b.length=208) :
    reducedWindowTrialSlice P Q hP hQ hrP hrQ a b=
      (reducedWindowTrialProgram P Q hP hQ hrP hrQ).run.filter
        (fun branch => decodeReducedWindowTrial P Q hP hQ hrP hrQ branch.history==some (a,b)) := by
  rw [reducedWindowTrialSlice,reducedFourierSlice_filter a b ha hb,reducedWindowTrialProgram,AdaptiveCircuit.run_seq]
  exact adaptiveTerminalFilter _ _ _ _ (by
    intro first hf second _
    simp [decodeReducedWindowTrial,InstrumentBranch.seq,consumeAdaptiveHistory_run _ first hf])
/-- Probability obtained by decoding the actual complete measurement transcript. -/
def reducedWindowTrialOutputMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool) : ℝ :=
  Instrument.bornMass ((reducedWindowTrialProgram P Q hP hQ hrP hrQ).run.filter
    (fun branch => decodeReducedWindowTrial P Q hP hQ hrP hrQ branch.history==some (a,b)))
      (ket zeroBasisState)

theorem reducedWindowTrial_zero_initial : ReducedPhaseInitial zeroBasisState := by
  have hz : zeroBasisState=(fun _ => false) := rfl
  simp [ReducedPhaseInitial,ScalarComputeValid,ScalarPaddingClean,Clean,wireValues,hz,List.map_const']

theorem reducedWindowTrialOutputMass_kernel (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=256) (hb : b.length=208) :
    reducedWindowTrialOutputMass P Q hP hQ hrP hrQ a b=
      normSq (measuredFourierKernel .inverse reducedFourierRight b
        (measuredFourierKernel .inverse reducedFourierLeft a
          ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q))
            (Quantum.run reducedPhasePrepare (ket zeroBasisState))))) := by
  rw [reducedWindowTrialOutputMass,←reducedWindowTrialSlice_filter P Q hP hQ hrP hrQ a b ha hb]
  exact reducedWindowTrialSlice_kernel_mass P Q hP hQ hrP hrQ a b ha hb _
    (supportedOn_ket _ _ reducedWindowTrial_zero_initial)

end
end ShorECDLP.Paper2607_13816
