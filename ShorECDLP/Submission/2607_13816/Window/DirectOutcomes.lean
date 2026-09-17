import ShorECDLP.Submission.«2607_13816».Window.DirectTrial
import ShorECDLP.Submission.«2607_13816».Window.Outcomes
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
def decodeDirectWindowTrial (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) :=
  (consumeAdaptiveHistory (directPreparedScalarProgram P Q hP hQ hrP hrQ) hist).map decodeScalarFourier

theorem directWindowTrialSlice_filter (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=257) (hb : b.length=257) :
    directWindowTrialSlice P Q hP hQ hrP hrQ a b=
      (directWindowTrialProgram P Q hP hQ hrP hrQ).run.filter
        (fun branch => decodeDirectWindowTrial P Q hP hQ hrP hrQ branch.history==some (a,b)) := by
  rw [directWindowTrialSlice,scalarFourierSlice_filter a b ha hb,directWindowTrialProgram,AdaptiveCircuit.run_seq]
  exact adaptiveTerminalFilter _ _ _ _ (by
    intro first hf second _
    simp [decodeDirectWindowTrial,InstrumentBranch.seq,consumeAdaptiveHistory_run _ first hf])
/-- Probability obtained by decoding the actual complete measurement transcript. -/
def directWindowTrialOutputMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool) : ℝ :=
  Instrument.bornMass ((directWindowTrialProgram P Q hP hQ hrP hrQ).run.filter
    (fun branch => decodeDirectWindowTrial P Q hP hQ hrP hrQ branch.history==some (a,b)))
      (ket zeroBasisState)

theorem directWindowTrialOutputMass_kernel (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=257) (hb : b.length=257) :
    directWindowTrialOutputMass P Q hP hQ hrP hrQ a b=
      normSq (measuredFourierKernel .inverse scalarFourierRight b
        (measuredFourierKernel .inverse scalarFourierLeft a
          ((Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q))
            (Quantum.run scalarPhasePrepare (ket zeroBasisState))))) := by
  rw [directWindowTrialOutputMass,←directWindowTrialSlice_filter P Q hP hQ hrP hrQ a b ha hb]
  exact directWindowTrialSlice_kernel_mass P Q hP hQ hrP hrQ a b ha hb _
    (supportedOn_ket _ _ windowTrial_zero_initial)

theorem directWindowTrialOutputMass_eq (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=257) (hb : b.length=257) :
    directWindowTrialOutputMass P Q hP hQ hrP hrQ a b=
      windowTrialOutputMass P Q hP hQ hrP hrQ a b := by
  rw [directWindowTrialOutputMass_kernel P Q hP hQ hrP hrQ a b ha hb,
    windowTrialOutputMass_kernel P Q hP hQ hrP hrQ a b ha hb]
end
end ShorECDLP.Paper2607_13816
