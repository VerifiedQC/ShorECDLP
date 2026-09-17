import ShorECDLP.Submission.«2607_13816».Window.Trial
import ShorECDLP.Submission.«2607_13816».OrderFinding.PhaseSchedule
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem filterPairInstrument (xs ys : Instrument) (p q z : InstrumentBranch → Bool)
    (hz : ∀ x∈xs, ∀ y∈ys, z (x.seq y)=(p x && q y)) :
    Instrument.seq (xs.filter p) (ys.filter q)=(Instrument.seq xs ys).filter z := by
  induction xs with
  | nil => simp [Instrument.seq]
  | cons x xs ih =>
    have htail : ∀ a∈xs, ∀ y∈ys, z (a.seq y)=(p a && q y) := by
      intro a ha y hy
      exact hz a (by simp [ha]) y hy
    have hmap : ((ys.map x.seq).filter z) = if p x then (ys.filter q).map x.seq else [] := by
      rw [List.filter_map]
      have he : ys.filter (z ∘ x.seq)=ys.filter (fun y => p x && q y) := by
        apply List.filter_congr
        intro y hy
        exact hz x (by simp) y hy
      rw [he]
      cases p x <;> simp
    have iht := ih htail
    unfold Instrument.seq at iht
    cases hp : p x <;> simp [Instrument.seq,hp,hmap,iht]

private theorem fourier_filter (dir : PhaseDir) (ws : List Wire) (bs : List Bool)
    (hlen : bs.length=ws.length) :
    (semiclassicalFourier dir ws List.nil).run.filter (fun b => b.history==bs)=
      [⟨bs,fourierBranch dir ws List.nil bs⟩] := by
  rw [semiclassicalFourier_run,List.filter_map]
  change ((fourierOutcomes ws.length).filter (·==bs)).map _=_
  rw [List.filter_beq]
  have hc : (fourierOutcomes ws.length).count bs=1 :=
    List.count_eq_one_of_mem (fourierOutcomes_nodup _) ((fourierOutcomes_mem _ _).mpr hlen)
  rw [hc]
  rfl
private theorem fourier_history_length (dir : PhaseDir) (ws : List Wire) (b : InstrumentBranch)
    (hb : b∈(semiclassicalFourier dir ws List.nil).run) : b.history.length=ws.length := by
  rw [semiclassicalFourier_run] at hb
  obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp hb
  exact (fourierOutcomes_mem _ _).mp hbs

def decodeScalarFourier (hist : List Bool) : List Bool × List Bool :=
  (hist.take 257,hist.drop 257)

theorem scalarFourierSlice_filter (a b : List Bool) (ha : a.length=257) (hb : b.length=257) :
    scalarFourierSlice a b=scalarFourierProgram.run.filter
      (fun branch => decodeScalarFourier branch.history==(a,b)) := by
  have hfirst : a.length=scalarFourierLeft.length := by simpa [scalarFourierLeft] using ha
  have hsecond : b.length=scalarFourierRight.length := by simpa [scalarFourierRight] using hb
  have hslice : scalarFourierSlice a b =
      Instrument.seq (List.singleton ⟨a,fourierBranch .inverse scalarFourierLeft List.nil a⟩)
        (List.singleton ⟨b,fourierBranch .inverse scalarFourierRight List.nil b⟩) := rfl
  rw [hslice]
  simp only [List.singleton]
  rw [←fourier_filter .inverse _ _ hfirst,←fourier_filter .inverse _ _ hsecond,
    scalarFourierProgram,AdaptiveCircuit.run_seq]
  apply filterPairInstrument
  intro first hf second _
  have hlen : first.history.length=257 := by
    simpa [scalarFourierLeft] using fourier_history_length .inverse scalarFourierLeft first hf
  simp [decodeScalarFourier,InstrumentBranch.seq,←hlen]
  rfl

def decodeWindowTrial (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) :=
  (consumeAdaptiveHistory (preparedScalarProgram P Q hP hQ hrP hrQ) hist).map decodeScalarFourier

theorem adaptiveTerminalFilter (program : AdaptiveCircuit) (ys : Instrument)
    (q z : InstrumentBranch → Bool)
    (hz : ∀ x∈program.run, ∀ y∈ys, z (x.seq y)=q y) :
    Instrument.seq program.run (ys.filter q)=(Instrument.seq program.run ys).filter z := by
  have h := filterPairInstrument program.run ys (fun _ => true) q z (by
    intro x hx y hy
    simpa using hz x hx y hy)
  simpa only [List.filter_true] using h

theorem windowTrialSlice_filter (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=257) (hb : b.length=257) :
    windowTrialSlice P Q hP hQ hrP hrQ a b=
      (windowTrialProgram P Q hP hQ hrP hrQ).run.filter
        (fun branch => decodeWindowTrial P Q hP hQ hrP hrQ branch.history==some (a,b)) := by
  rw [windowTrialSlice,scalarFourierSlice_filter a b ha hb,windowTrialProgram,AdaptiveCircuit.run_seq]
  exact adaptiveTerminalFilter _ _ _ _ (by
    intro first hf second _
    simp [decodeWindowTrial,InstrumentBranch.seq,consumeAdaptiveHistory_run _ first hf])
theorem windowTrial_zero_initial : ScalarPhaseInitial zeroBasisState := by
  have hz : zeroBasisState=(fun _ => false) := rfl
  simp [ScalarPhaseInitial,ScalarComputeValid,ScalarPaddingClean,Clean,wireValues,hz,List.map_const']

/-- Probability obtained by decoding the actual complete measurement transcript. -/
def windowTrialOutputMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool) : ℝ :=
  Instrument.bornMass ((windowTrialProgram P Q hP hQ hrP hrQ).run.filter
    (fun branch => decodeWindowTrial P Q hP hQ hrP hrQ branch.history==some (a,b)))
      (ket zeroBasisState)

theorem windowTrialOutputMass_kernel (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=257) (hb : b.length=257) :
    windowTrialOutputMass P Q hP hQ hrP hrQ a b=
      normSq (measuredFourierKernel .inverse scalarFourierRight b
        (measuredFourierKernel .inverse scalarFourierLeft a
          ((Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q))
            (Quantum.run scalarPhasePrepare (ket zeroBasisState))))) := by
  rw [windowTrialOutputMass,←windowTrialSlice_filter P Q hP hQ hrP hrQ a b ha hb]
  exact windowTrialSlice_kernel_mass P Q hP hQ hrP hrQ a b ha hb _
    (supportedOn_ket _ _ windowTrial_zero_initial)

end
end ShorECDLP.Paper2607_13816
