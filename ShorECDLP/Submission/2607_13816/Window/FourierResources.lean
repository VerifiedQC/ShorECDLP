import ShorECDLP.Submission.«2607_13816».Window.Trial
import ShorECDLP.Submission.«2607_13816».Arithmetic.PrimitiveResources
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem history_T (dir : PhaseDir) (w : Wire) (bs : List Bool) (k : Nat) :
    tCount (fourierHistoryRotations dir w bs k)≤bs.length := by
  induction bs generalizing k with
  | nil => simp [fourierHistoryRotations]
  | cons b bs ih =>
    have h := ih (k+1)
    cases b <;> simp [fourierHistoryRotations, fourierFeedForward,
      tCount, tCost] <;> unfold tCount at h <;> omega
private def phaseBudget : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, p => p+phaseBudget n (p+1)
private theorem fourier_T (dir : PhaseDir) (ws : List Wire) (prior : List Bool) :
    (semiclassicalFourier dir ws prior).tCount≤phaseBudget ws.length prior.length := by
  induction ws generalizing prior with
  | nil => simp [semiclassicalFourier,AdaptiveCircuit.tCount,phaseBudget]
  | cons w ws ih =>
    have hf := ih (false::prior)
    have ht := ih (true::prior)
    have hh := history_T dir w prior 2
    simp only [semiclassicalFourier,AdaptiveCircuit.tCount,List.length_cons,phaseBudget] at *
    omega
theorem scalarFourierProgram_tCount_le : scalarFourierProgram.tCount≤65792 := by
  have h := modularGateCount_seq tCost
    (semiclassicalFourier .inverse scalarFourierLeft List.nil)
    (semiclassicalFourier .inverse scalarFourierRight List.nil)
  simp only [gidneyGateCount_tCount] at h
  have hl := fourier_T .inverse scalarFourierLeft List.nil
  have hr := fourier_T .inverse scalarFourierRight List.nil
  have hb : phaseBudget 257 0=32896 := by decide +kernel
  simp only [scalarFourierLeft,scalarFourierRight,List.length_reverse,List.length_range',List.length_nil,hb] at hl hr
  change scalarFourierProgram.tCount=_+_ at h
  simp only [scalarFourierLeft,scalarFourierRight] at h
  omega
private theorem history_cost (cost : Gate → Nat) (v : Nat)
    (hc : ∀ dir k w, cost (.P dir k w)=v) (dir : PhaseDir) (w : Wire) (bs : List Bool) (k : Nat) :
    ((fourierHistoryRotations dir w bs k).map cost).sum =
      v*tCount (fourierHistoryRotations dir w bs k) := by
  induction bs generalizing k with
  | nil => simp [fourierHistoryRotations, tCount]
  | cons b bs ih =>
    cases b <;> simp [fourierHistoryRotations, fourierFeedForward, tCount, tCost, hc, ih, mul_add]
theorem semiclassicalFourier_gateCount (cost : Gate → Nat) (v : Nat)
    (hc : ∀ dir k w, cost (.P dir k w)=v) (dir : PhaseDir) (ws : List Wire) (prior : List Bool) :
    gidneyGateCount cost (semiclassicalFourier dir ws prior)=
      v*(semiclassicalFourier dir ws prior).tCount := by
  induction ws generalizing prior with
  | nil => simp [semiclassicalFourier,gidneyGateCount,AdaptiveCircuit.tCount]
  | cons w ws ih =>
    simp only [semiclassicalFourier,gidneyGateCount,AdaptiveCircuit.tCount,ih,history_cost cost v hc,
      Nat.mul_max_mul_left,mul_add]
private theorem scalar_cost (cost : Gate → Nat) (v : Nat)
    (hc : ∀ dir k w, cost (.P dir k w)=v) :
    gidneyGateCount cost scalarFourierProgram=v*scalarFourierProgram.tCount := by
  rw [scalarFourierProgram,modularGateCount_seq]
  simp only [semiclassicalFourier_gateCount cost v hc]
  have h := modularGateCount_seq tCost
    (semiclassicalFourier .inverse scalarFourierLeft List.nil)
    (semiclassicalFourier .inverse scalarFourierRight List.nil)
  simp only [gidneyGateCount_tCount] at h
  exact (mul_add _ _ _).symm.trans (congrArg (fun z : Nat => v*z) h.symm)
private theorem resources_of_cost (a : AdaptiveCircuit)
    (hc : ∀ (cost : Gate → Nat) (v : Nat), (∀ dir k w, cost (.P dir k w)=v) →
      gidneyGateCount cost a=v*a.tCount)
    (ht : a.tCount≤65792) (hm : a.measurementCount=514) :
    (primitiveResources a).x=0 ∧ (primitiveResources a).h=0 ∧
    (primitiveResources a).cnot=0 ∧ (primitiveResources a).toffoli=0 ∧
    (primitiveResources a).phase≤65792 ∧ (primitiveResources a).measurements=514 := by
  have hz (cost : Gate → Nat) (h : ∀ dir k w, cost (.P dir k w)=0) :
      gidneyGateCount cost a=0 := by simpa only [zero_mul] using hc cost 0 h
  have hp : gidneyGateCount primitivePhaseCost a=a.tCount := by
    simpa only [one_mul] using hc primitivePhaseCost 1 (by intros; rfl)
  exact ⟨hz _ (by intros; rfl),hz _ (by intros; rfl),hz _ (by intros; rfl),
    hz _ (by intros; rfl),hp.le.trans ht,hm⟩
/-- Fourier suffix primitive counts; phase synthesis costs are not included. -/
theorem scalarFourierProgram_resources :
    (primitiveResources scalarFourierProgram).x=0 ∧
    (primitiveResources scalarFourierProgram).h=0 ∧
    (primitiveResources scalarFourierProgram).cnot=0 ∧
    (primitiveResources scalarFourierProgram).toffoli=0 ∧
    (primitiveResources scalarFourierProgram).phase≤65792 ∧
    (primitiveResources scalarFourierProgram).measurements=514 :=
  resources_of_cost scalarFourierProgram scalar_cost scalarFourierProgram_tCount_le
    scalarFourierProgram_measurements

/-- The Fourier suffix adds at most 65,792 phase gates in the repository's unit-cost P metric. -/
theorem windowTrialProgram_tCount_le (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (windowTrialProgram P Q hP hQ hrP hrQ).tCount ≤
      (scalarWindowsProgram P Q hP hQ hrP hrQ).tCount+65792 := by
  have h := modularGateCount_seq tCost (preparedScalarProgram P Q hP hQ hrP hrQ) scalarFourierProgram
  simp only [gidneyGateCount_tCount,preparedScalar_tCount] at h
  change (windowTrialProgram P Q hP hQ hrP hrQ).tCount=_ at h
  rw [h]
  exact Nat.add_le_add_left scalarFourierProgram_tCount_le _
end
end ShorECDLP.Paper2607_13816
