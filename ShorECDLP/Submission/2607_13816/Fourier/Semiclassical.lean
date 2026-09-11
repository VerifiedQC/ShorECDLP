import ShorECDLP.Submission.«2607_13816».Fourier.FeedForward
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum
noncomputable section
/-- Input wires are most-significant first; emitted bits are least-significant first.
The history argument stores earlier outputs in reverse emission order. -/
def semiclassicalFourier (dir : PhaseDir) : List Wire → List Bool → AdaptiveCircuit
  | [], _ => .done
  | w :: ws, prior => .unitary (fourierHistoryRotations dir w prior 2)
      (.xMeasureReset w (semiclassicalFourier dir ws (false :: prior))
        (semiclassicalFourier dir ws (true :: prior)))
def fourierOutcomes : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (fourierOutcomes n).map (false :: ·) ++ (fourierOutcomes n).map (true :: ·)
/-- The Kraus map for one explicitly retained output string. -/
def fourierBranch (dir : PhaseDir) : List Wire → List Bool → List Bool → State →ₗ[ℂ] State
  | [], _, [] => LinearMap.id
  | w :: ws, prior, b :: bs =>
      (fourierBranch dir ws (b :: prior) bs).comp
        ((xResetKraus w b).comp (Quantum.run (fourierHistoryRotations dir w prior 2)))
  | _, _, _ => 0
theorem semiclassicalFourier_run (dir : PhaseDir) (ws : List Wire) (prior : List Bool) :
    (semiclassicalFourier dir ws prior).run =
      (fourierOutcomes ws.length).map (fun bs => ⟨bs, fourierBranch dir ws prior bs⟩) := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih =>
    simp only [semiclassicalFourier, AdaptiveCircuit.run, ih, List.length_cons,
      fourierOutcomes, List.map_append, List.map_map]
    rfl

theorem fourierOutcomes_length (n : Nat) : (fourierOutcomes n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fourierOutcomes, ih, pow_succ]; omega

theorem fourierOutcomes_mem (n : Nat) (bs : List Bool) : bs ∈ fourierOutcomes n ↔ bs.length = n := by
  induction n generalizing bs with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    cases bs with
    | nil => simp [fourierOutcomes]
    | cons b bs => cases b <;> simp [fourierOutcomes, ih]

theorem semiclassicalFourier_measurements (dir : PhaseDir) (ws : List Wire) (prior : List Bool) :
    (semiclassicalFourier dir ws prior).measurementCount = ws.length := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih => simp [semiclassicalFourier, AdaptiveCircuit.measurementCount, ih, Nat.add_comm]
/-- State after resetting all Fourier input wires. -/
def fourierClear : List Wire → BasisState → BasisState
  | [], s => s
  | w :: ws, s => fourierClear ws (s[w ↦ false])
/-- Exact scalar of one retained branch, before taking its Born mass. -/
def fourierBranchCoeff (dir : PhaseDir) : List Wire → List Bool → List Bool → BasisState → ℂ
  | [], _, [], _ => 1
  | w :: ws, prior, b :: bs, s =>
      (if s w then Complex.exp (Complex.I * (fourierHistoryAngle dir prior 2 : ℂ)) else 1) *
        xResetCoeff b (s w) * fourierBranchCoeff dir ws (b :: prior) bs (s[w ↦ false])
  | _, _, _, _ => 0

theorem fourierBranch_ket (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool) (s : BasisState) :
    fourierBranch dir ws prior bs (ket s) =
      fourierBranchCoeff dir ws prior bs s • ket (fourierClear ws s) := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> simp [fourierBranch, fourierBranchCoeff, fourierClear]
  | cons w ws ih =>
    cases bs with
    | nil => simp [fourierBranch, fourierBranchCoeff]
    | cons b bs =>
      simp only [fourierBranch, LinearMap.comp_apply, fourierHistoryRotations_ket,
        map_smul, xResetKraus_ket, ih, fourierBranchCoeff, fourierClear, smul_smul, mul_assoc]
private theorem fourierHistoryRotations_wellFormed (dir : PhaseDir) (w : Wire)
    (bs : List Bool) (k : Nat) : CircuitWellFormed (fourierHistoryRotations dir w bs k) := by
  induction bs generalizing k with
  | nil => simp [fourierHistoryRotations]
  | cons b bs ih =>
    cases b <;> simp [fourierHistoryRotations, fourierFeedForward, ih, Gate.WellFormed]

theorem semiclassicalFourier_wellFormed (dir : PhaseDir) (ws : List Wire) (prior : List Bool) :
    (semiclassicalFourier dir ws prior).WellFormed := by
  induction ws generalizing prior with
  | nil => trivial
  | cons w ws ih => exact ⟨fourierHistoryRotations_wellFormed _ _ _ _, ih _, ih _⟩

theorem semiclassicalFourier_bornMass (dir : PhaseDir) (ws : List Wire) (prior : List Bool) (ψ : State) :
    (semiclassicalFourier dir ws prior).run.bornMass ψ = normSq ψ :=
  AdaptiveCircuit.run_preservesBornMass _ (semiclassicalFourier_wellFormed _ _ _) ψ

theorem fourierOutcomes_nodup (n : Nat) : (fourierOutcomes n).Nodup := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [fourierOutcomes, List.nodup_append]
    refine ⟨ih.map (fun _ _ h => List.cons.inj h |>.2),
      ih.map (fun _ _ h => List.cons.inj h |>.2), ?_⟩
    simp
end
end ShorECDLP.Paper2607_13816
