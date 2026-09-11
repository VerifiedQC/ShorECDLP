import ShorECDLP.Framework.Quantum.CoherentRefinement
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum
noncomputable section
/-- Coherent dyadic phase with a reusable clean AND ancilla. -/
def fourierControlledPhase (dir : PhaseDir) (k : Nat) (c t anc : Wire) : Circuit :=
  [.CCX c t anc, .P dir k anc, .CCX c t anc]
/-- Rotation selected by an already observed computational-basis bit. -/
def fourierFeedForward (dir : PhaseDir) (k : Nat) (t : Wire) (b : Bool) : Circuit :=
  if b then [.P dir k t] else []
theorem fourierControlledPhase_ket (dir : PhaseDir) (k : Nat) (c t anc : Wire)
    (s : BasisState) (hc : c ≠ anc) (ht : t ≠ anc) (ha : s anc = false) :
    Quantum.run (fourierControlledPhase dir k c t anc) (ket s) =
      (if s c && s t then phaseCoeff dir k else 1) • ket s := by
  have hr : s[anc ↦ (s c && s t)][anc ↦ false] = s := by
    funext w
    by_cases hw : w = anc
    · subst w; simp [ha]
    · simp [upd, hw]
  simp only [fourierControlledPhase, run_cons, applyGate_CCX_ket]
  simp only [ha, Bool.false_xor]
  rw [applyGate_P_ket, applyGate_smul, applyGate_CCX_ket]
  simp [upd, hc, ht, hr, run_nil]
theorem fourierFeedForward_ket (dir : PhaseDir) (k : Nat) (t : Wire) (b : Bool)
    (s : BasisState) :
    Quantum.run (fourierFeedForward dir k t b) (ket s) =
      (if b && s t then phaseCoeff dir k else 1) • ket s := by
  cases b <;> simp [fourierFeedForward, run_cons, run_nil, onKet]
/-- Moving control measurement before a controlled phase preserves each unnormalised branch. -/
theorem fourierFeedForward_projectZ_ket (dir : PhaseDir) (k : Nat) (c t anc : Wire)
    (b : Bool) (s : BasisState) (hc : c ≠ anc) (ht : t ≠ anc) (ha : s anc = false) :
    projectZ c b (Quantum.run (fourierControlledPhase dir k c t anc) (ket s)) =
      Quantum.run (fourierFeedForward dir k t b) (projectZ c b (ket s)) := by
  rw [fourierControlledPhase_ket dir k c t anc s hc ht ha, map_smul, projectZ_ket]
  by_cases hb : s c = b
  · simp only [hb, if_true, fourierFeedForward_ket]
  · simp [hb]
/-- The same branch equality holds on arbitrary entangled inputs with clean workspace. -/
theorem fourierFeedForward_projectZ (dir : PhaseDir) (k : Nat) (c t anc : Wire)
    (b : Bool) (hc : c ≠ anc) (ht : t ≠ anc) (ψ : State)
    (hψ : SupportedOn (fun s => s anc = false) ψ) :
    projectZ c b (Quantum.run (fourierControlledPhase dir k c t anc) ψ) =
      Quantum.run (fourierFeedForward dir k t b) (projectZ c b ψ) := by
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add s z ψ hs hz ih =>
    have hψs : ψ s = 0 := by simpa using hs
    have hsa : s anc = false := hψ s (by simp [hψs, hz])
    have hrest : SupportedOn (fun s => s anc = false) ψ := by
      intro u hu
      apply hψ u
      by_cases hus : u = s
      · subst u; exact (hu hψs).elim
      · simp [hus, hu]
    have hsingle : Finsupp.single s z = z • ket s := by
      ext u; simp [ket]
    rw [map_add, map_add, map_add, map_add, hsingle, map_smul, map_smul,
      map_smul, map_smul, fourierFeedForward_projectZ_ket dir k c t anc b s hc ht hsa,
      ih hrest]
/-- History is most-recent outcome first; the nearest bit selects the quarter-turn. -/
def fourierHistoryRotations (dir : PhaseDir) (t : Wire) : List Bool → Nat → Circuit
  | [], _ => []
  | b :: bs, k => fourierFeedForward dir k t b ++ fourierHistoryRotations dir t bs (k+1)
def fourierHistoryAngle (dir : PhaseDir) : List Bool → Nat → ℝ
  | [], _ => 0
  | b :: bs, k => (if b then phaseAngle dir k else 0) + fourierHistoryAngle dir bs (k+1)
theorem fourierHistoryRotations_ket (dir : PhaseDir) (t : Wire) (bs : List Bool)
    (k : Nat) (s : BasisState) :
    Quantum.run (fourierHistoryRotations dir t bs k) (ket s) =
      (if s t then Complex.exp (Complex.I * (fourierHistoryAngle dir bs k : ℂ)) else 1) • ket s := by
  induction bs generalizing k with
  | nil => simp [fourierHistoryRotations, fourierHistoryAngle]
  | cons b bs ih =>
    rw [fourierHistoryRotations, run_append, fourierFeedForward_ket, map_smul, ih]
    cases b <;> cases h : s t <;>
      simp [fourierHistoryAngle, smul_smul, phaseCoeff, mul_add, Complex.exp_add]
end
end ShorECDLP.Paper2607_13816
