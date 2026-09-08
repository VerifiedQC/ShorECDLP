import ShorECDLP.Submission.«2607_13816».EEA.StepControl
import ShorECDLP.Submission.«2607_13816».EEA.LengthUpdate

/-!
# Multi-control using a known constant workspace

The EEA wrapper keeps a known modulus register while initializing the encoded input length.
Its constant bits can be cleared, used by the existing clean v-chain, and restored. This
provides an explicit X/CX/CCX lowering without allocating a second large scratch register.
-/

namespace ShorECDLP.Paper2607_13816

open _root_.ShorECDLP.Classical

/-- Clear the known workspace, apply the clean multi-control, and restore its constant. -/
def knownScratchMCX (controls : List Wire) (target : Wire)
    (scratches : List Wire) (value : Nat) : Circuit :=
  xorConstant scratches value ++ mcxVChain controls target scratches ++
    xorConstant scratches value

private theorem xorConstantBits_constantBits (width value : Nat) :
    xorConstantBits (constantBits width value) value = List.replicate width false := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
      by_cases h : value.testBit 0 <;>
        simpa [constantBits, List.replicate_succ, xorConstantBits, h] using
          congrArg (List.cons false) (ih (value / 2))

/-- A known constant register becomes clean after its own constant-XOR stream. -/
theorem xorConstant_clears_known (scratches : List Wire) (value : Nat)
    (state : BasisState) (hnd : scratches.Nodup)
    (hknown : wireValues scratches state = constantBits scratches.length value) :
    Clean scratches (run (xorConstant scratches value) state) := by
  have h := (xorConstant_correct scratches value state hnd).1
  rw [hknown, xorConstantBits_constantBits] at h
  intro wire hwire
  have hm : run (xorConstant scratches value) state wire ∈
      wireValues scratches (run (xorConstant scratches value) state) :=
    List.mem_map.mpr ⟨wire, hwire, rfl⟩
  rw [h] at hm
  exact (List.mem_replicate.mp hm).2

private theorem wireAnd_eq_of_agrees (controls : List Wire) (a b : BasisState)
    (h : ∀ wire ∈ controls, a wire = b wire) : wireAnd controls a = wireAnd controls b := by
  induction controls with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireAnd]
      rw [h wire (by simp), ih (by intro w hw; exact h w (by simp [hw]))]

/-- The lowering toggles precisely the target conjunction and restores the complete workspace. -/
theorem run_knownScratchMCX (controls : List Wire) (target : Wire)
    (scratches : List Wire) (value : Nat) (state : BasisState)
    (henough : controls.length - 2 ≤ scratches.length)
    (hlayout : McxVChainLayout controls target scratches)
    (hknown : wireValues scratches state = constantBits scratches.length value) :
    run (knownScratchMCX controls target scratches value) state =
      state[target ↦ Bool.xor (state target) (wireAnd controls state)] := by
  have hparts := List.nodup_append.mp hlayout
  have ht := List.nodup_cons.mp hparts.2.1
  have hs := ht.2
  have hc : ∀ wire ∈ controls, wire ∉ scratches := by
    intro wire hw hm
    exact hparts.2.2 wire hw wire (by simp [hm]) rfl
  let cleared := run (xorConstant scratches value) state
  have hclean : Clean scratches cleared := xorConstant_clears_known scratches value state hs hknown
  have hlocal := xorConstant_usesOnly scratches value
  have htarget : cleared target = state target := hlocal.preservesOutside state ht.1
  have hcontrols : wireAnd controls cleared = wireAnd controls state :=
    wireAnd_eq_of_agrees controls cleared state (by
      intro wire hw
      exact hlocal.preservesOutside state (hc wire hw))
  rw [knownScratchMCX, run_append, run_append]
  rw [run_mcxVChain controls target scratches cleared henough hlayout hclean]
  rw [hlocal.run_upd_outside target _ cleared ht.1]
  rw [run_xorConstant_twice scratches value state hs, htarget, hcontrols]

/-- The known-workspace lowering contains only reversible classical gates. -/
theorem knownScratchMCX_wellFormed (controls : List Wire) (target : Wire)
    (scratches : List Wire) (value : Nat)
    (henough : controls.length - 2 ≤ scratches.length)
    (hlayout : McxVChainLayout controls target scratches) :
    CircuitWellFormed (knownScratchMCX controls target scratches value) := by
  simp only [knownScratchMCX, circuitWellFormed_append]
  exact ⟨⟨xorConstant_wellFormed scratches value,
    mcxVChain_wellFormed controls target scratches henough hlayout⟩,
    xorConstant_wellFormed scratches value⟩

theorem knownScratchMCX_HPFree (controls : List Wire) (target : Wire)
    (scratches : List Wire) (value : Nat) :
    HPFree (knownScratchMCX controls target scratches value) := by
  simp [knownScratchMCX, hpFree_append, mcxVChain_HPFree]

/-- Clearing/restoring a known constant costs X gates only; Toffoli, CX and T costs
are those of the explicit clean v-chain. -/
theorem knownScratchMCX_counts (controls : List Wire) (target : Wire)
    (scratches : List Wire) (value : Nat)
    (henough : controls.length - 2 ≤ scratches.length) :
    eeaToffoliCount (knownScratchMCX controls target scratches value) =
        mcxVChainToffoliCost controls.length ∧
    eeaCnotCount (knownScratchMCX controls target scratches value) =
        mcxVChainCnotCost controls.length ∧
    ShorECDLP.tCount (knownScratchMCX controls target scratches value) =
        7 * mcxVChainToffoliCost controls.length := by
  simp [knownScratchMCX, eeaToffoliCount_append, eeaCnotCount_append,
    tCount_append, mcxVChain_toffoliCount controls target scratches henough,
    mcxVChain_cnotCount, mcxVChain_tCount controls target scratches henough]

/-- Mixed-polarity control used for the first-one cases of length initialization. -/
def knownScratchControl (controls : List Wire) (pattern : Nat) (target : Wire)
    (scratches : List Wire) (value : Nat) : Circuit :=
  zeroMask controls pattern ++ knownScratchMCX controls target scratches value ++
    (zeroMask controls pattern).adjoint

/-- Negative controls do not disturb the known workspace; only the selected flag changes. -/
theorem run_knownScratchControl (controls : List Wire) (pattern : Nat) (target : Wire)
    (scratches : List Wire) (value : Nat) (state : BasisState)
    (hlayout : ComputeControlLayout controls target scratches)
    (hknown : wireValues scratches state = constantBits scratches.length value) :
    run (knownScratchControl controls pattern target scratches value) state =
      state[target ↦ Bool.xor (state target) (registerMatches controls pattern state)] := by
  have hp := List.nodup_append.mp hlayout.2
  have ht : target ∉ controls := by
    intro h
    exact hp.2.2 target h target (by simp) rfl
  have hs : ∀ wire ∈ scratches, wire ∉ controls := by
    intro wire hw hc
    exact hp.2.2 wire hc wire (by simp [hw]) rfl
  let mask := zeroMask controls pattern
  let masked := run mask state
  have hm := zeroMask_usesOnly controls pattern
  have hk : wireValues scratches masked = constantBits scratches.length value := by
    rw [← hknown]
    apply List.map_congr_left
    intro wire hw
    exact hm.preservesOutside state (hs wire hw)
  have htarget : masked target = state target := hm.preservesOutside state ht
  have hmatch : wireAnd controls masked = registerMatches controls pattern state :=
    wireAnd_run_zeroMask controls pattern state hp.1
  rw [knownScratchControl, run_append, run_append]
  rw [run_knownScratchMCX controls target scratches value masked hlayout.1 hlayout.2 hk]
  rw [hm.adjoint.run_upd_outside target _ masked ht]
  rw [run_adjoint_run_classical mask (zeroMask_wellFormed controls pattern) state,
    htarget, hmatch]

theorem knownScratchControl_wellFormed (controls : List Wire) (pattern : Nat) (target : Wire)
    (scratches : List Wire) (value : Nat)
    (hlayout : ComputeControlLayout controls target scratches) :
    CircuitWellFormed (knownScratchControl controls pattern target scratches value) := by
  simp only [knownScratchControl, circuitWellFormed_append]
  exact ⟨⟨zeroMask_wellFormed controls pattern,
    knownScratchMCX_wellFormed controls target scratches value hlayout.1 hlayout.2⟩,
    (circuitWellFormed_adjoint _).mpr (zeroMask_wellFormed controls pattern)⟩

theorem knownScratchControl_counts (controls : List Wire) (pattern : Nat) (target : Wire)
    (scratches : List Wire) (value : Nat)
    (henough : controls.length - 2 ≤ scratches.length) :
    eeaToffoliCount (knownScratchControl controls pattern target scratches value) =
        mcxVChainToffoliCost controls.length ∧
    eeaCnotCount (knownScratchControl controls pattern target scratches value) =
        mcxVChainCnotCost controls.length ∧
    ShorECDLP.tCount (knownScratchControl controls pattern target scratches value) =
        7 * mcxVChainToffoliCost controls.length := by
  have h := knownScratchMCX_counts controls target scratches value henough
  simp [knownScratchControl, eeaToffoliCount_append, eeaCnotCount_append, tCount_append,
    eeaToffoliCount_adjoint, eeaCnotCount_adjoint, tCount_adjoint,
    zeroMask_toffoliCount, zeroMask_cnotCount, zeroMask_tCount, h.1, h.2.1, h.2.2]

private theorem knownScratch_hpFree_adjoint {circuit : Circuit} (h : HPFree circuit) :
    HPFree circuit.adjoint := by
  induction circuit with
  | nil => simp
  | cons gate circuit ih =>
      have hp := (hpFree_cons gate circuit).mp h
      rw [circuit_adjoint_cons, hpFree_append]
      constructor
      · exact ih hp.2
      · cases gate <;> simp_all

theorem knownScratchControl_HPFree (controls : List Wire) (pattern : Nat) (target : Wire)
    (scratches : List Wire) (value : Nat) :
    HPFree (knownScratchControl controls pattern target scratches value) := by
  simp only [knownScratchControl, hpFree_append]
  exact ⟨⟨zeroMask_HPFree controls pattern,
    knownScratchMCX_HPFree controls target scratches value⟩,
    knownScratch_hpFree_adjoint (zeroMask_HPFree controls pattern)⟩

theorem knownScratchMCX_usesOnly (controls : List Wire) (target : Wire)
    (scratches : List Wire) (value : Nat) :
    PaperCircuitUsesOnly (controls ++ target :: scratches)
      (knownScratchMCX controls target scratches value) := by
  have hx : PaperCircuitUsesOnly (controls ++ target :: scratches) (xorConstant scratches value) := (xorConstant_usesOnly scratches value).mono (by
    intro w hw; simp [hw])
  exact (hx.append (mcxVChain_usesOnly controls target scratches)).append hx

theorem knownScratchControl_usesOnly (controls : List Wire) (pattern : Nat) (target : Wire)
    (scratches : List Wire) (value : Nat) :
    PaperCircuitUsesOnly (controls ++ target :: scratches)
      (knownScratchControl controls pattern target scratches value) := by
  have hx : PaperCircuitUsesOnly (controls ++ target :: scratches) (zeroMask controls pattern) := (zeroMask_usesOnly controls pattern).mono (by
    intro w hw; simp [hw])
  exact (hx.append (knownScratchMCX_usesOnly controls target scratches value)).append hx.adjoint

end ShorECDLP.Paper2607_13816
