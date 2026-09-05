import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
import ShorECDLP.Submission.«2607_13816».EEA.Shift
import ShorECDLP.Submission.«2607_13816».EEA.WordNat

/-!
# Source-exact control and terminal-step wrappers

This module implements the small control-flow circuits used by the pinned FASTDUAL Algorithm-3
scheduler around its arithmetic blocks:

* `compute_control`, including the source's reverse-order cleanup mask;
* the terminal epoch spill into the low quotient-length bit and its literal inverse;
* the nonterminal R-block control, which excludes the all-ones truth-minus-one zero code; and
* the terminal padding rotation with its borrowed high epoch bit.

The arithmetic blocks themselves remain in their existing modules.  These wrappers expose exact
basis-state behavior, complete scratch restoration, literal inverse cancellation, locality,
physical well-formedness, and constructor-derived resource equations.  They do not yet compose a
complete indexed EEA step.
-/

namespace ShorECDLP.Paper2607_13816

open _root_.ShorECDLP.Classical

set_option linter.unusedSimpArgs false

private theorem stepControl_hpFree_adjoint
    {circuit : Circuit} (hfree : HPFree circuit) :
    HPFree circuit.adjoint := by
  induction circuit with
  | nil => simp
  | cons gate circuit ih =>
      have hparts := (hpFree_cons gate circuit).mp hfree
      rw [circuit_adjoint_cons, hpFree_append]
      constructor
      · exact ih hparts.2
      · cases gate <;> simp_all

private theorem run_run_adjoint_stepControl
    (circuit : Circuit) (hwellFormed : CircuitWellFormed circuit)
    (state : BasisState) :
    run circuit (run circuit.adjoint state) = state := by
  have hadjoint : CircuitWellFormed circuit.adjoint :=
    (circuitWellFormed_adjoint circuit).mpr hwellFormed
  have hinverse := run_adjoint_run_classical circuit.adjoint hadjoint state
  simpa [circuit_adjoint_adjoint] using hinverse

/-! ## Mixed-polarity source control -/

/-- Literal `_e.compute_control`: mask zero-valued literals in forward order, compute the clean
v-chain, then remove the mask in reverse order.  `value` is little-endian over `controls`. -/
def computeControl (controls : List Wire) (value : Nat)
    (target : Wire) (scratches : List Wire) : Circuit :=
  (zeroMask controls value ++ mcxVChain controls target scratches) ++
    (zeroMask controls value).adjoint

/-- Capacity and physical layout for the source control helper. -/
def ComputeControlLayout (controls : List Wire) (target : Wire)
    (scratches : List Wire) : Prop :=
  controls.length - 2 ≤ scratches.length ∧
    McxVChainLayout controls target scratches

private theorem computeControl_controlsNodup
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (hlayout : ComputeControlLayout controls target scratches) :
    controls.Nodup :=
  (List.nodup_append.mp hlayout.2).1

private theorem computeControl_target_not_mem
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (hlayout : ComputeControlLayout controls target scratches) :
    target ∉ controls := by
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hlayout.2
  intro hmem
  exact hcross target hmem target (by simp) rfl

private theorem computeControl_scratch_not_mem
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (hlayout : ComputeControlLayout controls target scratches) :
    ∀ wire ∈ scratches, wire ∉ controls := by
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hlayout.2
  intro wire hwire hmem
  exact hcross wire hmem wire (by simp [hwire]) rfl

/-- The helper toggles only `target`, exactly when every ordered literal matches.  All v-chain
scratch is restored. -/
theorem run_computeControl
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire) (state : BasisState)
    (hlayout : ComputeControlLayout controls target scratches)
    (hclean : Clean scratches state) :
    run (computeControl controls value target scratches) state =
      state[target ↦ Bool.xor (state target)
        (registerMatches controls value state)] := by
  let mask := zeroMask controls value
  let masked := run mask state
  have hcontrolsNodup :=
    computeControl_controlsNodup controls target scratches hlayout
  have htargetOutside :=
    computeControl_target_not_mem controls target scratches hlayout
  have hmaskUses : PaperCircuitUsesOnly controls mask :=
    zeroMask_usesOnly controls value
  have hmaskedTarget : masked target = state target :=
    hmaskUses.preservesOutside state htargetOutside
  have hmaskedClean : Clean scratches masked := by
    intro scratch hscratch
    change run mask state scratch = false
    rw [hmaskUses.preservesOutside state
      (computeControl_scratch_not_mem controls target scratches hlayout
        scratch hscratch)]
    exact hclean scratch hscratch
  have hchain := run_mcxVChain controls target scratches masked
    hlayout.1 hlayout.2 hmaskedClean
  have hmatch : wireAnd controls masked =
      registerMatches controls value state :=
    wireAnd_run_zeroMask controls value state hcontrolsNodup
  rw [computeControl, run_append, run_append]
  change run mask.adjoint
    (run (mcxVChain controls target scratches) masked) = _
  rw [hchain, hmaskUses.adjoint.run_upd_outside target
    (Bool.xor (masked target) (wireAnd controls masked)) masked htargetOutside,
    run_adjoint_run_classical mask (zeroMask_wellFormed controls value) state,
    hmaskedTarget, hmatch]

private theorem mcxVChainTail_stepControl_adjoint
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire) :
    (mcxVChainTail accumulator controls target scratches).adjoint =
      mcxVChainTail accumulator controls target scratches := by
  induction controls generalizing accumulator scratches with
  | nil => simp [mcxVChainTail]
  | cons control controls ih =>
      cases controls with
      | nil => simp [mcxVChainTail, Circuit.adjoint]
      | cons nextControl controls =>
          cases scratches with
          | nil => simp [mcxVChainTail]
          | cons scratch scratches =>
              simp [mcxVChainTail, circuit_adjoint_append, ih]

private theorem mcxVChain_stepControl_adjoint
    (controls : List Wire) (target : Wire) (scratches : List Wire) :
    (mcxVChain controls target scratches).adjoint =
      mcxVChain controls target scratches := by
  cases controls with
  | nil => simp [mcxVChain, Circuit.adjoint]
  | cons first controls =>
      cases controls with
      | nil => simp [mcxVChain, Circuit.adjoint]
      | cons second controls =>
          simp [mcxVChain, mcxVChainTail_stepControl_adjoint]

/-- The literal source helper is self-adjoint: its reverse cleanup becomes the forward setup of
the inverse and the v-chain itself is palindromic. -/
theorem computeControl_selfAdjoint
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire) :
    (computeControl controls value target scratches).adjoint =
      computeControl controls value target scratches := by
  simp [computeControl, circuit_adjoint_append,
    mcxVChain_stepControl_adjoint]

/-- Two calls to the source helper cancel on the complete basis state. -/
theorem run_computeControl_twice
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire) (state : BasisState)
    (hlayout : ComputeControlLayout controls target scratches) :
    run (computeControl controls value target scratches)
        (run (computeControl controls value target scratches) state) = state := by
  simpa [computeControl_selfAdjoint] using
    run_adjoint_run_classical
      (computeControl controls value target scratches)
      (by
        rw [computeControl, circuitWellFormed_append,
          circuitWellFormed_append]
        exact ⟨⟨zeroMask_wellFormed controls value,
          mcxVChain_wellFormed controls target scratches hlayout.1 hlayout.2⟩,
          (circuitWellFormed_adjoint (zeroMask controls value)).mpr
            (zeroMask_wellFormed controls value)⟩)
      state

theorem computeControl_usesOnly
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire) :
    PaperCircuitUsesOnly (controls ++ target :: scratches)
      (computeControl controls value target scratches) := by
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · exact (zeroMask_usesOnly controls value).mono (by
        intro wire hwire
        simp [hwire])
    · exact mcxVChain_usesOnly controls target scratches
  · exact (zeroMask_usesOnly controls value).adjoint.mono (by
      intro wire hwire
      simp [hwire])

@[simp]
theorem computeControl_HPFree
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire) :
    HPFree (computeControl controls value target scratches) := by
  rw [computeControl, hpFree_append, hpFree_append]
  exact ⟨⟨zeroMask_HPFree controls value,
    mcxVChain_HPFree controls target scratches⟩,
    stepControl_hpFree_adjoint (zeroMask_HPFree controls value)⟩

theorem computeControl_wellFormed
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire)
    (hlayout : ComputeControlLayout controls target scratches) :
    CircuitWellFormed (computeControl controls value target scratches) := by
  rw [computeControl, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨zeroMask_wellFormed controls value,
    mcxVChain_wellFormed controls target scratches hlayout.1 hlayout.2⟩,
    (circuitWellFormed_adjoint (zeroMask controls value)).mpr
      (zeroMask_wellFormed controls value)⟩

@[simp]
theorem computeControl_toffoliCount
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length) :
    eeaToffoliCount (computeControl controls value target scratches) =
      mcxVChainToffoliCost controls.length := by
  rw [computeControl, eeaToffoliCount_append, eeaToffoliCount_append,
    zeroMask_toffoliCount,
    mcxVChain_toffoliCount controls target scratches henough,
    eeaToffoliCount_adjoint, zeroMask_toffoliCount]
  omega

@[simp]
theorem computeControl_cnotCount
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire) :
    eeaCnotCount (computeControl controls value target scratches) =
      mcxVChainCnotCost controls.length := by
  rw [computeControl, eeaCnotCount_append, eeaCnotCount_append,
    zeroMask_cnotCount, mcxVChain_cnotCount,
    eeaCnotCount_adjoint, zeroMask_cnotCount]
  omega

@[simp]
theorem computeControl_tCount
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length) :
    ShorECDLP.tCount (computeControl controls value target scratches) =
      7 * mcxVChainToffoliCost controls.length := by
  rw [computeControl, tCount_append, tCount_append,
    zeroMask_tCount, mcxVChain_tCount controls target scratches henough,
    tCount_adjoint, zeroMask_tCount]
  omega

theorem computeControl_xCount
    (controls : List Wire) (value : Nat) (target : Wire)
    (scratches : List Wire) :
    eeaXCount (computeControl controls value target scratches) =
      2 * eeaXCount (zeroMask controls value) +
        eeaXCount (mcxVChain controls target scratches) := by
  rw [computeControl, eeaXCount_append, eeaXCount_append,
    eeaXCount_adjoint]
  omega

/-- A three-literal regression that distinguishes the source's forward setup order from its
reverse cleanup order. -/
theorem computeControl_reverseMask_source_regression
    (c₀ c₁ c₂ target scratch : Wire) :
    computeControl ([c₀, c₁, c₂] : List Wire) 0 target
        ([scratch] : List Wire) =
      [.X c₀, .X c₁, .X c₂,
        .CCX c₀ c₁ scratch, .CCX c₂ scratch target,
        .CCX c₀ c₁ scratch,
        .X c₂, .X c₁, .X c₀] := by
  rfl

/-! ## Nonterminal R-block control -/

/-- Source helper `_toggle_r_control_nonterminal`: compute the all-ones truth-minus-one zero flag,
add its negative literal to the ordered base conditions, and uncompute the flag before arithmetic
uses the resulting control.  `value` is reduced to the width of the base conditions so the
appended R-zero literal is always negative, exactly as in the source tuple list. -/
def rControlNonterminal (conditions : List Wire) (value : Nat)
    (control : Wire) (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire) : Circuit :=
  (mcxVChain lengthRPrime zeroRPrime scratches ++
    computeControl (conditions ++ [zeroRPrime])
      (value % 2 ^ conditions.length) control scratches) ++
      mcxVChain lengthRPrime zeroRPrime scratches

/-- The two shared v-chains and mixed-polarity control have enough clean scratch and compatible
physical layouts.  The explicit cross-condition prevents the output toggle from changing the
R-zero predicate used by the closing v-chain. -/
structure RControlNonterminalLayout
    (conditions : List Wire) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire) : Prop where
  rLayout : lengthRPrime.length - 2 ≤ scratches.length ∧
    McxVChainLayout lengthRPrime zeroRPrime scratches
  conditionLayout : ComputeControlLayout
    (conditions ++ [zeroRPrime]) control scratches
  control_not_r : control ∉ lengthRPrime

def rControlNonterminalPredicate
    (conditions : List Wire) (value : Nat)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (state : BasisState) : Bool :=
  registerMatches (conditions ++ [zeroRPrime])
    (value % 2 ^ conditions.length)
    state[zeroRPrime ↦ wireAnd lengthRPrime state]

private theorem rControl_zero_not_scratch
    (conditions : List Wire) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire)
    (hlayout : RControlNonterminalLayout conditions control
      lengthRPrime zeroRPrime scratches) :
    zeroRPrime ∉ scratches := by
  obtain ⟨_, htail, _⟩ := List.nodup_append.mp hlayout.rLayout.2
  exact (List.nodup_cons.mp htail).1

private theorem rControl_control_not_scratch
    (conditions : List Wire) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire)
    (hlayout : RControlNonterminalLayout conditions control
      lengthRPrime zeroRPrime scratches) :
    control ∉ scratches := by
  obtain ⟨_, htail, _⟩ :=
    List.nodup_append.mp hlayout.conditionLayout.2
  exact (List.nodup_cons.mp htail).1

private theorem rControl_zero_ne_control
    (conditions : List Wire) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire)
    (hlayout : RControlNonterminalLayout conditions control
      lengthRPrime zeroRPrime scratches) :
    zeroRPrime ≠ control := by
  obtain ⟨_, _, hcross⟩ :=
    List.nodup_append.mp hlayout.conditionLayout.2
  intro equality
  exact hcross zeroRPrime (by simp) control (by simp) equality

/-- Exact whole-state action.  The temporary R-zero flag and every shared scratch wire are
restored; only the requested control can change. -/
theorem run_rControlNonterminal
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire) (state : BasisState)
    (hlayout : RControlNonterminalLayout conditions control
      lengthRPrime zeroRPrime scratches)
    (hclean : Clean (zeroRPrime :: scratches) state) :
    run (rControlNonterminal conditions value control
      lengthRPrime zeroRPrime scratches) state =
      state[control ↦ Bool.xor (state control)
        (rControlNonterminalPredicate conditions value
          lengthRPrime zeroRPrime state)] := by
  let rZero := wireAnd lengthRPrime state
  let afterZero := state[zeroRPrime ↦ rZero]
  have hscratch : Clean scratches state := by
    intro wire hwire
    exact hclean wire (by simp [hwire])
  have hzeroFalse : state zeroRPrime = false := hclean zeroRPrime (by simp)
  have hfirst :
      run (mcxVChain lengthRPrime zeroRPrime scratches) state = afterZero := by
    simpa [afterZero, rZero, hzeroFalse] using
      run_mcxVChain lengthRPrime zeroRPrime scratches state
        hlayout.rLayout.1 hlayout.rLayout.2 hscratch
  have hcleanAfterZero : Clean scratches afterZero := by
    intro wire hwire
    have hne : wire ≠ zeroRPrime := by
      intro equality
      subst wire
      exact (rControl_zero_not_scratch conditions control lengthRPrime
        zeroRPrime scratches hlayout) hwire
    simp [afterZero, upd, hne, hscratch wire hwire]
  let matched := rControlNonterminalPredicate conditions value
    lengthRPrime zeroRPrime state
  let afterControl := afterZero[control ↦ Bool.xor (state control) matched]
  have hcontrolBefore : afterZero control = state control := by
    simp [afterZero, upd,
      (rControl_zero_ne_control conditions control lengthRPrime
        zeroRPrime scratches hlayout).symm]
  have hsecond :
      run (computeControl (conditions ++ [zeroRPrime])
        (value % 2 ^ conditions.length) control scratches)
        afterZero = afterControl := by
    simpa [afterControl, matched, rControlNonterminalPredicate,
      afterZero, rZero, hcontrolBefore] using
      run_computeControl (conditions ++ [zeroRPrime])
        (value % 2 ^ conditions.length) control scratches afterZero
        hlayout.conditionLayout hcleanAfterZero
  have hcleanAfterControl : Clean scratches afterControl := by
    intro wire hwire
    have hne : wire ≠ control := by
      intro equality
      subst wire
      exact (rControl_control_not_scratch conditions control lengthRPrime
        zeroRPrime scratches hlayout) hwire
    simp [afterControl, upd, hne, hcleanAfterZero wire hwire]
  have hzeroAfterControl : afterControl zeroRPrime = rZero := by
    simp [afterControl, afterZero, upd,
      rControl_zero_ne_control conditions control lengthRPrime
        zeroRPrime scratches hlayout]
  have hrAfterControl : wireAnd lengthRPrime afterControl = rZero := by
    change wireAnd lengthRPrime
      (afterZero[control ↦ Bool.xor (state control) matched]) = rZero
    rw [wireAnd_upd_not_mem _ _ control _ hlayout.control_not_r]
    change wireAnd lengthRPrime state[zeroRPrime ↦ rZero] = rZero
    have hzeroNotR : zeroRPrime ∉ lengthRPrime := by
      obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hlayout.rLayout.2
      intro hmem
      exact hcross zeroRPrime hmem zeroRPrime (by simp) rfl
    rw [wireAnd_upd_not_mem _ _ zeroRPrime _ hzeroNotR]
  rw [rControlNonterminal, run_append, run_append, hfirst, hsecond,
    run_mcxVChain lengthRPrime zeroRPrime scratches afterControl
      hlayout.rLayout.1 hlayout.rLayout.2 hcleanAfterControl,
    hzeroAfterControl, hrAfterControl]
  funext wire
  by_cases hwire : wire = zeroRPrime
  · subst wire
    simp [afterControl, afterZero, hzeroFalse, upd,
      rControl_zero_ne_control conditions control lengthRPrime
        zeroRPrime scratches hlayout]
  · simp [afterControl, afterZero, matched, upd, hwire,
      rControl_zero_ne_control conditions control lengthRPrime
        zeroRPrime scratches hlayout]

private theorem registerMatchesFrom_append_stepControl
    (first second : List Wire) (value bit : Nat) (state : BasisState) :
    registerMatchesFrom (first ++ second) value bit state =
      (registerMatchesFrom first value bit state &&
        registerMatchesFrom second value (bit + first.length) state) := by
  induction first generalizing bit with
  | nil => simp [registerMatchesFrom]
  | cons wire first ih =>
      rw [List.cons_append, registerMatchesFrom, registerMatchesFrom,
        ih (bit + 1)]
      simp only [List.length_cons]
      rw [show bit + 1 + first.length = bit + (first.length + 1) by omega]
      simp [Bool.and_assoc]

/-- The exact source predicate is the width-reduced base condition conjoined with
`ell_r' != 0`; no bit of the caller's natural can change the appended negative literal. -/
theorem rControlNonterminalPredicate_eq
    (conditions : List Wire) (value : Nat)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (state : BasisState)
    (hzeroNotConditions : zeroRPrime ∉ conditions) :
    rControlNonterminalPredicate conditions value
        lengthRPrime zeroRPrime state =
      (registerMatches conditions (value % 2 ^ conditions.length) state &&
        !wireAnd lengthRPrime state) := by
  rw [rControlNonterminalPredicate, registerMatches,
    registerMatchesFrom_append_stepControl]
  have hbase : registerMatchesFrom conditions
      (value % 2 ^ conditions.length) 0
      state[zeroRPrime ↦ wireAnd lengthRPrime state] =
      registerMatchesFrom conditions (value % 2 ^ conditions.length) 0 state :=
    registerMatchesFrom_upd_not_mem conditions
      (value % 2 ^ conditions.length) 0 state zeroRPrime
        (wireAnd lengthRPrime state) hzeroNotConditions
  rw [hbase]
  simp only [List.length_singleton, registerMatchesFrom, Nat.zero_add,
    Nat.add_zero, registerMatches]
  have hhigh :
      (value % 2 ^ conditions.length).testBit conditions.length = false :=
    Nat.testBit_lt_two_pow
      (Nat.mod_lt value (Nat.two_pow_pos conditions.length))
  rw [hhigh]
  cases wireAnd lengthRPrime state <;> simp [upd]

theorem rControlNonterminal_selfAdjoint
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire) :
    (rControlNonterminal conditions value control
      lengthRPrime zeroRPrime scratches).adjoint =
        rControlNonterminal conditions value control
          lengthRPrime zeroRPrime scratches := by
  simp [rControlNonterminal, circuit_adjoint_append,
    mcxVChain_stepControl_adjoint, computeControl_selfAdjoint]

theorem rControlNonterminal_wellFormed
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire)
    (hlayout : RControlNonterminalLayout conditions control
      lengthRPrime zeroRPrime scratches) :
    CircuitWellFormed (rControlNonterminal conditions value control
      lengthRPrime zeroRPrime scratches) := by
  rw [rControlNonterminal, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨mcxVChain_wellFormed lengthRPrime zeroRPrime scratches
      hlayout.rLayout.1 hlayout.rLayout.2,
    computeControl_wellFormed (conditions ++ [zeroRPrime])
      (value % 2 ^ conditions.length) control scratches
        hlayout.conditionLayout⟩,
    mcxVChain_wellFormed lengthRPrime zeroRPrime scratches
      hlayout.rLayout.1 hlayout.rLayout.2⟩

/-- Calling the same source helper after the arithmetic block clears the control and restores the
entire state, independently of the data values. -/
theorem run_rControlNonterminal_twice
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire) (state : BasisState)
    (hlayout : RControlNonterminalLayout conditions control
      lengthRPrime zeroRPrime scratches) :
    run (rControlNonterminal conditions value control
      lengthRPrime zeroRPrime scratches)
        (run (rControlNonterminal conditions value control
          lengthRPrime zeroRPrime scratches) state) = state := by
  simpa [rControlNonterminal_selfAdjoint] using
    run_adjoint_run_classical
      (rControlNonterminal conditions value control
        lengthRPrime zeroRPrime scratches)
      (rControlNonterminal_wellFormed conditions value control
        lengthRPrime zeroRPrime scratches hlayout) state

theorem rControlNonterminal_usesOnly
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire) :
    PaperCircuitUsesOnly
      (conditions ++ lengthRPrime ++ control :: zeroRPrime :: scratches)
      (rControlNonterminal conditions value control
        lengthRPrime zeroRPrime scratches) := by
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · exact (mcxVChain_usesOnly lengthRPrime zeroRPrime scratches).mono (by
        intro wire hwire
        simp only [List.mem_append, List.mem_cons] at hwire ⊢
        aesop)
    · exact (computeControl_usesOnly (conditions ++ [zeroRPrime])
        (value % 2 ^ conditions.length) control scratches).mono (by
          intro wire hwire
          simp only [List.mem_append, List.mem_cons] at hwire ⊢
          aesop)
  · exact (mcxVChain_usesOnly lengthRPrime zeroRPrime scratches).mono (by
      intro wire hwire
      simp only [List.mem_append, List.mem_cons] at hwire ⊢
      aesop)

@[simp]
theorem rControlNonterminal_HPFree
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire) :
    HPFree (rControlNonterminal conditions value control
      lengthRPrime zeroRPrime scratches) := by
  simp [rControlNonterminal]

@[simp]
theorem rControlNonterminal_toffoliCount
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire)
    (hrEnough : lengthRPrime.length - 2 ≤ scratches.length)
    (hcEnough : (conditions.length + 1) - 2 ≤ scratches.length) :
    eeaToffoliCount (rControlNonterminal conditions value control
      lengthRPrime zeroRPrime scratches) =
      2 * mcxVChainToffoliCost lengthRPrime.length +
        mcxVChainToffoliCost (conditions.length + 1) := by
  rw [rControlNonterminal, eeaToffoliCount_append,
    eeaToffoliCount_append,
    mcxVChain_toffoliCount lengthRPrime zeroRPrime scratches hrEnough,
    computeControl_toffoliCount (conditions ++ [zeroRPrime])
      (value % 2 ^ conditions.length) control scratches
        (by simpa using hcEnough)]
  simp
  omega

@[simp]
theorem rControlNonterminal_cnotCount
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire) :
    eeaCnotCount (rControlNonterminal conditions value control
      lengthRPrime zeroRPrime scratches) =
      2 * mcxVChainCnotCost lengthRPrime.length +
        mcxVChainCnotCost (conditions.length + 1) := by
  rw [rControlNonterminal, eeaCnotCount_append, eeaCnotCount_append,
    mcxVChain_cnotCount,
    computeControl_cnotCount]
  simp
  omega

@[simp]
theorem rControlNonterminal_tCount
    (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire)
    (scratches : List Wire)
    (hrEnough : lengthRPrime.length - 2 ≤ scratches.length)
    (hcEnough : (conditions.length + 1) - 2 ≤ scratches.length) :
    ShorECDLP.tCount (rControlNonterminal conditions value control
      lengthRPrime zeroRPrime scratches) =
      7 * (2 * mcxVChainToffoliCost lengthRPrime.length +
        mcxVChainToffoliCost (conditions.length + 1)) := by
  rw [rControlNonterminal, tCount_append, tCount_append,
    mcxVChain_tCount lengthRPrime zeroRPrime scratches hrEnough,
    computeControl_tCount (conditions ++ [zeroRPrime])
      (value % 2 ^ conditions.length) control scratches
        (by simpa using hcEnough)]
  simp
  omega

/-- Flattened source-order regression for the complete nonterminal R-control toggle.  The
temporary all-ones flag is erased before the caller's arithmetic block can begin. -/
theorem rControlNonterminal_source_regression
    (phase₁ phase₂ control r₀ r₁ r₂ zeroFlag scratch extra : Wire) :
    rControlNonterminal ([phase₁, phase₂] : List Wire) 3 control
        ([r₀, r₁, r₂] : List Wire) zeroFlag
        ([scratch, extra] : List Wire) =
      [.CCX r₀ r₁ scratch, .CCX r₂ scratch zeroFlag,
        .CCX r₀ r₁ scratch,
        .X zeroFlag,
        .CCX phase₁ phase₂ scratch, .CCX zeroFlag scratch control,
        .CCX phase₁ phase₂ scratch,
        .X zeroFlag,
        .CCX r₀ r₁ scratch, .CCX r₂ scratch zeroFlag,
        .CCX r₀ r₁ scratch] := by
  norm_num [rControlNonterminal]
  rfl

/-! ## Terminal epoch spill -/

/-- Forward source spill: make the low quotient-length bit zero on a terminal branch, then swap
the borrowed epoch into it. -/
def terminalEpochSpill (terminal shiftEpoch quotientLow : Wire) : Circuit :=
  [.CX terminal quotientLow] ++
    controlledSwap terminal shiftEpoch quotientLow

/-- Literal source restore in reverse gate order. -/
def terminalEpochRestore (terminal shiftEpoch quotientLow : Wire) : Circuit :=
  controlledSwap terminal shiftEpoch quotientLow ++
    [.CX terminal quotientLow]

def TerminalEpochLayout (terminal shiftEpoch quotientLow : Wire) : Prop :=
  [terminal, shiftEpoch, quotientLow].Nodup

private theorem controlledSwap_stepControl_selfAdjoint
    (control left right : Wire) :
    (controlledSwap control left right).adjoint =
      controlledSwap control left right := by
  rfl

theorem terminalEpochRestore_eq_adjoint
    (terminal shiftEpoch quotientLow : Wire) :
    terminalEpochRestore terminal shiftEpoch quotientLow =
      (terminalEpochSpill terminal shiftEpoch quotientLow).adjoint := by
  rw [terminalEpochSpill, circuit_adjoint_append,
    controlledSwap_stepControl_selfAdjoint]
  rfl

theorem terminalEpochSpill_wellFormed
    (terminal shiftEpoch quotientLow : Wire)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow) :
    CircuitWellFormed (terminalEpochSpill terminal shiftEpoch quotientLow) := by
  simp only [TerminalEpochLayout, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hlayout
  rw [terminalEpochSpill, circuitWellFormed_append]
  exact ⟨by
      simp [CircuitWellFormed, Gate.WellFormed, hlayout.1.2],
    controlledSwap_wellFormed terminal shiftEpoch quotientLow
      hlayout.1.1 hlayout.1.2 hlayout.2.1⟩

theorem terminalEpochRestore_wellFormed
    (terminal shiftEpoch quotientLow : Wire)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow) :
    CircuitWellFormed (terminalEpochRestore terminal shiftEpoch quotientLow) := by
  rw [terminalEpochRestore_eq_adjoint]
  exact (circuitWellFormed_adjoint
    (terminalEpochSpill terminal shiftEpoch quotientLow)).mpr
      (terminalEpochSpill_wellFormed terminal shiftEpoch quotientLow hlayout)

/-- Spill followed by the literal restore cancels on the complete basis state. -/
theorem run_terminalEpochRestore_after_spill
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow) :
    run (terminalEpochRestore terminal shiftEpoch quotientLow)
        (run (terminalEpochSpill terminal shiftEpoch quotientLow) state) = state := by
  rw [terminalEpochRestore_eq_adjoint]
  exact run_adjoint_run_classical
    (terminalEpochSpill terminal shiftEpoch quotientLow)
    (terminalEpochSpill_wellFormed terminal shiftEpoch quotientLow hlayout) state

/-- The literal spill also cancels a preceding restore on the complete basis state. -/
theorem run_terminalEpochSpill_after_restore
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow) :
    run (terminalEpochSpill terminal shiftEpoch quotientLow)
        (run (terminalEpochRestore terminal shiftEpoch quotientLow) state) = state := by
  rw [terminalEpochRestore_eq_adjoint]
  exact run_run_adjoint_stepControl
    (terminalEpochSpill terminal shiftEpoch quotientLow)
    (terminalEpochSpill_wellFormed terminal shiftEpoch quotientLow hlayout) state

/-- On the source's terminal boundary (`quotientLow = 1`), the spill clears the physical epoch
and stores its old value in the quotient bit. -/
theorem run_terminalEpochSpill_terminal
    (terminal shiftEpoch quotientLow : Wire) (state : BasisState)
    (hlayout : TerminalEpochLayout terminal shiftEpoch quotientLow)
    (hterminal : state terminal = true)
    (hquotient : state quotientLow = true) :
    run (terminalEpochSpill terminal shiftEpoch quotientLow) state =
      state[shiftEpoch ↦ false][quotientLow ↦ state shiftEpoch] := by
  simp only [TerminalEpochLayout, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hlayout
  rw [terminalEpochSpill, run_append]
  have hcx : run ([.CX terminal quotientLow] : Circuit) state =
      state[quotientLow ↦ false] := by
    funext wire
    by_cases hwire : wire = quotientLow
    · subst wire
      simp [run, applyGate, upd, hterminal, hquotient]
    · simp [run, applyGate, upd, hwire]
  rw [hcx, run_controlledSwap terminal shiftEpoch quotientLow]
  · rw [if_pos]
    · funext wire
      by_cases hwire : wire = shiftEpoch
      · subst wire
        simp [upd, hlayout.1.1, hlayout.2.1]
      · by_cases hwireLow : wire = quotientLow
        · subst wire
          simp [upd, hlayout.1.1, hlayout.2.1]
        · simp [upd, hwire, hwireLow]
    · simp [upd, hterminal, hlayout.1.2]
  · exact hlayout.1.1
  · exact hlayout.1.2
  · exact hlayout.2.1

theorem terminalEpochSpill_usesOnly
    (terminal shiftEpoch quotientLow : Wire) :
    PaperCircuitUsesOnly [terminal, shiftEpoch, quotientLow]
      (terminalEpochSpill terminal shiftEpoch quotientLow) := by
  apply PaperCircuitUsesOnly.append
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
  · exact controlledSwap_usesOnly terminal shiftEpoch quotientLow

theorem terminalEpochRestore_usesOnly
    (terminal shiftEpoch quotientLow : Wire) :
    PaperCircuitUsesOnly [terminal, shiftEpoch, quotientLow]
      (terminalEpochRestore terminal shiftEpoch quotientLow) := by
  rw [terminalEpochRestore_eq_adjoint]
  exact (terminalEpochSpill_usesOnly terminal shiftEpoch quotientLow).adjoint

@[simp]
theorem terminalEpochSpill_HPFree
    (terminal shiftEpoch quotientLow : Wire) :
    HPFree (terminalEpochSpill terminal shiftEpoch quotientLow) := by
  simp [terminalEpochSpill]

@[simp]
theorem terminalEpochRestore_HPFree
    (terminal shiftEpoch quotientLow : Wire) :
    HPFree (terminalEpochRestore terminal shiftEpoch quotientLow) := by
  rw [terminalEpochRestore_eq_adjoint]
  exact stepControl_hpFree_adjoint
    (terminalEpochSpill_HPFree terminal shiftEpoch quotientLow)

@[simp]
theorem terminalEpochSpill_toffoliCount
    (terminal shiftEpoch quotientLow : Wire) :
    eeaToffoliCount (terminalEpochSpill terminal shiftEpoch quotientLow) = 1 := by
  rw [terminalEpochSpill, eeaToffoliCount_append,
    controlledSwap_toffoliCount]
  rfl

@[simp]
theorem terminalEpochSpill_cnotCount
    (terminal shiftEpoch quotientLow : Wire) :
    eeaCnotCount (terminalEpochSpill terminal shiftEpoch quotientLow) = 3 := by
  rw [terminalEpochSpill, eeaCnotCount_append,
    controlledSwap_cnotCount]
  rfl

@[simp]
theorem terminalEpochSpill_tCount
    (terminal shiftEpoch quotientLow : Wire) :
    ShorECDLP.tCount (terminalEpochSpill terminal shiftEpoch quotientLow) = 7 := by
  rw [terminalEpochSpill, tCount_append, controlledSwap_tCount]
  rfl

@[simp]
theorem terminalEpochSpill_xCount
    (terminal shiftEpoch quotientLow : Wire) :
    eeaXCount (terminalEpochSpill terminal shiftEpoch quotientLow) = 0 := by
  rw [terminalEpochSpill, eeaXCount_append, controlledSwap_xCount]
  rfl

@[simp]
theorem terminalEpochRestore_toffoliCount
    (terminal shiftEpoch quotientLow : Wire) :
    eeaToffoliCount (terminalEpochRestore terminal shiftEpoch quotientLow) = 1 := by
  rw [terminalEpochRestore_eq_adjoint, eeaToffoliCount_adjoint,
    terminalEpochSpill_toffoliCount]

@[simp]
theorem terminalEpochRestore_cnotCount
    (terminal shiftEpoch quotientLow : Wire) :
    eeaCnotCount (terminalEpochRestore terminal shiftEpoch quotientLow) = 3 := by
  rw [terminalEpochRestore_eq_adjoint, eeaCnotCount_adjoint,
    terminalEpochSpill_cnotCount]

@[simp]
theorem terminalEpochRestore_tCount
    (terminal shiftEpoch quotientLow : Wire) :
    ShorECDLP.tCount (terminalEpochRestore terminal shiftEpoch quotientLow) = 7 := by
  rw [terminalEpochRestore_eq_adjoint, tCount_adjoint,
    terminalEpochSpill_tCount]

@[simp]
theorem terminalEpochRestore_xCount
    (terminal shiftEpoch quotientLow : Wire) :
    eeaXCount (terminalEpochRestore terminal shiftEpoch quotientLow) = 0 := by
  rw [terminalEpochRestore_eq_adjoint, eeaXCount_adjoint,
    terminalEpochSpill_xCount]

/-- Flattened source streams for the borrowed terminal-epoch spill and its literal restore. -/
theorem terminalEpoch_source_regression
    (terminal shiftEpoch quotientLow : Wire) :
    terminalEpochSpill terminal shiftEpoch quotientLow =
        [.CX terminal quotientLow, .CX quotientLow shiftEpoch,
          .CCX terminal shiftEpoch quotientLow, .CX quotientLow shiftEpoch] ∧
      terminalEpochRestore terminal shiftEpoch quotientLow =
        [.CX quotientLow shiftEpoch, .CCX terminal shiftEpoch quotientLow,
          .CX quotientLow shiftEpoch, .CX terminal quotientLow] := by
  constructor <;> rfl

/-! ## Terminal padding rotation -/

/-- Minimal source scratch split for terminal padding.  `wrapped` is both the first ripple carry
and the equality flag; `equalityExtra` is the one additional wire needed so the equality v-chain
can use the remaining carry bank while the flag is live. -/
structure TerminalPaddingRegisters where
  terminal : Wire
  shiftEpoch : Wire
  work2 : List Wire
  lengthS : List Wire
  wrapped : Wire
  carryTail : List Wire
  equalityExtra : Wire

namespace TerminalPaddingRegisters

def carries (registers : TerminalPaddingRegisters) : List Wire :=
  registers.wrapped :: registers.carryTail

def equalityScratch (registers : TerminalPaddingRegisters) : List Wire :=
  registers.carryTail ++ [registers.equalityExtra]

def scratch (registers : TerminalPaddingRegisters) : List Wire :=
  registers.wrapped :: registers.equalityScratch

def usedWires (registers : TerminalPaddingRegisters) : List Wire :=
  registers.terminal :: registers.shiftEpoch ::
    registers.work2 ++ registers.lengthS ++ registers.scratch

end TerminalPaddingRegisters

/-- Exact-minimal source capacity and a duplicate-free physical allocation.  The equality helper
receives the carry tail plus one extra wire, so the complete terminal scratch has exactly the
source minimum `lengthS.length` (and at least two wires). -/
structure TerminalPaddingLayout (registers : TerminalPaddingRegisters) : Prop where
  carry_capacity :
    registers.lengthS.length = registers.carries.length + 1
  nodup : registers.usedWires.Nodup

/-- Fixed-horizon guard checked by the pinned Python helper.  It is a scheduling precondition, not
a gate parameter: the borrowed epoch extends the low shift word by one logical bit. -/
def TerminalPaddingScheduleFits
    (registers : TerminalPaddingRegisters) (n maxSteps : Nat) : Prop :=
  maxSteps - 4 * n < 2 ^ (registers.lengthS.length + 1)

private theorem terminalPadding_rotationNodup
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    (registers.terminal :: registers.work2).Nodup := by
  apply List.Nodup.sublist _ hlayout.nodup
  simp [TerminalPaddingRegisters.usedWires]

private theorem terminalPadding_incrementNodup
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    (registers.terminal :: registers.lengthS ++ registers.carries).Nodup := by
  apply List.Nodup.sublist _ hlayout.nodup
  have hcarries : registers.carries.Sublist registers.scratch := by
    change registers.carries.Sublist
      (registers.carries ++ [registers.equalityExtra])
    exact List.sublist_append_left registers.carries
      ([registers.equalityExtra] : List Wire)
  have hlength :
      (registers.lengthS ++ registers.carries).Sublist
        (registers.lengthS ++ registers.scratch) :=
    (List.Sublist.refl registers.lengthS).append hcarries
  have hwork :
      (registers.lengthS ++ registers.carries).Sublist
        (registers.work2 ++ registers.lengthS ++ registers.scratch) := by
    exact hlength.trans (by
      rw [List.append_assoc]
      exact List.sublist_append_right registers.work2
        (registers.lengthS ++ registers.scratch))
  simpa [TerminalPaddingRegisters.usedWires, List.append_assoc] using
    (hwork.cons registers.shiftEpoch).cons₂ registers.terminal

private theorem terminalPadding_eqLayout
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    ComputeControlLayout registers.lengthS registers.wrapped
      registers.equalityScratch := by
  constructor
  · have hcapacity := hlayout.carry_capacity
    simp [TerminalPaddingRegisters.carries] at hcapacity
    simp [TerminalPaddingRegisters.equalityScratch]
    omega
  · apply List.Nodup.sublist _ hlayout.nodup
    have htail :
        (registers.lengthS ++ registers.wrapped :: registers.equalityScratch).Sublist
          (registers.work2 ++
            (registers.lengthS ++ registers.wrapped :: registers.equalityScratch)) :=
      List.sublist_append_right registers.work2 _
    simpa [McxVChainLayout, TerminalPaddingRegisters.usedWires,
      TerminalPaddingRegisters.scratch, List.append_assoc] using
      (htail.cons registers.shiftEpoch).cons registers.terminal

private theorem terminalPadding_markNodup
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    [registers.terminal, registers.wrapped, registers.shiftEpoch].Nodup := by
  have hordered :
      [registers.terminal, registers.shiftEpoch, registers.wrapped].Nodup := by
    apply List.Nodup.sublist _ hlayout.nodup
    simp [TerminalPaddingRegisters.usedWires,
      TerminalPaddingRegisters.scratch]
  exact hordered.perm
    (List.Perm.cons registers.terminal
      (List.Perm.swap registers.wrapped registers.shiftEpoch ([] : List Wire)))

private theorem terminalPadding_scratchNodup
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    registers.scratch.Nodup := by
  apply List.Nodup.sublist _ hlayout.nodup
  have htail : registers.scratch.Sublist
      (registers.lengthS ++ registers.scratch) :=
    List.sublist_append_right registers.lengthS registers.scratch
  have hwork : registers.scratch.Sublist
      (registers.work2 ++ registers.lengthS ++ registers.scratch) :=
    htail.trans (by
      rw [List.append_assoc]
      exact List.sublist_append_right registers.work2
        (registers.lengthS ++ registers.scratch))
  simpa [TerminalPaddingRegisters.usedWires] using
    (hwork.cons registers.shiftEpoch).cons registers.terminal

private theorem terminalPadding_scratch_not_work2
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    ∀ wire ∈ registers.scratch, wire ∉ registers.work2 := by
  intro wire hscratch hwork
  have hafterTerminal := (List.nodup_cons.mp hlayout.nodup).2
  have hafterEpoch := (List.nodup_cons.mp hafterTerminal).2
  have hrest :
      (registers.work2 ++ (registers.lengthS ++ registers.scratch)).Nodup := by
    simpa [TerminalPaddingRegisters.usedWires, List.append_assoc] using hafterEpoch
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hrest
  exact (hcross wire hwork wire
    (List.mem_append_right registers.lengthS hscratch)) rfl

private theorem terminalPadding_shiftEpoch_not_scratch
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    registers.shiftEpoch ∉ registers.scratch := by
  have hafterTerminal := (List.nodup_cons.mp hlayout.nodup).2
  have hnot := (List.nodup_cons.mp hafterTerminal).1
  intro hmem
  exact hnot (by simp [hmem])

private theorem terminalPadding_shiftEpoch_not_lengthS
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    registers.shiftEpoch ∉ registers.lengthS := by
  have hafterTerminal := (List.nodup_cons.mp hlayout.nodup).2
  have hnot := (List.nodup_cons.mp hafterTerminal).1
  intro hmem
  exact hnot (by simp [hmem])

private theorem terminalPadding_terminal_not_scratch
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    registers.terminal ∉ registers.scratch := by
  have hnot := (List.nodup_cons.mp hlayout.nodup).1
  intro hmem
  exact hnot (by
    simp [TerminalPaddingRegisters.usedWires, hmem])

private theorem terminalPadding_scratch_not_lengthS
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    ∀ wire ∈ registers.scratch, wire ∉ registers.lengthS := by
  have hafterTerminal := (List.nodup_cons.mp hlayout.nodup).2
  have hafterEpoch := (List.nodup_cons.mp hafterTerminal).2
  have hrest :
      (registers.work2 ++ (registers.lengthS ++ registers.scratch)).Nodup := by
    simpa [TerminalPaddingRegisters.usedWires, List.append_assoc] using hafterEpoch
  obtain ⟨_, htail, _⟩ := List.nodup_append.mp hrest
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp htail
  intro wire hscratch hlength
  exact (hcross wire hlength wire hscratch) rfl

/-- Prefix before the low-word wrap test: rotate Work2 left and increment the truth-minus-one
shift word under the terminal control. -/
def terminalPaddingPrefix (registers : TerminalPaddingRegisters) : Circuit :=
  controlledRotateLeftOne registers.terminal registers.work2 ++
    controlledIncrement registers.terminal registers.lengthS registers.carries

/-- Compute the low-word wrap flag, toggle the borrowed epoch, and clear the flag. -/
def terminalPaddingEpochUpdate (registers : TerminalPaddingRegisters) : Circuit :=
  (computeControl registers.lengthS 0 registers.wrapped registers.equalityScratch ++
    [.CCX registers.terminal registers.wrapped registers.shiftEpoch]) ++
      computeControl registers.lengthS 0 registers.wrapped registers.equalityScratch

/-- Literal `_append_terminal_padding_rotation`. -/
def terminalPaddingForward (registers : TerminalPaddingRegisters) : Circuit :=
  terminalPaddingPrefix registers ++ terminalPaddingEpochUpdate registers

/-- Literal `_append_terminal_padding_rotation_inverse`: wrap test first, then decrement and the
reverse adjacent-Fredkin cascade. -/
def terminalPaddingInverse (registers : TerminalPaddingRegisters) : Circuit :=
  (terminalPaddingEpochUpdate registers ++
    controlledDecrement registers.terminal registers.lengthS registers.carries) ++
      controlledRotateRightOne registers.terminal registers.work2

/-- Gate-independent forward terminal-padding transition.  The two word updates are written
directly as little-endian Boolean words; the final epoch toggle tests the updated low word. -/
def terminalPaddingForwardState
    (registers : TerminalPaddingRegisters) (state : BasisState) : BasisState :=
  let rotatedBits :=
    if state registers.terminal then
      rotateLeftOne (wireValues registers.work2 state)
    else wireValues registers.work2 state
  let rotated :=
    writeReg registers.work2 (boolWordToNat rotatedBits) state
  let incrementedBits :=
    incrementBits (rotated registers.terminal)
      (wireValues registers.lengthS rotated)
  let incremented :=
    writeReg registers.lengthS (boolWordToNat incrementedBits) rotated
  incremented[registers.shiftEpoch ↦
    Bool.xor (incremented registers.shiftEpoch)
      (incremented registers.terminal &&
        registerMatches registers.lengthS 0 incremented)]

/-- Gate-independent inverse terminal-padding transition.  The source tests the current low word
before decrementing it and rotating Work2 one position to the right. -/
def terminalPaddingInverseState
    (registers : TerminalPaddingRegisters) (state : BasisState) : BasisState :=
  let marked := state[registers.shiftEpoch ↦
    Bool.xor (state registers.shiftEpoch)
      (state registers.terminal &&
        registerMatches registers.lengthS 0 state)]
  let decrementedBits :=
    decrementBits (marked registers.terminal)
      (wireValues registers.lengthS marked)
  let decremented :=
    writeReg registers.lengthS (boolWordToNat decrementedBits) marked
  let rotatedBits :=
    if decremented registers.terminal then
      (wireValues registers.work2 decremented).rotate
        (registers.work2.length - 1)
    else wireValues registers.work2 decremented
  writeReg registers.work2 (boolWordToNat rotatedBits) decremented

private theorem terminalPaddingEpochUpdate_wellFormed
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    CircuitWellFormed (terminalPaddingEpochUpdate registers) := by
  have heq := terminalPadding_eqLayout registers hlayout
  have hmark := terminalPadding_markNodup registers hlayout
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hmark
  rw [terminalPaddingEpochUpdate, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨computeControl_wellFormed registers.lengthS 0 registers.wrapped
      registers.equalityScratch heq,
    by simp [CircuitWellFormed, Gate.WellFormed,
      hmark.1.1, hmark.1.2, hmark.2.1]⟩,
    computeControl_wellFormed registers.lengthS 0 registers.wrapped
      registers.equalityScratch heq⟩

private theorem terminalPaddingEpochUpdate_selfAdjoint
    (registers : TerminalPaddingRegisters) :
    (terminalPaddingEpochUpdate registers).adjoint =
      terminalPaddingEpochUpdate registers := by
  unfold terminalPaddingEpochUpdate
  rw [circuit_adjoint_append, computeControl_selfAdjoint,
    circuit_adjoint_append, computeControl_selfAdjoint]
  simp [Circuit.adjoint, List.append_assoc]

private theorem run_terminalPaddingEpochUpdate_twice
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers) :
    run (terminalPaddingEpochUpdate registers)
        (run (terminalPaddingEpochUpdate registers) state) = state := by
  simpa [terminalPaddingEpochUpdate_selfAdjoint] using
    run_adjoint_run_classical (terminalPaddingEpochUpdate registers)
      (terminalPaddingEpochUpdate_wellFormed registers hlayout) state

/-- The wrap-test block restores every scratch wire and changes only the borrowed epoch. -/
private theorem run_terminalPaddingEpochUpdate
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    run (terminalPaddingEpochUpdate registers) state =
      state[registers.shiftEpoch ↦
        Bool.xor (state registers.shiftEpoch)
          (state registers.terminal &&
            registerMatches registers.lengthS 0 state)] := by
  let matched := registerMatches registers.lengthS 0 state
  let flagged := state[registers.wrapped ↦ matched]
  have heq := terminalPadding_eqLayout registers hlayout
  have hscratchNodup := terminalPadding_scratchNodup registers hlayout
  have hwrappedFalse : state registers.wrapped = false :=
    hclean registers.wrapped (by
      simp [TerminalPaddingRegisters.scratch])
  have heqClean : Clean registers.equalityScratch state := by
    intro wire hwire
    exact hclean wire (by
      simp [TerminalPaddingRegisters.scratch, hwire])
  have hfirst : run (computeControl registers.lengthS 0 registers.wrapped
      registers.equalityScratch) state = flagged := by
    simpa [flagged, matched, hwrappedFalse] using
      run_computeControl registers.lengthS 0 registers.wrapped
        registers.equalityScratch state heq heqClean
  let marked := flagged[registers.shiftEpoch ↦
    Bool.xor (flagged registers.shiftEpoch)
      (flagged registers.terminal && flagged registers.wrapped)]
  have hmark : run ([.CCX registers.terminal registers.wrapped
      registers.shiftEpoch] : Circuit) flagged = marked := rfl
  have hwrappedNotEqScratch :
      registers.wrapped ∉ registers.equalityScratch := by
    simpa [TerminalPaddingRegisters.scratch] using
      (List.nodup_cons.mp hscratchNodup).1
  have hshiftNotEqScratch :
      registers.shiftEpoch ∉ registers.equalityScratch := by
    intro hmem
    exact terminalPadding_shiftEpoch_not_scratch registers hlayout (by
      simp [TerminalPaddingRegisters.scratch, hmem])
  have hcleanMarked : Clean registers.equalityScratch marked := by
    intro wire hwire
    have hwWrapped : wire ≠ registers.wrapped := by
      intro equality
      subst wire
      exact hwrappedNotEqScratch hwire
    have hwShift : wire ≠ registers.shiftEpoch := by
      intro equality
      subst wire
      exact hshiftNotEqScratch hwire
    simp [marked, flagged, upd, hwWrapped, hwShift,
      heqClean wire hwire]
  have hwrappedMarked : marked registers.wrapped = matched := by
    have hmarkNodup := terminalPadding_markNodup registers hlayout
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hmarkNodup
    simp [marked, flagged, upd, hmarkNodup.2.1,
      Ne.symm hmarkNodup.2.1]
  have hmatchMarked : registerMatches registers.lengthS 0 marked = matched := by
    have hwrappedNotLength : registers.wrapped ∉ registers.lengthS :=
      computeControl_target_not_mem registers.lengthS registers.wrapped
        registers.equalityScratch heq
    have hshiftNotLength :=
      terminalPadding_shiftEpoch_not_lengthS registers hlayout
    change registerMatchesFrom registers.lengthS 0 0
      (flagged[registers.shiftEpoch ↦
        Bool.xor (flagged registers.shiftEpoch)
          (flagged registers.terminal && flagged registers.wrapped)]) = matched
    rw [registerMatchesFrom_upd_not_mem _ _ _ _ _ _ hshiftNotLength]
    change registerMatchesFrom registers.lengthS 0 0
      state[registers.wrapped ↦ matched] = matched
    rw [registerMatchesFrom_upd_not_mem _ _ _ _ _ _ hwrappedNotLength]
    rfl
  have hsecond := run_computeControl registers.lengthS 0 registers.wrapped
    registers.equalityScratch marked heq hcleanMarked
  rw [terminalPaddingEpochUpdate, run_append, run_append, hfirst, hmark,
    hsecond, hwrappedMarked, hmatchMarked]
  funext wire
  by_cases hwWrapped : wire = registers.wrapped
  · subst wire
    have hmarkNodup := terminalPadding_markNodup registers hlayout
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hmarkNodup
    cases matched <;>
      simp [marked, flagged, hwrappedFalse, upd,
        hmarkNodup.1.1, hmarkNodup.2.1, Ne.symm hmarkNodup.2.1]
  · by_cases hwShift : wire = registers.shiftEpoch
    · subst wire
      have hmarkNodup := terminalPadding_markNodup registers hlayout
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or] at hmarkNodup
      simp [marked, flagged, matched, upd, hmarkNodup.1.1,
        Ne.symm hmarkNodup.1.1, hmarkNodup.1.2,
        hmarkNodup.2.1, Ne.symm hmarkNodup.2.1]
    · simp [marked, flagged, upd, hwWrapped, hwShift]

private theorem decrementBits_incrementBits
    (carry : Bool) (bits : List Bool) :
    decrementBits carry (incrementBits carry bits) = bits := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih =>
      cases carry <;> cases bit <;>
        simp [incrementBits, decrementBits, ih]

private theorem incrementBits_decrementBits
    (carry : Bool) (bits : List Bool) :
    incrementBits carry (decrementBits carry bits) = bits := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih =>
      cases carry <;> cases bit <;>
        simp [incrementBits, decrementBits, ih]

private theorem basisState_eq_of_word
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    (houtside : ∀ wire, wire ∉ wires → left wire = right wire) :
    left = right := by
  induction wires with
  | nil =>
      funext wire
      exact houtside wire (by simp)
  | cons head tail ih =>
      have hhead : left head = right head := by
        have h := congrArg List.head? hvalues
        simpa [wireValues] using h
      have htail : wireValues tail left = wireValues tail right := by
        have h := congrArg List.tail hvalues
        simpa [wireValues] using h
      apply ih htail
      intro wire hwire
      by_cases heq : wire = head
      · subst wire
        exact hhead
      · exact houtside wire (by simp [heq, hwire])

private theorem stepControl_writeReg_preservesOutside
    (register : List Wire) (value : Nat) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    writeReg register value state wire = state wire := by
  induction register generalizing value state with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at hwire
      rw [writeReg, ih (value / 2) _ hwire.2]
      exact upd_other state head (value.testBit 0) hwire.1

private theorem stepControl_boolWordToNat_testBit_zero
    (bit : Bool) (bits : List Bool) :
    (boolWordToNat (bit :: bits)).testBit 0 = bit := by
  cases bit <;>
    simp [boolWordToNat, Nat.testBit_zero, Nat.add_mod]

private theorem stepControl_boolWordToNat_div_two
    (bit : Bool) (bits : List Bool) :
    boolWordToNat (bit :: bits) / 2 = boolWordToNat bits := by
  cases bit
  · simp [boolWordToNat]
  · simp only [boolWordToNat, Bool.toNat_true]
    omega

private theorem stepControl_wireValues_writeReg_boolWord
    (register : List Wire) (bits : List Bool) (state : BasisState)
    (hnd : register.Nodup) (hlength : bits.length = register.length) :
    wireValues register (writeReg register (boolWordToNat bits) state) = bits := by
  induction register generalizing bits state with
  | nil =>
      have hbits : bits = [] :=
        List.length_eq_zero_iff.mp (by simpa using hlength)
      subst bits
      rfl
  | cons head tail ih =>
      cases bits with
      | nil => simp at hlength
      | cons bit bits =>
          have hhead : head ∉ tail := (List.nodup_cons.mp hnd).1
          have htail : tail.Nodup := (List.nodup_cons.mp hnd).2
          have htailLength : bits.length = tail.length := by
            simpa using hlength
          rw [writeReg, stepControl_boolWordToNat_div_two]
          simp only [wireValues, List.map_cons]
          rw [stepControl_writeReg_preservesOutside tail (boolWordToNat bits)
              _ hhead,
            stepControl_boolWordToNat_testBit_zero, upd_same]
          change bit :: wireValues tail
              (writeReg tail (boolWordToNat bits) state[head ↦ bit]) =
            bit :: bits
          rw [ih bits _ htail htailLength]

private theorem stepControl_state_eq_writeReg_boolWord
    (register : List Wire) (bits : List Bool)
    (before after : BasisState)
    (hnd : register.Nodup) (hlength : bits.length = register.length)
    (hvalues : wireValues register after = bits)
    (houtside : ∀ wire, wire ∉ register → after wire = before wire) :
    after = writeReg register (boolWordToNat bits) before := by
  apply basisState_eq_of_word register after _
  · calc
      wireValues register after = bits := hvalues
      _ = wireValues register
          (writeReg register (boolWordToNat bits) before) :=
        (stepControl_wireValues_writeReg_boolWord register bits before hnd
          hlength).symm
  · intro wire hwire
    rw [houtside wire hwire,
      stepControl_writeReg_preservesOutside register _ before hwire]

private theorem stepControl_rotateLeftOne_length (bits : List α) :
    (rotateLeftOne bits).length = bits.length := by
  cases bits <;> simp [rotateLeftOne]

private theorem stepControl_decrementBits_length
    (borrow : Bool) (bits : List Bool) :
    (decrementBits borrow bits).length = bits.length := by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih => simp [decrementBits, ih]

private theorem run_controlledRotateLeftOne_eq_writeReg
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    run (controlledRotateLeftOne control register) state =
      writeReg register
        (boolWordToNat
          (if state control then rotateLeftOne (wireValues register state)
            else wireValues register state)) state := by
  apply stepControl_state_eq_writeReg_boolWord register _ state _
  · exact (List.nodup_cons.mp hnd).2
  · split
    · simpa [wireValues] using
        stepControl_rotateLeftOne_length (wireValues register state)
    · simp [wireValues]
  · exact run_controlledRotateLeftOne_values control register state hnd
  · intro wire hwire
    by_cases hcontrol : wire = control
    · subst wire
      exact controlledRotateLeftOne_control control register state
        (List.nodup_cons.mp hnd).1
    · exact
        (controlledRotateLeftOne_usesOnly control register).preservesOutside
          state (by simp [hcontrol, hwire])

private theorem run_controlledIncrement_eq_writeReg
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledIncrement control register carries) state =
      writeReg register
        (boolWordToNat
          (incrementBits (state control) (wireValues register state))) state := by
  have hcorrect := controlledIncrement_correct control register carries state
    hlength hnd hclean
  apply stepControl_state_eq_writeReg_boolWord register _ state _
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  · simp [wireValues]
  · exact hcorrect.1
  · exact hcorrect.2

private theorem run_controlledDecrement_eq_writeReg
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledDecrement control register carries) state =
      writeReg register
        (boolWordToNat
          (decrementBits (state control) (wireValues register state))) state := by
  have hcorrect := controlledDecrement_correct control register carries state
    hlength hnd hclean
  apply stepControl_state_eq_writeReg_boolWord register _ state _
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  · simpa [wireValues] using
      stepControl_decrementBits_length (state control)
        (wireValues register state)
  · exact hcorrect.1
  · exact hcorrect.2

private theorem stepControl_rotateLeftOne_eq_rotate_one (bits : List α) :
    rotateLeftOne bits = bits.rotate 1 := by
  cases bits <;> simp [rotateLeftOne]

private theorem stepControl_rotateLeftOne_rotate_right (bits : List α) :
    (rotateLeftOne bits).rotate (bits.length - 1) = bits := by
  cases bits with
  | nil => rfl
  | cons head tail =>
      rw [stepControl_rotateLeftOne_eq_rotate_one, List.rotate_rotate]
      have hsum : 1 + ((head :: tail).length - 1) = (head :: tail).length := by
        simp [Nat.add_comm]
      rw [hsum, List.rotate_length]

private theorem controlledRotateRightOne_control_stepControl
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    run (controlledRotateRightOne control register) state control =
      state control := by
  let after := run (controlledRotateRightOne control register) state
  have hleft := controlledRotateLeftOne_control control register after
    (List.nodup_cons.mp hnd).1
  have hcancel := run_run_adjoint_stepControl
    (controlledRotateLeftOne control register)
    (controlledRotateLeftOne_wellFormed control register hnd) state
  calc
    after control =
        run (controlledRotateLeftOne control register) after control := hleft.symm
    _ = state control := congrFun hcancel control

private theorem run_controlledRotateRightOne_values_stepControl
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    wireValues register
        (run (controlledRotateRightOne control register) state) =
      if state control then
        (wireValues register state).rotate (register.length - 1)
      else wireValues register state := by
  let after := run (controlledRotateRightOne control register) state
  have hcancel := run_run_adjoint_stepControl
    (controlledRotateLeftOne control register)
    (controlledRotateLeftOne_wellFormed control register hnd) state
  have hcancel' :
      run (controlledRotateLeftOne control register) after = state := by
    simpa [after, controlledRotateRightOne] using hcancel
  have hleft := run_controlledRotateLeftOne_values control register after hnd
  have hcontrol := controlledRotateRightOne_control_stepControl control register state hnd
  change after control = state control at hcontrol
  rw [hcancel', hcontrol] at hleft
  cases hc : state control
  · simpa [hc] using hleft.symm
  · simp only [hc, if_true] at hleft ⊢
    calc
      wireValues register after =
          (rotateLeftOne (wireValues register after)).rotate
            ((wireValues register after).length - 1) :=
        (stepControl_rotateLeftOne_rotate_right
          (wireValues register after)).symm
      _ = (wireValues register state).rotate
            ((wireValues register after).length - 1) := by rw [← hleft]
      _ = (wireValues register state).rotate (register.length - 1) := by
        simp [wireValues]

private theorem run_controlledRotateRightOne_eq_writeReg
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    run (controlledRotateRightOne control register) state =
      writeReg register
        (boolWordToNat
          (if state control then
            (wireValues register state).rotate (register.length - 1)
          else wireValues register state)) state := by
  apply stepControl_state_eq_writeReg_boolWord register _ state _
  · exact (List.nodup_cons.mp hnd).2
  · split
    · simp [wireValues]
    · simp [wireValues]
  · exact run_controlledRotateRightOne_values_stepControl control register state hnd
  · intro wire hwire
    by_cases hcontrol : wire = control
    · subst wire
      exact controlledRotateRightOne_control_stepControl control register state hnd
    · exact
        (controlledRotateRightOne_usesOnly control register).preservesOutside
          state (by simp [hcontrol, hwire])

private theorem run_decrement_after_increment
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledDecrement control register carries)
        (run (controlledIncrement control register carries) state) = state := by
  let increased := run (controlledIncrement control register carries) state
  have hinc := controlledIncrement_correct control register carries state
    hlength hnd hclean
  have hcontrol := controlledIncrement_control control register carries state
    hlength hnd hclean
  have hcleanIncreased := controlledIncrement_clean control register carries state
    hlength hnd hclean
  have hdec := controlledDecrement_correct control register carries increased
    hlength hnd hcleanIncreased
  apply basisState_eq_of_word register _ state
  · rw [hdec.1]
    rw [show increased control = state control by exact hcontrol, hinc.1,
      decrementBits_incrementBits]
  · intro wire hwire
    rw [hdec.2 wire hwire]
    exact hinc.2 wire hwire

private theorem run_increment_after_decrement
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledIncrement control register carries)
        (run (controlledDecrement control register carries) state) = state := by
  let decreased := run (controlledDecrement control register carries) state
  have hdec := controlledDecrement_correct control register carries state
    hlength hnd hclean
  have hcontrol := controlledDecrement_control control register carries state
    hlength hnd hclean
  have hcleanDecreased := controlledDecrement_clean control register carries state
    hlength hnd hclean
  have hinc := controlledIncrement_correct control register carries decreased
    hlength hnd hcleanDecreased
  apply basisState_eq_of_word register _ state
  · rw [hinc.1]
    rw [show decreased control = state control by exact hcontrol, hdec.1,
      incrementBits_decrementBits]
  · intro wire hwire
    rw [hinc.2 wire hwire]
    exact hdec.2 wire hwire

private theorem terminalPadding_clean_after_rotate
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    Clean registers.scratch
      (run (controlledRotateLeftOne registers.terminal registers.work2) state) := by
  intro wire hwire
  rw [(controlledRotateLeftOne_usesOnly registers.terminal registers.work2).preservesOutside
    state]
  · exact hclean wire hwire
  · intro hmem
    rcases List.mem_cons.mp hmem with hterminal | hwork
    · subst wire
      exact terminalPadding_terminal_not_scratch registers hlayout hwire
    · exact terminalPadding_scratch_not_work2 registers hlayout
        wire hwire hwork

private theorem terminalPadding_clean_after_rotateRight
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    Clean registers.scratch
      (run (controlledRotateRightOne registers.terminal registers.work2) state) := by
  intro wire hwire
  rw [(controlledRotateRightOne_usesOnly registers.terminal registers.work2).preservesOutside
    state]
  · exact hclean wire hwire
  · intro hmem
    rcases List.mem_cons.mp hmem with hterminal | hwork
    · subst wire
      exact terminalPadding_terminal_not_scratch registers hlayout hwire
    · exact terminalPadding_scratch_not_work2 registers hlayout
        wire hwire hwork

private theorem run_controlledRotateLeftOne_after_right
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    run (controlledRotateLeftOne control register)
        (run (controlledRotateRightOne control register) state) = state := by
  rw [controlledRotateRightOne]
  exact run_run_adjoint_stepControl
    (controlledRotateLeftOne control register)
    (controlledRotateLeftOne_wellFormed control register hnd) state

private theorem terminalPaddingPrefix_clean
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    Clean registers.scratch (run (terminalPaddingPrefix registers) state) := by
  let rotated := run
    (controlledRotateLeftOne registers.terminal registers.work2) state
  have hscratchRotated : Clean registers.scratch rotated :=
    terminalPadding_clean_after_rotate registers state hlayout hclean
  have hcarryClean : Clean registers.carries rotated := by
    intro wire hwire
    apply hscratchRotated wire
    rcases List.mem_cons.mp hwire with rfl | htail
    · simp [TerminalPaddingRegisters.scratch]
    · simp [TerminalPaddingRegisters.scratch,
        TerminalPaddingRegisters.equalityScratch, htail]
  have hincNodup := terminalPadding_incrementNodup registers hlayout
  have hcleanCarries := controlledIncrement_clean registers.terminal
    registers.lengthS registers.carries rotated hlayout.carry_capacity
      hincNodup hcarryClean
  rw [terminalPaddingPrefix, run_append]
  intro wire hwire
  by_cases hcarry : wire ∈ registers.carries
  · exact hcleanCarries wire hcarry
  · rw [(controlledIncrement_usesOnly registers.terminal registers.lengthS
      registers.carries).preservesOutside rotated]
    · exact hscratchRotated wire hwire
    · intro hmem
      rcases List.mem_cons.mp hmem with hterminal | hrest
      · subst wire
        exact terminalPadding_terminal_not_scratch registers hlayout hwire
      · rcases List.mem_append.mp hrest with hlength | hcarryMem
        · exact terminalPadding_scratch_not_lengthS registers hlayout
            wire hwire hlength
        · exact hcarry hcarryMem

private theorem run_terminalPaddingForward_via_prefix
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    let afterPrefix := run (terminalPaddingPrefix registers) state
    run (terminalPaddingForward registers) state =
      afterPrefix[registers.shiftEpoch ↦
        Bool.xor (afterPrefix registers.shiftEpoch)
          (afterPrefix registers.terminal &&
            registerMatches registers.lengthS 0 afterPrefix)] := by
  let afterPrefix := run (terminalPaddingPrefix registers) state
  have hcleanPrefix : Clean registers.scratch afterPrefix :=
    terminalPaddingPrefix_clean registers state hlayout hclean
  rw [terminalPaddingForward, run_append]
  exact run_terminalPaddingEpochUpdate registers afterPrefix hlayout hcleanPrefix

/-- Direct circuit-free whole-state semantics of the literal forward wrapper. -/
theorem run_terminalPaddingForward
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    run (terminalPaddingForward registers) state =
      terminalPaddingForwardState registers state := by
  let rotatedBits :=
    if state registers.terminal then
      rotateLeftOne (wireValues registers.work2 state)
    else wireValues registers.work2 state
  let rotated :=
    writeReg registers.work2 (boolWordToNat rotatedBits) state
  have hrunRotated :
      run (controlledRotateLeftOne registers.terminal registers.work2) state =
        rotated := by
    simpa only [rotated, rotatedBits] using
      run_controlledRotateLeftOne_eq_writeReg registers.terminal
        registers.work2 state (terminalPadding_rotationNodup registers hlayout)
  have hscratchRotated : Clean registers.scratch rotated := by
    rw [← hrunRotated]
    exact terminalPadding_clean_after_rotate registers state hlayout hclean
  have hcarryClean : Clean registers.carries rotated := by
    intro wire hwire
    apply hscratchRotated wire
    rcases List.mem_cons.mp hwire with rfl | htail
    · simp [TerminalPaddingRegisters.scratch]
    · simp [TerminalPaddingRegisters.scratch,
        TerminalPaddingRegisters.equalityScratch, htail]
  let incrementedBits :=
    incrementBits (rotated registers.terminal)
      (wireValues registers.lengthS rotated)
  let incremented :=
    writeReg registers.lengthS (boolWordToNat incrementedBits) rotated
  have hrunIncremented :
      run (controlledIncrement registers.terminal registers.lengthS
        registers.carries) rotated = incremented := by
    simpa only [incremented, incrementedBits] using
      run_controlledIncrement_eq_writeReg registers.terminal registers.lengthS
        registers.carries rotated hlayout.carry_capacity
        (terminalPadding_incrementNodup registers hlayout) hcarryClean
  have hcleanIncremented : Clean registers.scratch incremented := by
    rw [← hrunIncremented, ← hrunRotated]
    simpa only [terminalPaddingPrefix, run_append] using
      terminalPaddingPrefix_clean registers state hlayout hclean
  have hepoch := run_terminalPaddingEpochUpdate registers incremented
    hlayout hcleanIncremented
  rw [terminalPaddingForward, terminalPaddingPrefix, run_append, run_append,
    hrunRotated, hrunIncremented, hepoch]
  rfl

/-- The complete minimal terminal scratch bank is returned to zero. -/
theorem terminalPaddingForward_clean
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    Clean registers.scratch (run (terminalPaddingForward registers) state) := by
  let afterPrefix := run (terminalPaddingPrefix registers) state
  have hcleanPrefix : Clean registers.scratch afterPrefix :=
    terminalPaddingPrefix_clean registers state hlayout hclean
  rw [run_terminalPaddingForward_via_prefix registers state hlayout hclean]
  intro wire hwire
  rw [upd_other]
  · exact hcleanPrefix wire hwire
  · intro equality
    subst wire
    exact terminalPadding_shiftEpoch_not_scratch registers hlayout hwire

private theorem terminalPaddingEpochUpdate_clean
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    Clean registers.scratch
      (run (terminalPaddingEpochUpdate registers) state) := by
  rw [run_terminalPaddingEpochUpdate registers state hlayout hclean]
  intro wire hwire
  rw [upd_other]
  · exact hclean wire hwire
  · intro equality
    subst wire
    exact terminalPadding_shiftEpoch_not_scratch registers hlayout hwire

/-- Direct circuit-free whole-state semantics of the literal inverse wrapper. -/
theorem run_terminalPaddingInverse
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    run (terminalPaddingInverse registers) state =
      terminalPaddingInverseState registers state := by
  let marked := state[registers.shiftEpoch ↦
    Bool.xor (state registers.shiftEpoch)
      (state registers.terminal &&
        registerMatches registers.lengthS 0 state)]
  have hrunMarked :
      run (terminalPaddingEpochUpdate registers) state = marked := by
    simpa only [marked] using
      run_terminalPaddingEpochUpdate registers state hlayout hclean
  have hcleanMarked : Clean registers.scratch marked := by
    rw [← hrunMarked]
    exact terminalPaddingEpochUpdate_clean registers state hlayout hclean
  have hcarryClean : Clean registers.carries marked := by
    intro wire hwire
    apply hcleanMarked wire
    rcases List.mem_cons.mp hwire with rfl | htail
    · simp [TerminalPaddingRegisters.scratch]
    · simp [TerminalPaddingRegisters.scratch,
        TerminalPaddingRegisters.equalityScratch, htail]
  let decrementedBits :=
    decrementBits (marked registers.terminal)
      (wireValues registers.lengthS marked)
  let decremented :=
    writeReg registers.lengthS (boolWordToNat decrementedBits) marked
  have hrunDecremented :
      run (controlledDecrement registers.terminal registers.lengthS
        registers.carries) marked = decremented := by
    simpa only [decremented, decrementedBits] using
      run_controlledDecrement_eq_writeReg registers.terminal registers.lengthS
        registers.carries marked hlayout.carry_capacity
        (terminalPadding_incrementNodup registers hlayout) hcarryClean
  let rotatedBits :=
    if decremented registers.terminal then
      (wireValues registers.work2 decremented).rotate
        (registers.work2.length - 1)
    else wireValues registers.work2 decremented
  let rotated :=
    writeReg registers.work2 (boolWordToNat rotatedBits) decremented
  have hrunRotated :
      run (controlledRotateRightOne registers.terminal registers.work2)
        decremented = rotated := by
    simpa only [rotated, rotatedBits] using
      run_controlledRotateRightOne_eq_writeReg registers.terminal
        registers.work2 decremented
        (terminalPadding_rotationNodup registers hlayout)
  rw [terminalPaddingInverse, run_append, run_append, hrunMarked,
    hrunDecremented, hrunRotated]
  rfl

/-- The literal inverse also returns the complete source scratch bank to zero. -/
theorem terminalPaddingInverse_clean
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    Clean registers.scratch (run (terminalPaddingInverse registers) state) := by
  let afterEpoch := run (terminalPaddingEpochUpdate registers) state
  let decreased := run
    (controlledDecrement registers.terminal registers.lengthS registers.carries)
    afterEpoch
  have hcleanEpoch : Clean registers.scratch afterEpoch :=
    terminalPaddingEpochUpdate_clean registers state hlayout hclean
  have hcarryClean : Clean registers.carries afterEpoch := by
    intro wire hwire
    apply hcleanEpoch wire
    rcases List.mem_cons.mp hwire with rfl | htail
    · simp [TerminalPaddingRegisters.scratch]
    · simp [TerminalPaddingRegisters.scratch,
        TerminalPaddingRegisters.equalityScratch, htail]
  have hdecNodup := terminalPadding_incrementNodup registers hlayout
  have hdecreasedCarries : Clean registers.carries decreased :=
    controlledDecrement_clean registers.terminal registers.lengthS
      registers.carries afterEpoch hlayout.carry_capacity hdecNodup hcarryClean
  have hdecreasedClean : Clean registers.scratch decreased := by
    intro wire hwire
    by_cases hcarry : wire ∈ registers.carries
    · exact hdecreasedCarries wire hcarry
    · change run (controlledDecrement registers.terminal registers.lengthS
          registers.carries) afterEpoch wire = false
      rw [(controlledDecrement_usesOnly registers.terminal registers.lengthS
        registers.carries).preservesOutside afterEpoch]
      · exact hcleanEpoch wire hwire
      · intro hmem
        rcases List.mem_cons.mp hmem with hterminal | hrest
        · subst wire
          exact terminalPadding_terminal_not_scratch registers hlayout hwire
        · rcases List.mem_append.mp hrest with hlength | hcarryMem
          · exact terminalPadding_scratch_not_lengthS registers hlayout
              wire hwire hlength
          · exact hcarry hcarryMem
  rw [terminalPaddingInverse, run_append, run_append]
  exact terminalPadding_clean_after_rotateRight registers decreased hlayout
    hdecreasedClean

/-- The forward terminal padding circuit and the literal source inverse cancel on every basis
state satisfying the clean-scratch boundary. -/
theorem run_terminalPaddingInverse_after_forward
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    run (terminalPaddingInverse registers)
        (run (terminalPaddingForward registers) state) = state := by
  have hrotation := terminalPadding_rotationNodup registers hlayout
  let rotated := run
    (controlledRotateLeftOne registers.terminal registers.work2) state
  have hscratchRotated : Clean registers.scratch rotated :=
    terminalPadding_clean_after_rotate registers state hlayout hclean
  have hcarryClean : Clean registers.carries rotated := by
    intro wire hwire
    have hscratch : wire ∈ registers.scratch := by
      rcases List.mem_cons.mp hwire with rfl | htail
      · simp [TerminalPaddingRegisters.scratch]
      · simp [TerminalPaddingRegisters.scratch,
          TerminalPaddingRegisters.equalityScratch, htail]
    exact hscratchRotated wire hscratch
  have hincNodup := terminalPadding_incrementNodup registers hlayout
  simp only [terminalPaddingInverse, terminalPaddingForward,
    terminalPaddingPrefix, run_append]
  rw [run_terminalPaddingEpochUpdate_twice registers
      (run (controlledIncrement registers.terminal registers.lengthS
        registers.carries) rotated) hlayout,
    run_decrement_after_increment registers.terminal registers.lengthS
      registers.carries rotated hlayout.carry_capacity hincNodup hcarryClean,
    run_controlledRotateRightOne_after_left registers.terminal registers.work2
      state hrotation]

/-- The literal forward wrapper also cancels a preceding inverse on every clean-scratch basis
state. -/
theorem run_terminalPaddingForward_after_inverse
    (registers : TerminalPaddingRegisters) (state : BasisState)
    (hlayout : TerminalPaddingLayout registers)
    (hclean : Clean registers.scratch state) :
    run (terminalPaddingForward registers)
        (run (terminalPaddingInverse registers) state) = state := by
  let afterEpoch := run (terminalPaddingEpochUpdate registers) state
  have hcleanEpoch : Clean registers.scratch afterEpoch :=
    terminalPaddingEpochUpdate_clean registers state hlayout hclean
  have hcarryClean : Clean registers.carries afterEpoch := by
    intro wire hwire
    apply hcleanEpoch wire
    rcases List.mem_cons.mp hwire with rfl | htail
    · simp [TerminalPaddingRegisters.scratch]
    · simp [TerminalPaddingRegisters.scratch,
        TerminalPaddingRegisters.equalityScratch, htail]
  have hrotation := terminalPadding_rotationNodup registers hlayout
  have hincNodup := terminalPadding_incrementNodup registers hlayout
  simp only [terminalPaddingInverse, terminalPaddingForward,
    terminalPaddingPrefix, run_append]
  rw [run_controlledRotateLeftOne_after_right registers.terminal registers.work2
      (run (controlledDecrement registers.terminal registers.lengthS
        registers.carries) afterEpoch) hrotation,
    run_increment_after_decrement registers.terminal registers.lengthS
      registers.carries afterEpoch hlayout.carry_capacity hincNodup hcarryClean,
    run_terminalPaddingEpochUpdate_twice registers state hlayout]

theorem terminalPaddingForward_usesOnly
    (registers : TerminalPaddingRegisters) :
    PaperCircuitUsesOnly registers.usedWires
      (terminalPaddingForward registers) := by
  have hrotate : PaperCircuitUsesOnly registers.usedWires
      (controlledRotateLeftOne registers.terminal registers.work2) :=
    (controlledRotateLeftOne_usesOnly registers.terminal registers.work2).mono (by
      intro wire hwire
      simp [TerminalPaddingRegisters.usedWires] at hwire ⊢
      aesop)
  have hinc : PaperCircuitUsesOnly registers.usedWires
      (controlledIncrement registers.terminal registers.lengthS registers.carries) :=
    (controlledIncrement_usesOnly registers.terminal registers.lengthS
      registers.carries).mono (by
        intro wire hwire
        simp [TerminalPaddingRegisters.usedWires,
          TerminalPaddingRegisters.scratch,
          TerminalPaddingRegisters.carries,
          TerminalPaddingRegisters.equalityScratch] at hwire ⊢
        aesop)
  have heq : PaperCircuitUsesOnly registers.usedWires
      (computeControl registers.lengthS 0 registers.wrapped
        registers.equalityScratch) :=
    (computeControl_usesOnly registers.lengthS 0 registers.wrapped
      registers.equalityScratch).mono (by
        intro wire hwire
        simp [TerminalPaddingRegisters.usedWires,
          TerminalPaddingRegisters.scratch,
          TerminalPaddingRegisters.equalityScratch] at hwire ⊢
        aesop)
  have hmark : PaperCircuitUsesOnly registers.usedWires
      ([.CCX registers.terminal registers.wrapped
        registers.shiftEpoch] : Circuit) := by
    simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
      TerminalPaddingRegisters.usedWires,
      TerminalPaddingRegisters.scratch]
  simpa [terminalPaddingForward, terminalPaddingPrefix,
    terminalPaddingEpochUpdate, List.append_assoc] using
      (hrotate.append hinc).append ((heq.append hmark).append heq)

theorem terminalPaddingInverse_usesOnly
    (registers : TerminalPaddingRegisters) :
    PaperCircuitUsesOnly registers.usedWires
      (terminalPaddingInverse registers) := by
  have heq : PaperCircuitUsesOnly registers.usedWires
      (computeControl registers.lengthS 0 registers.wrapped
        registers.equalityScratch) :=
    (computeControl_usesOnly registers.lengthS 0 registers.wrapped
      registers.equalityScratch).mono (by
        intro wire hwire
        simp [TerminalPaddingRegisters.usedWires,
          TerminalPaddingRegisters.scratch,
          TerminalPaddingRegisters.equalityScratch] at hwire ⊢
        aesop)
  have hmark : PaperCircuitUsesOnly registers.usedWires
      ([.CCX registers.terminal registers.wrapped
        registers.shiftEpoch] : Circuit) := by
    simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
      TerminalPaddingRegisters.usedWires,
      TerminalPaddingRegisters.scratch]
  have hdec : PaperCircuitUsesOnly registers.usedWires
      (controlledDecrement registers.terminal registers.lengthS registers.carries) :=
    (controlledDecrement_usesOnly registers.terminal registers.lengthS
      registers.carries).mono (by
        intro wire hwire
        simp [TerminalPaddingRegisters.usedWires,
          TerminalPaddingRegisters.scratch,
          TerminalPaddingRegisters.carries,
          TerminalPaddingRegisters.equalityScratch] at hwire ⊢
        aesop)
  have hrotate : PaperCircuitUsesOnly registers.usedWires
      (controlledRotateRightOne registers.terminal registers.work2) :=
    (controlledRotateRightOne_usesOnly registers.terminal registers.work2).mono (by
      intro wire hwire
      simp [TerminalPaddingRegisters.usedWires] at hwire ⊢
      aesop)
  simpa [terminalPaddingInverse, terminalPaddingEpochUpdate,
    List.append_assoc] using
      ((heq.append hmark).append heq).append (hdec.append hrotate)

@[simp]
theorem terminalPaddingForward_HPFree
    (registers : TerminalPaddingRegisters) :
    HPFree (terminalPaddingForward registers) := by
  simp [terminalPaddingForward, terminalPaddingPrefix,
    terminalPaddingEpochUpdate]

@[simp]
theorem terminalPaddingInverse_HPFree
    (registers : TerminalPaddingRegisters) :
    HPFree (terminalPaddingInverse registers) := by
  simp [terminalPaddingInverse, terminalPaddingEpochUpdate]

theorem terminalPaddingForward_wellFormed
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    CircuitWellFormed (terminalPaddingForward registers) := by
  rw [terminalPaddingForward, terminalPaddingPrefix,
    circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨controlledRotateLeftOne_wellFormed registers.terminal registers.work2
      (terminalPadding_rotationNodup registers hlayout),
    controlledIncrement_wellFormed registers.terminal registers.lengthS
      registers.carries (terminalPadding_incrementNodup registers hlayout)⟩,
    terminalPaddingEpochUpdate_wellFormed registers hlayout⟩

theorem terminalPaddingInverse_wellFormed
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    CircuitWellFormed (terminalPaddingInverse registers) := by
  rw [terminalPaddingInverse, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨terminalPaddingEpochUpdate_wellFormed registers hlayout,
    controlledDecrement_wellFormed registers.terminal registers.lengthS
      registers.carries (terminalPadding_incrementNodup registers hlayout)⟩,
    controlledRotateRightOne_wellFormed registers.terminal registers.work2
      (terminalPadding_rotationNodup registers hlayout)⟩

private theorem controlledIncrement_stepControl_cnotCount_of_two_le
    (control : Wire) (register carries : List Wire)
    (hlength : register.length = carries.length + 1)
    (hwidth : 2 ≤ register.length) :
    eeaCnotCount (controlledIncrement control register carries) =
      register.length + 2 := by
  cases register with
  | nil => simp at hwidth
  | cons low tail =>
      cases tail with
      | nil => simp at hwidth
      | cons next rest =>
          exact controlledIncrement_cnotCount control low next rest carries hlength

private theorem controlledDecrement_stepControl_cnotCount_of_two_le
    (control : Wire) (register borrows : List Wire)
    (hlength : register.length = borrows.length + 1)
    (hwidth : 2 ≤ register.length) :
    eeaCnotCount (controlledDecrement control register borrows) =
      register.length + 2 := by
  cases register with
  | nil => simp at hwidth
  | cons low tail =>
      cases tail with
      | nil => simp at hwidth
      | cons next rest =>
          exact controlledDecrement_cnotCount control low next rest borrows hlength

private theorem mcxVChainTail_stepControl_xCount
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire) :
    eeaXCount (mcxVChainTail accumulator controls target scratches) = 0 := by
  induction controls generalizing accumulator scratches with
  | nil => rfl
  | cons control controls ih =>
      cases controls with
      | nil => rfl
      | cons nextControl controls =>
          cases scratches with
          | nil => rfl
          | cons scratch scratches =>
              rw [mcxVChainTail, eeaXCount_append, eeaXCount_append,
                ih scratch scratches]
              rfl

private theorem mcxVChain_stepControl_xCount_of_two_le
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (hwidth : 2 ≤ controls.length) :
    eeaXCount (mcxVChain controls target scratches) = 0 := by
  cases controls with
  | nil => simp at hwidth
  | cons first controls =>
      cases controls with
      | nil => simp at hwidth
      | cons second controls =>
          exact mcxVChainTail_stepControl_xCount second
            (first :: controls) target scratches

private theorem zeroMaskFrom_zero_stepControl_xCount
    (register : List Wire) (bit : Nat) :
    eeaXCount (zeroMaskFrom register 0 bit) = register.length := by
  induction register generalizing bit with
  | nil => rfl
  | cons wire register ih =>
      rw [zeroMaskFrom, if_neg (by simp), eeaXCount_append,
        ih (bit + 1)]
      simp [eeaXCount]
      omega

private theorem zeroMask_zero_stepControl_xCount
    (register : List Wire) :
    eeaXCount (zeroMask register 0) = register.length := by
  exact zeroMaskFrom_zero_stepControl_xCount register 0

@[simp]
theorem terminalPaddingForward_toffoliCount
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    eeaToffoliCount (terminalPaddingForward registers) =
      (registers.work2.length - 1) +
        2 * (registers.lengthS.length - 1) +
        (2 * mcxVChainToffoliCost registers.lengthS.length + 1) := by
  have heq := terminalPadding_eqLayout registers hlayout
  rw [terminalPaddingForward, terminalPaddingPrefix,
    terminalPaddingEpochUpdate, eeaToffoliCount_append,
    eeaToffoliCount_append, eeaToffoliCount_append,
    eeaToffoliCount_append,
    controlledRotateLeftOne_toffoliCount,
    controlledIncrement_toffoliCount _ _ _ hlayout.carry_capacity,
    computeControl_toffoliCount _ _ _ _ heq.1]
  simp [eeaToffoliCount]
  omega

@[simp]
theorem terminalPaddingForward_cnotCount
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    eeaCnotCount (terminalPaddingForward registers) =
      2 * (registers.work2.length - 1) +
        (registers.lengthS.length + 2) +
        2 * mcxVChainCnotCost registers.lengthS.length := by
  have heq := terminalPadding_eqLayout registers hlayout
  have hwidth : 2 ≤ registers.lengthS.length := by
    rw [hlayout.carry_capacity]
    simp [TerminalPaddingRegisters.carries]
  rw [terminalPaddingForward, terminalPaddingPrefix,
    terminalPaddingEpochUpdate, eeaCnotCount_append,
    eeaCnotCount_append, eeaCnotCount_append,
    eeaCnotCount_append,
    controlledRotateLeftOne_cnotCount,
    controlledIncrement_stepControl_cnotCount_of_two_le _ _ _
      hlayout.carry_capacity hwidth,
    computeControl_cnotCount]
  simp [eeaCnotCount]
  omega

@[simp]
theorem terminalPaddingForward_xCount
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    eeaXCount (terminalPaddingForward registers) =
      4 * registers.lengthS.length := by
  have hwidth : 2 ≤ registers.lengthS.length := by
    rw [hlayout.carry_capacity]
    simp [TerminalPaddingRegisters.carries]
  rw [terminalPaddingForward, terminalPaddingPrefix,
    terminalPaddingEpochUpdate, eeaXCount_append,
    eeaXCount_append, eeaXCount_append, eeaXCount_append,
    controlledRotateLeftOne_xCount, controlledIncrement_xCount,
    computeControl_xCount,
    zeroMask_zero_stepControl_xCount,
    mcxVChain_stepControl_xCount_of_two_le _ _ _ hwidth]
  simp [eeaXCount]
  omega

@[simp]
theorem terminalPaddingForward_tCount
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    ShorECDLP.tCount (terminalPaddingForward registers) =
      7 * ((registers.work2.length - 1) +
        2 * (registers.lengthS.length - 1) +
        (2 * mcxVChainToffoliCost registers.lengthS.length + 1)) := by
  have heq := terminalPadding_eqLayout registers hlayout
  rw [terminalPaddingForward, terminalPaddingPrefix,
    terminalPaddingEpochUpdate, tCount_append, tCount_append,
    tCount_append, tCount_append,
    controlledRotateLeftOne_tCount,
    controlledIncrement_tCount _ _ _ hlayout.carry_capacity,
    computeControl_tCount _ _ _ _ heq.1]
  simp [tCost]
  omega

@[simp]
theorem terminalPaddingInverse_toffoliCount
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    eeaToffoliCount (terminalPaddingInverse registers) =
      (registers.work2.length - 1) +
        2 * (registers.lengthS.length - 1) +
        (2 * mcxVChainToffoliCost registers.lengthS.length + 1) := by
  have heq := terminalPadding_eqLayout registers hlayout
  rw [terminalPaddingInverse, terminalPaddingEpochUpdate,
    eeaToffoliCount_append, eeaToffoliCount_append,
    eeaToffoliCount_append, eeaToffoliCount_append,
    controlledRotateRightOne_toffoliCount,
    controlledDecrement_toffoliCount _ _ _ hlayout.carry_capacity,
    computeControl_toffoliCount _ _ _ _ heq.1]
  simp [eeaToffoliCount]
  omega

@[simp]
theorem terminalPaddingInverse_cnotCount
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    eeaCnotCount (terminalPaddingInverse registers) =
      2 * (registers.work2.length - 1) +
        (registers.lengthS.length + 2) +
        2 * mcxVChainCnotCost registers.lengthS.length := by
  have heq := terminalPadding_eqLayout registers hlayout
  have hwidth : 2 ≤ registers.lengthS.length := by
    rw [hlayout.carry_capacity]
    simp [TerminalPaddingRegisters.carries]
  rw [terminalPaddingInverse, terminalPaddingEpochUpdate,
    eeaCnotCount_append, eeaCnotCount_append,
    eeaCnotCount_append, eeaCnotCount_append,
    controlledRotateRightOne_cnotCount,
    controlledDecrement_stepControl_cnotCount_of_two_le _ _ _
      hlayout.carry_capacity hwidth,
    computeControl_cnotCount]
  simp [eeaCnotCount]
  omega

@[simp]
theorem terminalPaddingInverse_xCount
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    eeaXCount (terminalPaddingInverse registers) =
      4 * registers.lengthS.length +
        4 * (registers.lengthS.length - 1) := by
  have hwidth : 2 ≤ registers.lengthS.length := by
    rw [hlayout.carry_capacity]
    simp [TerminalPaddingRegisters.carries]
  rw [terminalPaddingInverse, terminalPaddingEpochUpdate,
    eeaXCount_append, eeaXCount_append, eeaXCount_append,
    eeaXCount_append, controlledRotateRightOne_xCount,
    controlledDecrement_xCount _ _ _ hlayout.carry_capacity,
    computeControl_xCount,
    zeroMask_zero_stepControl_xCount,
    mcxVChain_stepControl_xCount_of_two_le _ _ _ hwidth]
  simp [eeaXCount]
  omega

@[simp]
theorem terminalPaddingInverse_tCount
    (registers : TerminalPaddingRegisters)
    (hlayout : TerminalPaddingLayout registers) :
    ShorECDLP.tCount (terminalPaddingInverse registers) =
      7 * ((registers.work2.length - 1) +
        2 * (registers.lengthS.length - 1) +
        (2 * mcxVChainToffoliCost registers.lengthS.length + 1)) := by
  have heq := terminalPadding_eqLayout registers hlayout
  rw [terminalPaddingInverse, terminalPaddingEpochUpdate,
    tCount_append, tCount_append, tCount_append, tCount_append,
    controlledRotateRightOne_tCount,
    controlledDecrement_tCount _ _ _ hlayout.carry_capacity,
    computeControl_tCount _ _ _ _ heq.1]
  simp [tCost]
  omega

/-! ## Closed source and production witnesses -/

private def terminalPaddingWidthTwoRegisters
    (terminal shiftEpoch w₀ w₁ w₂ l₀ l₁ wrapped extra : Wire) :
    TerminalPaddingRegisters where
  terminal := terminal
  shiftEpoch := shiftEpoch
  work2 := [w₀, w₁, w₂]
  lengthS := [l₀, l₁]
  wrapped := wrapped
  carryTail := []
  equalityExtra := extra

/-- Flattened width-two streams emitted by the pinned terminal-padding helpers.  The forward
stream rotates left before incrementing and checking wrap; the inverse checks wrap first and
finishes with the reversed adjacent-Fredkin cascade. -/
theorem terminalPadding_widthTwo_source_regression
    (terminal shiftEpoch w₀ w₁ w₂ l₀ l₁ wrapped extra : Wire) :
    let registers := terminalPaddingWidthTwoRegisters terminal shiftEpoch
      w₀ w₁ w₂ l₀ l₁ wrapped extra
    terminalPaddingForward registers =
        [.CX w₁ w₀, .CCX terminal w₀ w₁, .CX w₁ w₀,
          .CX w₂ w₁, .CCX terminal w₁ w₂, .CX w₂ w₁,
          .CCX terminal l₀ wrapped, .CX terminal l₀, .CX wrapped l₁,
          .CX terminal l₀, .CCX terminal l₀ wrapped, .CX terminal l₀,
          .X l₀, .X l₁, .CCX l₀ l₁ wrapped, .X l₁, .X l₀,
          .CCX terminal wrapped shiftEpoch,
          .X l₀, .X l₁, .CCX l₀ l₁ wrapped, .X l₁, .X l₀] ∧
      terminalPaddingInverse registers =
        [.X l₀, .X l₁, .CCX l₀ l₁ wrapped, .X l₁, .X l₀,
          .CCX terminal wrapped shiftEpoch,
          .X l₀, .X l₁, .CCX l₀ l₁ wrapped, .X l₁, .X l₀,
          .X l₀, .CCX terminal l₀ wrapped, .X l₀, .CX terminal l₀,
          .CX wrapped l₁, .CX terminal l₀, .X l₀,
          .CCX terminal l₀ wrapped, .X l₀, .CX terminal l₀,
          .CX w₂ w₁, .CCX terminal w₁ w₂, .CX w₂ w₁,
          .CX w₁ w₀, .CCX terminal w₀ w₁, .CX w₁ w₀] := by
  constructor <;> rfl

private def terminalPaddingSecp256k1Registers : TerminalPaddingRegisters where
  terminal := 0
  shiftEpoch := 1
  work2 := List.range' 2 259
  lengthS := List.range' 261 9
  wrapped := 270
  carryTail := List.range' 271 7
  equalityExtra := 278

set_option maxRecDepth 100000 in
private theorem terminalPaddingSecp256k1Layout :
    TerminalPaddingLayout terminalPaddingSecp256k1Registers := by
  refine ⟨by simp [terminalPaddingSecp256k1Registers,
    TerminalPaddingRegisters.carries], ?_⟩
  decide

/-- Closed production witness for the borrowed-epoch terminal padding.  The source allocates 279
roles (including one surplus equality-pool wire).  At `n = 256`, `T_max = 1620`, the 9-bit low
word plus its borrowed epoch fits the entire padding horizon. -/
theorem terminalPadding_secp256k1_resources :
    TerminalPaddingScheduleFits terminalPaddingSecp256k1Registers 256 1620 ∧
      terminalPaddingSecp256k1Registers.scratch.length = 9 ∧
      terminalPaddingSecp256k1Registers.usedWires.length = 279 ∧
      eeaToffoliCount
          (terminalPaddingForward terminalPaddingSecp256k1Registers) = 305 ∧
      eeaCnotCount
          (terminalPaddingForward terminalPaddingSecp256k1Registers) = 527 ∧
      eeaXCount
          (terminalPaddingForward terminalPaddingSecp256k1Registers) = 36 ∧
      ShorECDLP.tCount
          (terminalPaddingForward terminalPaddingSecp256k1Registers) = 2135 ∧
      eeaToffoliCount
          (terminalPaddingInverse terminalPaddingSecp256k1Registers) = 305 ∧
      eeaCnotCount
          (terminalPaddingInverse terminalPaddingSecp256k1Registers) = 527 ∧
      eeaXCount
          (terminalPaddingInverse terminalPaddingSecp256k1Registers) = 68 ∧
      ShorECDLP.tCount
          (terminalPaddingInverse terminalPaddingSecp256k1Registers) = 2135 := by
  have hlayout := terminalPaddingSecp256k1Layout
  constructor
  · norm_num [TerminalPaddingScheduleFits,
      terminalPaddingSecp256k1Registers]
  constructor
  · norm_num [TerminalPaddingRegisters.scratch,
      TerminalPaddingRegisters.equalityScratch,
      terminalPaddingSecp256k1Registers]
  constructor
  · norm_num [TerminalPaddingRegisters.usedWires,
      TerminalPaddingRegisters.scratch,
      TerminalPaddingRegisters.equalityScratch,
      terminalPaddingSecp256k1Registers]
  constructor
  · simpa [terminalPaddingSecp256k1Registers,
      mcxVChainToffoliCost] using
      terminalPaddingForward_toffoliCount
        terminalPaddingSecp256k1Registers hlayout
  constructor
  · simpa [terminalPaddingSecp256k1Registers,
      mcxVChainCnotCost] using
      terminalPaddingForward_cnotCount
        terminalPaddingSecp256k1Registers hlayout
  constructor
  · simpa [terminalPaddingSecp256k1Registers] using
      terminalPaddingForward_xCount
        terminalPaddingSecp256k1Registers hlayout
  constructor
  · simpa [terminalPaddingSecp256k1Registers,
      mcxVChainToffoliCost] using
      terminalPaddingForward_tCount
        terminalPaddingSecp256k1Registers hlayout
  constructor
  · simpa [terminalPaddingSecp256k1Registers,
      mcxVChainToffoliCost] using
      terminalPaddingInverse_toffoliCount
        terminalPaddingSecp256k1Registers hlayout
  constructor
  · simpa [terminalPaddingSecp256k1Registers,
      mcxVChainCnotCost] using
      terminalPaddingInverse_cnotCount
        terminalPaddingSecp256k1Registers hlayout
  constructor
  · simpa [terminalPaddingSecp256k1Registers] using
      terminalPaddingInverse_xCount
        terminalPaddingSecp256k1Registers hlayout
  · simpa [terminalPaddingSecp256k1Registers,
      mcxVChainToffoliCost] using
      terminalPaddingInverse_tCount
        terminalPaddingSecp256k1Registers hlayout

end ShorECDLP.Paper2607_13816
