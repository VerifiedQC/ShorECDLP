import ShorECDLP.Submission.«2607_13816».Window.RawCoordinate
import ShorECDLP.Submission.«2607_13816».Window.Preparation
/-! Prepared raw window calls and execution-order conditions.
The domain records actual successive complete states. It does not establish that
scalar initialization satisfies those conditions, or bound exceptional weight.
The repaired algorithm and its success/resource certificates remain separate. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

/-- Raw core placed on the actual bank used for window j. -/
def parkedRawProgram (x y : Nat → Nat → Nat) (j : Nat) : AdaptiveCircuit :=
  (signedRawProgram (x j) (y j)).relabel
    (windowAddressPerm (windowBankStart j) (by unfold windowBankStart; omega))
def parkedRawState (x y : Nat → Nat → Nat) (j : Nat) (s : BasisState) : BasisState :=
  let e := windowAddressPerm (windowBankStart j) (by unfold windowBankStart; omega)
  relabelBasis e (signedLookupCoordinateState (x j) (y j) (relabelBasis e.symm s))
def ParkedRawDomain (x y : Nat → Nat → Nat) (j : Nat) (s : BasisState) : Prop :=
  SignedRawDomain (x j) (y j)
    (relabelBasis (windowAddressPerm (windowBankStart j) (by unfold windowBankStart; omega)).symm s)

theorem parkedRawProgram_coherent (x y : Nat → Nat → Nat) (j : Nat) :
    CoherentlyImplementsOn (parkedRawProgram x y j)
      (Finsupp.lmapDomain ℂ ℂ (parkedRawState x y j)) (ParkedRawDomain x y j) := by
  have h := (signedRawProgram_coherent (x j) (y j)).relabel
    (windowAddressPerm (windowBankStart j) (by unfold windowBankStart; omega))
  apply h.congrIdeal
  intro s hs
  simp [parkedRawState,LinearMap.comp_apply,relabelState,ket]

/-- The same physical address preparation before and after the raw core. -/
def preparedRawProgram (x y : Nat → Nat → Nat) (j : Nat) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary (windowPrepareCircuit j) .done).seq
    (parkedRawProgram x y j)).seq (.unitary (windowPrepareCircuit j) .done)
def preparedRawState (x y : Nat → Nat → Nat) (j : Nat) (s : BasisState) : BasisState :=
  windowPrepareState j (parkedRawState x y j (windowPrepareState j s))
/-- Readiness and both nonzero inputs are checked after actual address preparation. -/
def PreparedRawDomain (x y : Nat → Nat → Nat) (j : Nat) (s : BasisState) : Prop :=
  ParkedRawDomain x y j (windowPrepareState j s)

private theorem strengthen {p : AdaptiveCircuit} {f : State →ₗ[ℂ] State}
    {V W : BasisState → Prop} (h : CoherentlyImplementsOn p f V)
    (hs : ∀ s, W s → V s) : CoherentlyImplementsOn p f W := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hv => hb s (hs s hv)),hm⟩
private theorem prepare_coherent (j : Nat) (V : BasisState → Prop) :
    CoherentlyImplementsOn (.unitary (windowPrepareCircuit j) .done)
      (Finsupp.lmapDomain ℂ ℂ (windowPrepareState j)) V := by
  apply (CoherentlyImplementsOn.unitary (windowPrepareCircuit j) V).congrIdeal
  intro s _
  simpa [ket] using windowPrepareCircuit_ket j s

theorem preparedRawProgram_coherent (x y : Nat → Nat → Nat) (j : Nat) :
    CoherentlyImplementsOn (preparedRawProgram x y j)
      (Finsupp.lmapDomain ℂ ℂ (preparedRawState x y j)) (PreparedRawDomain x y j) := by
  have h := (prepare_coherent j (PreparedRawDomain x y j)).seq (parkedRawProgram_coherent x y j) (by
    intro s hs
    simpa [ket] using supportedOn_ket (ParkedRawDomain x y j) (windowPrepareState j s) hs)
  have hh := h.seq (prepare_coherent j (fun _ => True)) (by
    intro s hs
    simp only [LinearMap.comp_apply]
    simpa [ket] using supportedOn_ket (fun _ => True) (parkedRawState x y j (windowPrepareState j s)) trivial)
  apply hh.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket,preparedRawState]

/-- The list is execution order, with repetitions allowed. -/
def rawWindowSchedule (x y : Nat → Nat → Nat) : List Nat → AdaptiveCircuit
  | [] => .done
  | j::js => (preparedRawProgram x y j).seq (rawWindowSchedule x y js)
def rawWindowScheduleState (x y : Nat → Nat → Nat) : List Nat → BasisState → BasisState
  | [], s => s
  | j::js, s => rawWindowScheduleState x y js (preparedRawState x y j s)
/-- Each condition is evaluated after all preceding calls. Output cleanup alone
is not sufficient: the next call's nonzero preconditions remain explicit. -/
def RawWindowScheduleDomain (x y : Nat → Nat → Nat) : List Nat → BasisState → Prop
  | [], _ => True
  | j::js, s => PreparedRawDomain x y j s ∧
      RawWindowScheduleDomain x y js (preparedRawState x y j s)

theorem rawWindowSchedule_coherent (x y : Nat → Nat → Nat) (js : List Nat) :
    CoherentlyImplementsOn (rawWindowSchedule x y js)
      (Finsupp.lmapDomain ℂ ℂ (rawWindowScheduleState x y js)) (RawWindowScheduleDomain x y js) := by
  induction js with
  | nil =>
    refine ⟨[1],?_,by simp⟩
    simp only [rawWindowSchedule,AdaptiveCircuit.run]
    apply List.Forall₂.cons
    · intro s hs; simp [rawWindowScheduleState,ket]
    · exact .nil
  | cons j js ih =>
    have h := strengthen (preparedRawProgram_coherent x y j)
      (fun s (hs : RawWindowScheduleDomain x y (j::js) s) => hs.1)
    have hh := h.seq ih (by
      intro s hs
      simpa [ket] using supportedOn_ket _ _ hs.2)
    apply hh.congrIdeal
    intro s hs
    simp [rawWindowScheduleState,LinearMap.comp_apply,ket]

/-- Bank relocation does not change which physical coordinate wires can change. -/
theorem parkedRawState_frame (x y : Nat → Nat → Nat) (j : Nat) (s : BasisState)
    (hs : ParkedRawDomain x y j s) (w : Wire)
    (hx : w ∉ List.range' 263 256) (hy : w ∉ List.range' 580 256) :
    parkedRawState x y j s w = s w := by
  let e := windowAddressPerm (windowBankStart j) (by unfold windowBankStart; omega)
  have hpre (a n : Nat) (hb : a+n ≤ 839) (hw : w ∉ List.range' a n) :
      e.symm w ∉ List.range' a n := by
    intro hm
    have hlt : e.symm w < 839 := by
      simp only [List.mem_range'_1] at hm
      dsimp only [Wire] at *
      omega
    have he : w = e.symm w := by
      have hh : e (e.symm w) = e.symm w :=
        windowAddressPerm_core (windowBankStart j) (by unfold windowBankStart; omega) (e.symm w) hlt
      simpa only [Equiv.apply_symm_apply] using hh
    exact hw (he.symm ▸ hm)
  change signedLookupCoordinateState (x j) (y j) (relabelBasis e.symm s) (e.symm w) = s w
  rw [(signedRawProgram_output (x j) (y j) (relabelBasis e.symm s) hs).2
    (e.symm w) (hpre 263 256 (by decide) hx) (hpre 580 256 (by decide) hy)]
  simp [relabelBasis]

private theorem prepare_frame_congr (j : Nat) (s t : BasisState)
    (hf : ∀ w, w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → t w = s w)
    (w : Wire) (hx : w ∉ List.range' 263 256) (hy : w ∉ List.range' 580 256) :
    windowPrepareState j t w = windowPrepareState j s w := by
  have hq := hf 836 (by decide) (by decide)
  have hz := hf (windowBankStart j+15)
    (by simp only [List.mem_range'_1,windowBankStart]; omega)
    (by simp only [List.mem_range'_1,windowBankStart]; omega)
  simp only [windowPrepareState,signedAddressState,tableXorState,hq,hz,hf w hx hy]

/-- The second address preparation restores every non-coordinate wire, including
all parked input banks, address/sign bits and query work. -/
theorem preparedRawState_frame (x y : Nat → Nat → Nat) (j : Nat) (s : BasisState)
    (hs : PreparedRawDomain x y j s) (w : Wire)
    (hx : w ∉ List.range' 263 256) (hy : w ∉ List.range' 580 256) :
    preparedRawState x y j s w = s w := by
  change windowPrepareState j (parkedRawState x y j (windowPrepareState j s)) w = s w
  rw [prepare_frame_congr j _ _ (parkedRawState_frame x y j _ hs) w hx hy,
    windowPrepareState_involution]

/-- Complete non-coordinate frame for the stated execution order. -/
theorem rawWindowScheduleState_frame (x y : Nat → Nat → Nat) (js : List Nat) (s : BasisState)
    (hs : RawWindowScheduleDomain x y js s) (w : Wire)
    (hx : w ∉ List.range' 263 256) (hy : w ∉ List.range' 580 256) :
    rawWindowScheduleState x y js s w = s w := by
  induction js generalizing s with
  | nil => rfl
  | cons j js ih =>
    exact (ih _ hs.2).trans (preparedRawState_frame x y j s hs.1 w hx hy)
end
end ShorECDLP.Paper2607_13816
