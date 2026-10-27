import ShorECDLP.Submission.«2607_13816».Challenge.Outer

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The suffix bound must cover the actual history inherited from the prefix. -/
theorem outer_append_t_le {n s m e : Nat} (p : Straight n s m) (q : Straight n m e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (bound : Nat)
    (hq : ∀ h, (q.instantiate read h).tCount ≤ bound) :
    ((p.append q).instantiate read history).tCount ≤ (p.instantiate read history).tCount + bound := by
  induction p with
  | done => simpa [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount] using hq history
  | gate g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount]
    have h := ih q history hq; omega
  | recordGate i v g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount]
    have h := ih q history hq; omega
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount]
    have hf := ih q (Fin.lastCases false history) hq
    have ht := ih q (Fin.lastCases true history) hq
    omega

theorem prepareOuterBank_slots {n s e : Nat} (ws : List Wire) (p : Straight n s e) :
    (prepareOuterBank ws p).gateSlots = ws.length + p.gateSlots := by
  induction ws <;> simp_all [prepareOuterBank, Straight.gateSlots, Nat.add_assoc, Nat.add_left_comm]

theorem prepareOuterBank_t {n s e : Nat} (ws : List Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((prepareOuterBank ws p).instantiate read history).tCount = (p.instantiate read history).tCount := by
  induction ws <;> simp_all [prepareOuterBank, Straight.instantiate, TemplateGate.instantiate,
    AdaptiveCircuit.tCount, ShorECDLP.tCount, tCost]

theorem feedbackProgram_t_le {n s e : Nat} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((feedbackProgram dir w indices k p).instantiate read history).tCount ≤
      indices.length + (p.instantiate read history).tCount := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih =>
    simp only [feedbackProgram, Straight.instantiate, AdaptiveCircuit.tCount, List.length_cons]
    have h := ih (k+1)
    have hcost : ShorECDLP.tCount (if history i = true then [.P dir k w] else []) ≤ 1 := by
      split <;> simp [ShorECDLP.tCount, tCost]
    omega

theorem fourierProgram_t_le (n : Nat) (dir : PhaseDir) (ws : List Wire) (start : Nat)
    (prior : List (Fin start)) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((fourierProgram n dir ws start prior).instantiate read history).tCount ≤ fourierSlots ws.length prior.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [fourierProgram, castFinish_instantiate]
    apply (feedbackProgram_t_le _ _ _ _ _ _ _).trans
    have hf := ih (start+1) (Fin.last start :: prior.map Fin.castSucc) (Fin.lastCases false history)
    have ht := ih (start+1) (Fin.last start :: prior.map Fin.castSucc) (Fin.lastCases true history)
    simp only [Straight.instantiate, AdaptiveCircuit.tCount, List.length_cons, List.length_map] at *
    simp only [fourierSlots]
    omega

theorem resetProgram_t (n start : Nat) (ws : List Wire) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) : ((resetProgram n start ws).instantiate read history).tCount = 0 := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp [resetProgram, castFinish_instantiate, Straight.instantiate, AdaptiveCircuit.tCount, ih]

/-- Feedback slots for complete 16-bit banks, starting with `prior` earlier bits. -/
def axisFeedback : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, prior => fourierSlots 16 prior + axisFeedback k (prior+16)

theorem nextBankPrior_length {start : Nat} (count : Nat) (prior : List (Fin start)) :
    (nextBankPrior count prior).length = prior.length+16 := by
  simp only [nextBankPrior, List.length_append, List.length_reverse, List.length_ofFn, List.length_map]
  omega

theorem bankPrior_length {start : Nat} (count : Nat) (prior : List (Fin start)) :
    (bankPrior count prior).length = prior.length := by simp [bankPrior]

theorem outerAxis_slots_le {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n)) (slots : Nat)
    (hw : ∀ w ∈ ws, ∀ s, (w.program s).gateSlots ≤ slots) (start : Nat) (prior : List (Fin start)) :
    (outerAxis wires ws start prior).gateSlots ≤ ws.length*(slots+16) + axisFeedback ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [outerAxis, axisFeedback, Straight.gateSlots]
  | cons w ws ih =>
    simp only [outerAxis, castFinish_gateSlots, Straight.gateSlots_append,
      prepareOuterBank_slots, List.length_reverse, Vector.length_toList,
      fourierProgram_slots, bankPrior_length]
    have h := ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) (start+w.count+16) (nextBankPrior w.count prior)
    have hg := hw w (by simp) start
    simp only [nextBankPrior_length] at h
    simp only [List.length_cons, axisFeedback, Nat.add_mul, Nat.one_mul]
    omega

theorem outerAxis_t_le {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n)) (cost : Nat)
    (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ ws, ∀ s h, ((w.program s).instantiate read h).tCount ≤ cost)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((outerAxis wires ws start prior).instantiate read history).tCount ≤
      ws.length*cost + axisFeedback ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [outerAxis, axisFeedback, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons w ws ih =>
    simp only [outerAxis, castFinish_instantiate]
    apply (outer_append_t_le _ _ read history
      (fourierSlots 16 prior.length + (ws.length*cost+axisFeedback ws.length (prior.length+16))) ?_).trans
    · simp only [prepareOuterBank_t, List.length_cons, Nat.add_mul, Nat.one_mul, axisFeedback]
      have h := hw w (by simp) start history
      omega
    · intro h
      apply (outer_append_t_le _ _ read h
        (ws.length*cost+axisFeedback ws.length (prior.length+16)) ?_).trans
      · have hf := fourierProgram_t_le n .inverse wires.toList (start+w.count) (bankPrior w.count prior) read h
        simp only [Vector.length_toList, bankPrior_length] at hf
        simp only [castFinish_instantiate]
        omega
      · intro h₂
        simpa only [nextBankPrior_length] using
          ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _ (nextBankPrior w.count prior) h₂

theorem outer_feedback_overhead : axisFeedback 16 0 + axisFeedback 13 0 = 54168 := by decide +kernel

theorem OuterPlan.round_slots_le {n : Nat} (p : OuterPlan n) (slots : Nat)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s, (w.program s).gateSlots ≤ slots) (start : Nat) :
    (p.round start).gateSlots ≤ 29*slots+54634 := by
  have hl := outerAxis_slots_le p.wires p.left.toList slots
    (fun w h => hw w (List.mem_append_left _ h)) start List.nil
  have hr := outerAxis_slots_le p.wires p.right.toList slots
    (fun w h => hw w (List.mem_append_right _ h)) (start+axisCount p.left.toList) List.nil
  simp only [Vector.length_toList, List.length_nil] at hl hr
  simp only [OuterPlan.round, castFinish_gateSlots, Straight.gateSlots, Straight.gateSlots_append, resetProgram_gateSlots]
  have h := outer_feedback_overhead
  omega

theorem OuterPlan.round_t_le {n : Nat} (p : OuterPlan n) (cost : Nat) (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s h, ((w.program s).instantiate read h).tCount ≤ cost)
    (start : Nat) (history : Fin start → Bool) :
    ((p.round start).instantiate read history).tCount ≤ 29*cost+54168 := by
  have hl := outerAxis_t_le p.wires p.left.toList cost read
    (fun w h => hw w (List.mem_append_left _ h)) start List.nil history
  have hr (h) := outerAxis_t_le p.wires p.right.toList cost read
    (fun w h => hw w (List.mem_append_right _ h)) (start+axisCount p.left.toList) List.nil h
  simp only [Vector.length_toList, List.length_nil] at hl hr
  simp only [OuterPlan.round, castFinish_instantiate, Straight.instantiate, TemplateGate.instantiate,
    AdaptiveCircuit.tCount, ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    tCost, Nat.zero_add]
  apply (outer_append_t_le _ _ read history (13*cost+axisFeedback 13 0) ?_).trans
  · have h := outer_feedback_overhead; omega
  · intro h
    apply (outer_append_t_le _ _ read h 0 ?_).trans
    · have ht := hr h; omega
    · intro h₂
      simp [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
        ShorECDLP.tCount, tCost, resetProgram_t]

theorem OuterPlan.repeat_slots_le {n : Nat} (p : OuterPlan n) (slots : Nat)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s, (w.program s).gateSlots ≤ slots)
    (count start : Nat) : (p.repeat count start).gateSlots ≤ count*(29*slots+54634) := by
  induction count generalizing start with
  | zero => simp [OuterPlan.repeat, Straight.gateSlots]
  | succ k ih =>
    simp only [OuterPlan.repeat, castFinish_gateSlots, Straight.gateSlots_append, Nat.succ_mul]
    have h := p.round_slots_le slots hw start
    have ht := ih (start+p.stride)
    nlinarith

theorem OuterPlan.repeat_t_le {n : Nat} (p : OuterPlan n) (cost : Nat) (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s h, ((w.program s).instantiate read h).tCount ≤ cost)
    (count start : Nat) (history : Fin start → Bool) :
    ((p.repeat count start).instantiate read history).tCount ≤ count*(29*cost+54168) := by
  induction count generalizing start with
  | zero => simp [OuterPlan.repeat, Straight.instantiate, AdaptiveCircuit.tCount]
  | succ k ih =>
    simp only [OuterPlan.repeat, castFinish_instantiate]
    apply (outer_append_t_le _ _ read history (k*(29*cost+54168)) (ih _)).trans
    have h := p.round_t_le cost read hw start history
    nlinarith

theorem axisCount_le {n : Nat} (ws : List (OuterWindow n)) (measurements : Nat)
    (hw : ∀ w ∈ ws, w.count ≤ measurements) : axisCount ws ≤ ws.length*(measurements+16) := by
  induction ws with
  | nil => simp [axisCount]
  | cons w ws ih =>
    have h := hw w (by simp)
    have ht := ih (fun v hv => hw v (List.mem_cons_of_mem w hv))
    simp only [axisCount, List.length_cons, Nat.succ_mul]; omega

theorem OuterPlan.stride_le {n : Nat} (p : OuterPlan n) (measurements : Nat)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, w.count ≤ measurements) :
    p.stride ≤ 29*measurements+464+p.reset.length := by
  have hl := axisCount_le p.left.toList measurements (fun w h => hw w (List.mem_append_left _ h))
  have hr := axisCount_le p.right.toList measurements (fun w h => hw w (List.mem_append_right _ h))
  simp only [Vector.length_toList] at hl hr
  dsimp only [OuterPlan.stride]; omega

/-- Shared support is preserved by sequential composition, independently of
which measurement history reaches the suffix. -/
theorem outer_append_support {n s m e : Nat} (p : Straight n s m) (q : Straight n m e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (support : List Wire)
    (hp : (p.instantiate read history).wires ⊆ support)
    (hq : ∀ h, (q.instantiate read h).wires ⊆ support) :
    ((p.append q).instantiate read history).wires ⊆ support := by
  induction p with
  | done => exact hq history
  | gate g p ih =>
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hp (List.mem_append_left _ hw)
    · exact ih q history (fun _ h => hp (List.mem_append_right _ h)) hq hw
  | recordGate i v g p ih =>
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hp (List.mem_append_left _ hw)
    · exact ih q history (fun _ h => hp (List.mem_append_right _ h)) hq hw
  | measure v p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with hw | hw
    · subst w; exact hp List.mem_cons_self
    · rcases List.mem_append.mp hw with hw | hw
      · exact ih q (Fin.lastCases false history)
          (fun _ h => hp (List.mem_cons_of_mem _ (List.mem_append_left _ h))) hq hw
      · exact ih q (Fin.lastCases true history)
          (fun _ h => hp (List.mem_cons_of_mem _ (List.mem_append_right _ h))) hq hw

theorem prepareOuterBank_support {n s e : Nat} (ws support : List Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (hw : ws ⊆ support) (hp : (p.instantiate read history).wires ⊆ support) :
    ((prepareOuterBank ws p).instantiate read history).wires ⊆ support := by
  induction ws with
  | nil => exact hp
  | cons w ws ih =>
    intro v hv
    change v ∈ circuitWires [.H w] ++ _ at hv
    simp only [circuitWires, List.flatMap_cons, List.flatMap_nil, gateWires, List.append_nil,
      List.mem_append, List.mem_singleton] at hv
    rcases hv with rfl | hv
    · exact hw List.mem_cons_self
    · exact ih (fun _ h => hw (List.mem_cons_of_mem _ h)) hv

theorem feedbackProgram_support {n s e : Nat} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (support : List Wire) (hw : w ∈ support) (hp : (p.instantiate read history).wires ⊆ support) :
    ((feedbackProgram dir w indices k p).instantiate read history).wires ⊆ support := by
  induction indices generalizing k with
  | nil => exact hp
  | cons i is ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · change v ∈ circuitWires (if history i = true then [.P dir k w] else []) at hv
      split at hv
      · simp only [circuitWires, List.flatMap_cons, List.flatMap_nil, gateWires, List.append_nil, List.mem_singleton] at hv
        subst v; exact hw
      · simp [circuitWires] at hv
    · exact ih (k+1) hv

theorem fourierProgram_support (n : Nat) (dir : PhaseDir) (ws : List Wire) (start : Nat)
    (prior : List (Fin start)) (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (support : List Wire) (hw : ws ⊆ support) :
    ((fourierProgram n dir ws start prior).instantiate read history).wires ⊆ support := by
  induction ws generalizing start with
  | nil => exact List.nil_subset _
  | cons w ws ih =>
    simp only [fourierProgram, castFinish_instantiate]
    apply feedbackProgram_support _ _ _ _ _ _ _ support (hw List.mem_cons_self)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hw List.mem_cons_self
    · rcases List.mem_append.mp hv with hv | hv
      all_goals exact ih _ _ _ (fun _ h => hw (List.mem_cons_of_mem _ h)) hv

theorem resetProgram_support (n start : Nat) (ws support : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (hw : ws ⊆ support) :
    ((resetProgram n start ws).instantiate read history).wires ⊆ support := by
  induction ws generalizing start with
  | nil => exact List.nil_subset _
  | cons w ws ih =>
    simp only [resetProgram, castFinish_instantiate, Straight.instantiate, AdaptiveCircuit.wires]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hw List.mem_cons_self
    · rcases List.mem_append.mp hv with hv | hv
      all_goals exact ih _ _ (fun _ h => hw (List.mem_cons_of_mem _ h)) hv

theorem outerAxis_support {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n))
    (support : List Wire) (read : ConstantBit n → Bool) (hf : wires.toList ⊆ support)
    (hw : ∀ w ∈ ws, ∀ s h, ((w.program s).instantiate read h).wires ⊆ support)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((outerAxis wires ws start prior).instantiate read history).wires ⊆ support := by
  induction ws generalizing start with
  | nil => exact List.nil_subset _
  | cons w ws ih =>
    simp only [outerAxis, castFinish_instantiate]
    apply outer_append_support _ _ read history support
    · exact prepareOuterBank_support _ _ _ read history
        (fun _ h => hf (List.mem_reverse.mp h)) (hw w (by simp) start history)
    · intro h
      apply outer_append_support _ _ read h support
      · simpa only [castFinish_instantiate] using fourierProgram_support n .inverse wires.toList _ _ read h support hf
      · intro h₂
        exact ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _ _ h₂

theorem outer_control_support {n s e : Nat} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (support : List Wire) (hc : 836 ∈ support)
    (hp : (p.instantiate read history).wires ⊆ support) :
    ((Straight.gate (.literal (.X 836)) p).instantiate read history).wires ⊆ support := by
  intro v hv
  change v ∈ circuitWires [.X 836] ++ _ at hv
  simp only [circuitWires, List.flatMap_cons, List.flatMap_nil, gateWires, List.append_nil,
    List.mem_append, List.mem_singleton] at hv
  exact hv.elim (fun h => h ▸ hc) (fun h => hp h)

theorem OuterPlan.round_support {n : Nat} (p : OuterPlan n) (support : List Wire)
    (read : ConstantBit n → Bool) (hf : p.wires.toList ⊆ support) (hr : p.reset ⊆ support)
    (hx : 836 ∈ support)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s h, ((w.program s).instantiate read h).wires ⊆ support)
    (start : Nat) (history : Fin start → Bool) :
    ((p.round start).instantiate read history).wires ⊆ support := by
  simp only [OuterPlan.round, castFinish_instantiate]
  apply outer_control_support _ _ _ _ hx
  apply outer_append_support _ _ read history support
  · exact outerAxis_support _ _ support read hf (fun w h => hw w (List.mem_append_left _ h)) _ _ _
  · intro h
    apply outer_append_support _ _ read h support
    · exact outerAxis_support _ _ support read hf (fun w h => hw w (List.mem_append_right _ h)) _ _ _
    · intro h₂
      exact outer_control_support _ _ _ _ hx (resetProgram_support _ _ _ support read h₂ hr)

theorem OuterPlan.repeat_support {n : Nat} (p : OuterPlan n) (support : List Wire)
    (read : ConstantBit n → Bool) (hf : p.wires.toList ⊆ support) (hr : p.reset ⊆ support)
    (hx : 836 ∈ support)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s h, ((w.program s).instantiate read h).wires ⊆ support)
    (count start : Nat) (history : Fin start → Bool) :
    ((p.repeat count start).instantiate read history).wires ⊆ support := by
  induction count generalizing start with
  | zero => simp [OuterPlan.repeat, Straight.instantiate, AdaptiveCircuit.wires]
  | succ k ih =>
    simp only [OuterPlan.repeat, castFinish_instantiate]
    exact outer_append_support _ _ read history support (p.round_support support read hf hr hx hw _ _) (ih _)

/-- Producer-facing uniform window estimates. The support is shared across
all rounds; it is not multiplied by the number of windows or repetitions. -/
structure OuterBudget (coefficients : List PointCoeff) (p : OuterPlan coefficients.length) where
  support : List Wire
  slotBound : Nat
  tBound : Nat
  measurementBound : Nat
  fourierSupport : p.wires.toList ⊆ support
  resetSupport : p.reset ⊆ support
  controlSupport : 836 ∈ support
  windowSlots : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s, (w.program s).gateSlots ≤ slotBound
  windowCount : ∀ w ∈ p.left.toList ++ p.right.toList, w.count ≤ measurementBound
  windowT : ∀ (Q : Secp256k1.Point) w, w ∈ p.left.toList ++ p.right.toList → ∀ s h,
    ((w.program s).instantiate (readConstant coefficients.get Q) h).tCount ≤ tBound
  windowSupport : ∀ (Q : Secp256k1.Point) w, w ∈ p.left.toList ++ p.right.toList → ∀ s h,
    ((w.program s).instantiate (readConstant coefficients.get Q) h).wires ⊆ support

def OuterBudget.bounds {coefficients : List PointCoeff} {p : OuterPlan coefficients.length}
    (b : OuterBudget coefficients p) : Bounds :=
  ⟨b.support.toFinset.card, 56*(29*b.tBound+54168),
    56*(29*b.measurementBound+464+p.reset.length)⟩

theorem OuterBudget.gateSlots {coefficients : List PointCoeff} {p : OuterPlan coefficients.length}
    (b : OuterBudget coefficients p) : (p.entry coefficients).program.gateSlots ≤ 56*(29*b.slotBound+54634) := by
  simpa only [OuterPlan.entry, castFinish_gateSlots] using p.repeat_slots_le b.slotBound b.windowSlots 56 0

theorem OuterBudget.finalCursor {coefficients : List PointCoeff} {p : OuterPlan coefficients.length}
    (b : OuterBudget coefficients p) : (p.entry coefficients).finalCursor ≤ b.bounds.measurements := by
  exact Nat.mul_le_mul_left 56 (p.stride_le b.measurementBound b.windowCount)

theorem OuterBudget.resources {coefficients : List PointCoeff} {p : OuterPlan coefficients.length}
    (b : OuterBudget coefficients p) (Q : Secp256k1.Point) :
    (resources ((p.entry coefficients).instantiate Q)).qubits ≤ b.bounds.qubits ∧
    (resources ((p.entry coefficients).instantiate Q)).tModel ≤ b.bounds.tModel ∧
    (resources ((p.entry coefficients).instantiate Q)).measurements ≤ b.bounds.measurements := by
  have hs : ((p.entry coefficients).instantiate Q).wires ⊆ b.support := by
    simpa only [OuterPlan.entry, StraightEntry.instantiate, castFinish_instantiate] using
      p.repeat_support b.support (readConstant coefficients.get Q) b.fourierSupport b.resetSupport
        b.controlSupport (b.windowSupport Q) 56 0 Fin.elim0
  have hc : ((p.entry coefficients).instantiate Q).wires.toFinset ⊆ b.support.toFinset := by
    intro w hw; exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hw))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [resources, AdaptiveCircuit.qubitCount, OuterBudget.bounds, List.card_toFinset] using Finset.card_le_card hc
  · simpa only [resources, OuterBudget.bounds, OuterPlan.entry, StraightEntry.instantiate,
      castFinish_instantiate] using p.repeat_t_le b.tBound (readConstant coefficients.get Q) (b.windowT Q) 56 0 Fin.elim0
  · change ((p.entry coefficients).program.instantiate (readConstant coefficients.get Q) Fin.elim0).measurementCount ≤ _
    rw [Straight.measurementCount, Nat.sub_zero]
    exact b.finalCursor

/-- Resource fields now follow from local window budgets. Only physical window
validity and the final decoder success proof are still needed here. -/
theorem OuterBudget.assembly {coefficients : List PointCoeff} {p : OuterPlan coefficients.length}
    (b : OuterBudget coefficients p) (hp : p.WindowsWellFormed)
    (hs : ∀ (Q : Secp256k1.Point) (d : Nat), Q ≠ 0 → Q = d • Secp256k1.G →
      (99 : ℝ)/100 ≤ Instrument.bornMass
        (((p.entry coefficients).instantiate Q).run.filter
          (fun branch => (verifiedCandidate p.layout Q branch.history).isSome)) (ket zeroBasisState)) :
    StreamingAssembly p.layout (p.entry coefficients) b.bounds :=
  p.assembly coefficients hp b.bounds b.resources hs

end ShorECDLP.Paper2607_13816.ChallengeMigration
