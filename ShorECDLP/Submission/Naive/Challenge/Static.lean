import ShorECDLP.Submission.Naive.Challenge.TrialGates

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge

/-- Non-X constant-controlled gates depend only on the infinity flag. -/
def SlotSafe {n : Nat} : TemplateGate n → Prop
  | .literal _ => True
  | .whenBit r _ g => (∃ w, g = .X w) ∨ (r.field = .infinity ∧ r.bit.val = 0)
def SlotsSafe {n : Nat} (gs : List (TemplateGate n)) : Prop := ∀ g ∈ gs, SlotSafe g

@[simp] theorem slotsSafe_append {n : Nat} (a b : List (TemplateGate n)) :
    SlotsSafe (a++b) ↔ SlotsSafe a ∧ SlotsSafe b := by
  simp only [SlotsSafe, List.mem_append, or_imp, forall_and]
@[simp] theorem slotsSafe_literal {n : Nat} (c : Circuit) :
    SlotsSafe (c.map (TemplateGate.literal (tableSize := n))) := by
  intro g hg
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
  trivial
@[simp] theorem slotsSafe_reverse {n : Nat} (gs : List (TemplateGate n)) :
    SlotsSafe gs.reverse ↔ SlotsSafe gs := by simp only [SlotsSafe, List.mem_reverse]

@[simp] theorem slotsSafe_fieldLoad {n : Nat} (row : Fin n) (field : PointField)
    (ws : List Wire) (i : Nat) : SlotsSafe (fieldLoadGates row field ws i) := by
  induction ws generalizing i with
  | nil => simp [SlotsSafe, fieldLoadGates]
  | cons w ws ih =>
    simp only [fieldLoadGates, slotsSafe_append]
    refine ⟨?_, ih _⟩
    split <;> simp [SlotsSafe, SlotSafe]
@[simp] theorem slotsSafe_packedLoad {n : Nat} (row : Fin n) (ws : List Wire) (i : Nat) :
    SlotsSafe (packedLoadGates row ws i) := by
  induction ws generalizing i with
  | nil => simp [SlotsSafe, packedLoadGates]
  | cons w ws ih =>
    simp only [packedLoadGates, slotsSafe_append]
    refine ⟨?_, ih _⟩
    unfold packedGate
    split
    · simp [SlotsSafe, SlotSafe]
    · split
      · simp [SlotsSafe, SlotSafe]
      · split <;> simp [SlotsSafe, SlotSafe]

@[simp] theorem slotsSafe_guard {n : Nat} (row : Fin n) (gs : List (TemplateGate n))
    (h : SlotsSafe gs) : SlotsSafe (gs.map (guardSlot row)) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  cases a with
  | literal g => exact Or.inr ⟨rfl, rfl⟩
  | whenBit r b g => exact h _ ha

@[simp] theorem slotsSafe_controlledOut {n : Nat} (row : Fin n) (control : Wire)
    (pointReg outReg : List Wire) (workStart : Wire) :
    SlotsSafe (controlledOutGates row control pointReg outReg workStart) := by
  simp only [controlledOutGates, slotsSafe_append]
  constructor
  · apply slotsSafe_guard
    simp only [finiteControlledOutGates, finiteComputeGates, pointFlagGates, genericBranchGates,
      genericPointGates, infinityBranchGates, fieldSubConstGates,
      slotsSafe_append, slotsSafe_reverse, slotsSafe_literal, slotsSafe_fieldLoad,
      slotsSafe_packedLoad, and_self]
  · intro g hg
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
    exact Or.inr ⟨rfl, rfl⟩

@[simp] theorem slotsSafe_negControlledOut {n : Nat} (row : Fin n) (control : Wire)
    (pointReg outReg : List Wire) (workStart : Wire) :
    SlotsSafe (negControlledOutGates row control pointReg outReg workStart) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  have hs := slotsSafe_controlledOut (0 : Fin 1) control pointReg outReg workStart a ha
  cases a with
  | literal g => trivial
  | whenBit r b g =>
    rcases hs with hx | ⟨hf, hi⟩
    · exact Or.inl hx
    · exact Or.inr ⟨by simp [negRowRef, hf, negPointField], hi⟩

@[simp] theorem slotsSafe_controlledPoint {n : Nat} (row : Fin n) (control : Wire)
    (pointReg : List Wire) (workStart : Wire) :
    SlotsSafe (controlledPointGates row control pointReg workStart) := by
  simp only [controlledPointGates, slotsSafe_append, slotsSafe_reverse, slotsSafe_controlledOut,
    slotsSafe_literal, slotsSafe_negControlledOut, and_self]

theorem slotSafe_wellFormed {n : Nat} (g : TemplateGate n) (hs : SlotSafe g)
    (r0 r1 : ConstantBit n → Bool)
    (h0 : ∀ row, r0 ⟨row, .infinity, 0⟩ = false)
    (h1 : ∀ row, r1 ⟨row, .infinity, 0⟩ = true)
    (w0 : CircuitWellFormed (g.instantiate r0))
    (w1 : CircuitWellFormed (g.instantiate r1)) : g.WellFormed := by
  cases g with
  | literal g => exact w0 g (by simp [TemplateGate.instantiate])
  | whenBit ref b g =>
    rcases hs with ⟨w, rfl⟩ | ⟨hf, hi⟩
    · trivial
    · have he : ref = ⟨ref.point, .infinity, 0⟩ := by
        cases ref with
        | mk row field bit => simp_all only [ConstantBit.mk.injEq, true_and, Fin.ext_iff, Fin.val_zero]
      have hr0 : r0 ref = false := by rw [he]; exact h0 _
      have hr1 : r1 ref = true := by rw [he]; exact h1 _
      cases b with
      | false => exact w0 g (by simp only [TemplateGate.instantiate, hr0, ↓reduceIte, List.mem_singleton])
      | true => exact w1 g (by simp only [TemplateGate.instantiate, hr1, ↓reduceIte, List.mem_singleton])

theorem slotsSafe_wellFormed {n : Nat} (gs : List (TemplateGate n)) (hs : SlotsSafe gs)
    (r0 r1 : ConstantBit n → Bool)
    (h0 : ∀ row, r0 ⟨row, .infinity, 0⟩ = false)
    (h1 : ∀ row, r1 ⟨row, .infinity, 0⟩ = true)
    (w0 : CircuitWellFormed (gs.flatMap (TemplateGate.instantiate r0)))
    (w1 : CircuitWellFormed (gs.flatMap (TemplateGate.instantiate r1))) :
    ∀ g ∈ gs, g.WellFormed := by
  intro g hg
  apply slotSafe_wellFormed g (hs g hg) r0 r1 h0 h1
  · intro a ha
    exact w0 a (List.mem_flatMap.mpr ⟨g, hg, ha⟩)
  · intro a ha
    exact w1 a (List.mem_flatMap.mpr ⟨g, hg, ha⟩)

theorem qCoefficient_infinity_G {n : Nat} (row : Fin n) :
    readConstant (fun _ : Fin n => qCoefficient) G ⟨row, .infinity, 0⟩ = false := by
  simp only [readConstant, qCoefficient_point]
  rfl

theorem qCoefficient_infinity_zero {n : Nat} (row : Fin n) :
    readConstant (fun _ : Fin n => qCoefficient) 0 ⟨row, .infinity, 0⟩ = true := by
  simp only [readConstant, qCoefficient_point]
  rfl

theorem controlledPointGates_wellFormed {n : Nat} (row : Fin n) (control : Wire)
    (pointReg : List Wire) (workStart : Wire)
    (hlen : pointReg.length = pointWidth)
    (hn : ([control] ++ pointReg ++ controlledPointAddWork workStart).Nodup) :
    ∀ g ∈ controlledPointGates row control pointReg workStart, g.WellFormed := by
  apply slotsSafe_wellFormed _ (slotsSafe_controlledPoint row control pointReg workStart)
    (readConstant (fun _ : Fin n => qCoefficient) G)
    (readConstant (fun _ : Fin n => qCoefficient) 0)
    qCoefficient_infinity_G qCoefficient_infinity_zero
  · rw [controlledPointGates_source, qCoefficient_point]
    exact controlledPointAdd_wellFormed control pointReg workStart G hlen hn
  · rw [controlledPointGates_source, qCoefficient_point]
    exact controlledPointAdd_wellFormed control pointReg workStart 0 hlen hn

theorem scalarGates_wellFormed {n : Nat} (pointReg : List Wire) (workStart : Wire)
    (controls : List Wire) (rows : List (Fin n)) (hlen : pointReg.length = pointWidth)
    (hn : (controls ++ (pointReg ++ controlledPointAddWork workStart)).Nodup) :
    ∀ g ∈ scalarGates pointReg workStart controls rows, g.WellFormed := by
  induction controls generalizing rows with
  | nil => simp [scalarGates]
  | cons c cs ih =>
    cases rows with
    | nil => simp [scalarGates]
    | cons r rs =>
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · apply controlledPointGates_wellFormed r c pointReg workStart hlen ?_ g hg
        have hs := List.nodup_append.mp hn
        have hc : c ∉ pointReg ++ controlledPointAddWork workStart := by
          intro hc
          exact hs.2.2 c List.mem_cons_self c hc rfl
        simpa only [List.singleton_append, List.append_assoc] using
          (List.nodup_cons.mpr ⟨hc, hs.2.1⟩)
      · exact ih rs hn.tail g hg

theorem trialGates_wellFormed : ∀ g ∈ trialGates, g.WellFormed := by
  obtain ⟨ha, hb, hp, hn, hf⟩ := bitcoinWireLayout
  have hn' : ((bitcoinAReg ++ bitcoinBReg) ++
      (bitcoinPointReg ++ controlledPointAddWork bitcoinWorkStart)).Nodup := by
    simpa only [scalarMulWork, List.append_assoc] using hn
  have ha' : (bitcoinAReg ++ (bitcoinPointReg ++ controlledPointAddWork bitcoinWorkStart)).Nodup := by
    exact (List.sublist_append_left bitcoinAReg bitcoinBReg).append (List.Sublist.refl _) |>.nodup hn'
  have hb' : (bitcoinBReg ++ (bitcoinPointReg ++ controlledPointAddWork bitcoinWorkStart)).Nodup := by
    exact (List.sublist_append_right bitcoinAReg bitcoinBReg).append (List.Sublist.refl _) |>.nodup hn'
  have hab := hn'.of_append_left
  have hfa : bitcoinQFTAncilla ∉ bitcoinAReg := by
    intro h; exact hf (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl h)))
  have hfb : bitcoinQFTAncilla ∉ bitcoinBReg := by
    intro h; exact hf (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr h)))
  intro g hg
  simp only [trialGates, List.mem_append] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    have hh : CircuitWellFormed (PhaseEstimation.hadamards (bitcoinAReg ++ bitcoinBReg)) := by
      intro g hg
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
      trivial
    exact hh a ha
  · exact scalarGates_wellFormed _ _ _ _ hp ha' g hg
  · exact scalarGates_wellFormed _ _ _ _ hp hb' g hg
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact ((circuitWellFormed_append _ _).mpr ⟨iqft_wellFormed _ _ hfa hab.of_append_left,
      iqft_wellFormed _ _ hfb hab.of_append_right⟩) a ha

theorem trialProgram_wellFormed (cursor : Nat) : (trialProgram cursor).WellFormed :=
  constantGateProgram_wellFormed trialGates cursor trialGates_wellFormed

theorem straight_append_wellFormed {n a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (hp : p.WellFormed) (hq : q.WellFormed) : (p.append q).WellFormed := by
  induction p with
  | done => exact hq
  | gate g next ih => exact ⟨hp.1, ih q hp.2 hq⟩
  | recordGate r v g next ih => exact ⟨hp.1, ih q hp.2 hq⟩
  | measure w next ih => exact ih q hp hq

theorem observeWires_wellFormed {n : Nat} (ws : List Wire) (cursor : Nat) :
    (observeWires (n := n) ws cursor).WellFormed := by
  induction ws generalizing cursor with
  | nil => trivial
  | cons w ws ih =>
    simp only [observeWires, Straight.WellFormed, TemplateGate.WellFormed,
      Gate.WellFormed, wellFormed_castFinish, ih, and_self]

theorem observedTrialProgram_wellFormed (cursor : Nat) :
    (observedTrialProgram cursor).WellFormed :=
  straight_append_wellFormed _ _ (trialProgram_wellFormed cursor) (observeWires_wellFormed _ _)

end ShorECDLP.NaiveChallenge
