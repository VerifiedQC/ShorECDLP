import ShorECDLP.Framework.Quantum.Adaptive

/-!
# Compile away a fixed constant control

The uncontrolled Gidney comparator is the controlled gate stream with each
CNOT from its external control replaced by X. The control is a proof parameter
only: the resulting circuit contains no such physical wire. This pass also
preserves measurement outcomes and phases.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

/-- Specialize a CNOT control to the classical constant one. -/
def constantControlGate (q : Wire) : Gate → Gate
  | .CX c t => if c = q then .X t else .CX c t
  | g => g

/-- The eliminated wire may occur only as the control of a CNOT. -/
def constantControlSafe (q : Wire) : Gate → Prop
  | .X t | .H t | .P _ _ t => t ≠ q
  | .CX _ t => t ≠ q
  | .CCX a b t => a ≠ q ∧ b ≠ q ∧ t ≠ q

private noncomputable def setControl (q : Wire) (b : Bool) :
    Quantum.State →ₗ[ℂ] Quantum.State :=
  Finsupp.linearCombination ℂ (fun s => Quantum.ket (upd s q b))

private theorem setControl_ket (q : Wire) (b : Bool) (s : BasisState) :
    setControl q b (Quantum.ket s) = Quantum.ket (upd s q b) := by
  simp [setControl, Quantum.ket]

private theorem setControl_commute (s : BasisState) (q t : Wire) (b c : Bool)
    (ht : t ≠ q) : upd (upd s q b) t c = upd (upd s t c) q b := by
  funext w
  by_cases hwq : w = q <;> by_cases hwt : w = t <;> simp_all [upd]

private theorem constantControlGate_intertwine (q : Wire) (g : Gate)
    (h : constantControlSafe q g) :
    (Quantum.applyGate g).comp (setControl q true) =
      (setControl q true).comp (Quantum.applyGate (constantControlGate q g)) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change Quantum.applyGate g (setControl q true (Quantum.ket s)) =
    setControl q true (Quantum.applyGate (constantControlGate q g) (Quantum.ket s))
  rw [setControl_ket]
  cases g with
  | X t =>
      change t ≠ q at h
      simpa [constantControlGate, Quantum.onKet, setControl_ket, upd, h]
      using congrArg Quantum.ket (setControl_commute s q t true (!s t) h)
  | H t =>
      change t ≠ q at h
      simp only [constantControlGate, Quantum.applyGate_H_ket, map_add, map_smul,
        setControl_ket]
      simp only [upd, if_neg h]
      rw [setControl_commute s q t true false h, setControl_commute s q t true true h]
  | CX c t =>
      change t ≠ q at h
      by_cases hc : c = q
      · subst c
        simp only [constantControlGate, if_pos rfl, Quantum.applyGate_CX_ket,
          Quantum.applyGate_X_ket, setControl_ket]
        simpa [upd, h, Quantum.onKet, setControl_ket] using congrArg Quantum.ket
          (setControl_commute s q t true (!s t) h)
      · simp only [constantControlGate, if_neg hc, Quantum.applyGate_CX_ket,
          setControl_ket]
        simpa [upd, h, hc] using congrArg Quantum.ket
          (setControl_commute s q t true (Bool.xor (s t) (s c)) h)
  | CCX a b t =>
      rcases h with ⟨ha,hb,ht⟩
      simp only [constantControlGate, Quantum.applyGate_CCX_ket, setControl_ket]
      simpa [upd,ha,hb,ht] using congrArg Quantum.ket
        (setControl_commute s q t true (Bool.xor (s t) (s a && s b)) ht)
  | P dir k t =>
      change t ≠ q at h
      cases hs : s t <;> simp [constantControlGate,Quantum.onKet,setControl_ket,upd,h,hs]

private theorem gate_setControl (q : Wire) (b : Bool) (g : Gate)
    (h : q ∉ gateWires g) :
    (Quantum.applyGate g).comp (setControl q b) =
      (setControl q b).comp (Quantum.applyGate g) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change Quantum.applyGate g (setControl q b (Quantum.ket s)) =
    setControl q b (Quantum.applyGate g (Quantum.ket s))
  rw [setControl_ket]
  cases g with
  | X t =>
      have ht : t ≠ q := by simpa [gateWires, eq_comm] using h
      simpa [Quantum.onKet, setControl_ket, upd, ht]
        using congrArg Quantum.ket (setControl_commute s q t b (!s t) ht)
  | H t =>
      have ht : t ≠ q := by simpa [gateWires, eq_comm] using h
      simp only [Quantum.applyGate_H_ket, map_add, map_smul, setControl_ket]
      simp only [upd, if_neg ht]
      rw [setControl_commute s q t b false ht, setControl_commute s q t b true ht]
  | CX c t =>
      have hc : c ≠ q := by simp_all [gateWires, eq_comm]
      have ht : t ≠ q := by simp_all [gateWires, eq_comm]
      simpa [Quantum.onKet, setControl_ket, upd, ht, hc]
        using congrArg Quantum.ket (setControl_commute s q t b (Bool.xor (s t) (s c)) ht)
  | CCX a c t =>
      have ha : a ≠ q := by simp_all [gateWires, eq_comm]
      have hc : c ≠ q := by simp_all [gateWires, eq_comm]
      have ht : t ≠ q := by simp_all [gateWires, eq_comm]
      simpa [Quantum.onKet, setControl_ket, upd, ht, ha, hc]
        using congrArg Quantum.ket (setControl_commute s q t b
          (Bool.xor (s t) (s a && s c)) ht)
  | P dir k t =>
      have ht : t ≠ q := by simpa [gateWires, eq_comm] using h
      cases hs : s t <;> simp [Quantum.onKet,setControl_ket,upd,ht,hs]

private theorem constantControlGate_noControl (q : Wire) (g : Gate)
    (h : constantControlSafe q g) : q ∉ gateWires (constantControlGate q g) := by
  cases g with
  | CX c t =>
      by_cases hc : c = q <;>
        simp_all [constantControlGate,constantControlSafe,gateWires,eq_comm]
  | _ => simpa [constantControlGate,constantControlSafe,gateWires,eq_comm] using h

private theorem reset_setControl (q t : Wire) (b outcome : Bool) (h : t ≠ q) :
    (Quantum.xResetKraus t outcome).comp (setControl q b) =
      (setControl q b).comp (Quantum.xResetKraus t outcome) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change Quantum.xResetKraus t outcome (setControl q b (Quantum.ket s)) =
    setControl q b (Quantum.xResetKraus t outcome (Quantum.ket s))
  rw [setControl_ket, Quantum.xResetKraus_ket, Quantum.xResetKraus_ket, map_smul,
    setControl_ket]
  simp only [upd, if_neg h]
  rw [setControl_commute s q t b false h]

/-- Compile each unitary block while retaining the adaptive measurement tree. -/
def constantControlProgram (q : Wire) : Quantum.AdaptiveCircuit → Quantum.AdaptiveCircuit
  | .done => .done
  | .unitary circuit next => .unitary (circuit.map (constantControlGate q))
      (constantControlProgram q next)
  | .xMeasureReset t onFalse onTrue => .xMeasureReset t
      (constantControlProgram q onFalse) (constantControlProgram q onTrue)

/-- A constant control is never targeted, measured, or used in a Toffoli. -/
def constantControlProgramSafe (q : Wire) : Quantum.AdaptiveCircuit → Prop
  | .done => True
  | .unitary circuit next => (∀ g ∈ circuit, constantControlSafe q g) ∧
      constantControlProgramSafe q next
  | .xMeasureReset t onFalse onTrue => t ≠ q ∧
      constantControlProgramSafe q onFalse ∧ constantControlProgramSafe q onTrue

private theorem constantControlCircuit_intertwine (q : Wire) (circuit : Circuit)
    (h : ∀ g ∈ circuit, constantControlSafe q g) :
    (Quantum.run circuit).comp (setControl q true) =
      (setControl q true).comp (Quantum.run (circuit.map (constantControlGate q))) := by
  induction circuit with
  | nil => rfl
  | cons g circuit ih =>
      have hg := constantControlGate_intertwine q g (h g (by simp))
      have hc := ih (fun g hg => h g (by simp [hg]))
      change (Quantum.run circuit ∘ₗ Quantum.applyGate g) ∘ₗ setControl q true =
        setControl q true ∘ₗ (Quantum.run (circuit.map (constantControlGate q)) ∘ₗ
          Quantum.applyGate (constantControlGate q g))
      rw [LinearMap.comp_assoc, hg, ← LinearMap.comp_assoc, hc, LinearMap.comp_assoc]

private theorem constantControlCircuit_commute (q : Wire) (b : Bool) (circuit : Circuit)
    (h : ∀ g ∈ circuit, constantControlSafe q g) :
    (Quantum.run (circuit.map (constantControlGate q))).comp (setControl q b) =
      (setControl q b).comp (Quantum.run (circuit.map (constantControlGate q))) := by
  induction circuit with
  | nil => rfl
  | cons g circuit ih =>
      have hg := gate_setControl q b (constantControlGate q g)
        (constantControlGate_noControl q g (h g (by simp)))
      have hc := ih (fun g hg => h g (by simp [hg]))
      change (Quantum.run (circuit.map (constantControlGate q)) ∘ₗ
          Quantum.applyGate (constantControlGate q g)) ∘ₗ setControl q b =
        setControl q b ∘ₗ (Quantum.run (circuit.map (constantControlGate q)) ∘ₗ
          Quantum.applyGate (constantControlGate q g))
      rw [LinearMap.comp_assoc, hg, ← LinearMap.comp_assoc, hc, LinearMap.comp_assoc]

private theorem constantControlProgram_intertwine (q : Wire) (program : Quantum.AdaptiveCircuit)
    (h : constantControlProgramSafe q program) (after : Quantum.InstrumentBranch)
    (ha : after ∈ (constantControlProgram q program).run) :
    ∃ before ∈ program.run, before.history = after.history ∧
      before.kraus.comp (setControl q true) = (setControl q true).comp after.kraus ∧
      ∀ b, after.kraus.comp (setControl q b) = (setControl q b).comp after.kraus := by
  induction program generalizing after with
  | done =>
      simp only [constantControlProgram,Quantum.AdaptiveCircuit.run,List.mem_singleton] at ha
      subst after
      exact ⟨_,by simp [Quantum.AdaptiveCircuit.run],rfl,rfl,fun _ => rfl⟩
  | unitary circuit next ih =>
      rcases h with ⟨hc,hn⟩
      simp only [constantControlProgram,Quantum.AdaptiveCircuit.run,List.mem_map] at ha
      obtain ⟨rest,hr,rfl⟩ := ha
      obtain ⟨before,hb,hh,he,hcomm⟩ := ih hn rest hr
      refine ⟨⟨before.history,before.kraus.comp (Quantum.run circuit)⟩,?_,hh,?_,?_⟩
      · simp only [Quantum.AdaptiveCircuit.run,List.mem_map]
        exact ⟨before,hb,rfl⟩
      · change (before.kraus ∘ₗ Quantum.run circuit) ∘ₗ setControl q true =
          setControl q true ∘ₗ (rest.kraus ∘ₗ Quantum.run (circuit.map (constantControlGate q)))
        rw [LinearMap.comp_assoc,constantControlCircuit_intertwine q circuit hc,
          ← LinearMap.comp_assoc,he,LinearMap.comp_assoc]
      · intro b
        change (rest.kraus ∘ₗ Quantum.run (circuit.map (constantControlGate q))) ∘ₗ setControl q b =
          setControl q b ∘ₗ (rest.kraus ∘ₗ Quantum.run (circuit.map (constantControlGate q)))
        rw [LinearMap.comp_assoc,constantControlCircuit_commute q b circuit hc,
          ← LinearMap.comp_assoc,hcomm b,LinearMap.comp_assoc]
  | xMeasureReset t onFalse onTrue ihFalse ihTrue =>
      rcases h with ⟨ht,hf,htree⟩
      simp only [constantControlProgram,Quantum.AdaptiveCircuit.run,List.mem_append,List.mem_map] at ha
      rcases ha with ⟨rest,hr,rfl⟩ | ⟨rest,hr,rfl⟩
      · obtain ⟨before,hb,hh,he,hcomm⟩ := ihFalse hf rest hr
        refine ⟨⟨false :: before.history,before.kraus.comp (Quantum.xResetKraus t false)⟩,?_,?_,?_,?_⟩
        · simp only [Quantum.AdaptiveCircuit.run,List.mem_append,List.mem_map]
          exact Or.inl ⟨before,hb,rfl⟩
        · change false :: before.history = false :: rest.history
          rw [hh]
        · change (before.kraus ∘ₗ Quantum.xResetKraus t false) ∘ₗ setControl q true =
            setControl q true ∘ₗ (rest.kraus ∘ₗ Quantum.xResetKraus t false)
          rw [LinearMap.comp_assoc,reset_setControl q t true false ht,
            ← LinearMap.comp_assoc,he,LinearMap.comp_assoc]
        · intro b
          change (rest.kraus ∘ₗ Quantum.xResetKraus t false) ∘ₗ setControl q b =
            setControl q b ∘ₗ (rest.kraus ∘ₗ Quantum.xResetKraus t false)
          rw [LinearMap.comp_assoc,reset_setControl q t b false ht,
            ← LinearMap.comp_assoc,hcomm b,LinearMap.comp_assoc]
      · obtain ⟨before,hb,hh,he,hcomm⟩ := ihTrue htree rest hr
        refine ⟨⟨true :: before.history,before.kraus.comp (Quantum.xResetKraus t true)⟩,?_,?_,?_,?_⟩
        · simp only [Quantum.AdaptiveCircuit.run,List.mem_append,List.mem_map]
          exact Or.inr ⟨before,hb,rfl⟩
        · change true :: before.history = true :: rest.history
          rw [hh]
        · change (before.kraus ∘ₗ Quantum.xResetKraus t true) ∘ₗ setControl q true =
            setControl q true ∘ₗ (rest.kraus ∘ₗ Quantum.xResetKraus t true)
          rw [LinearMap.comp_assoc,reset_setControl q t true true ht,
            ← LinearMap.comp_assoc,he,LinearMap.comp_assoc]
        · intro b
          change (rest.kraus ∘ₗ Quantum.xResetKraus t true) ∘ₗ setControl q b =
            setControl q b ∘ₗ (rest.kraus ∘ₗ Quantum.xResetKraus t true)
          rw [LinearMap.comp_assoc,reset_setControl q t b true ht,
            ← LinearMap.comp_assoc,hcomm b,LinearMap.comp_assoc]

/-- Every specialized branch inherits the original branch's exact amplitude,
with the eliminated control restored to its arbitrary input value. -/
theorem constantControlProgram_branch (q : Wire) (program : Quantum.AdaptiveCircuit)
    (h : constantControlProgramSafe q program) (after : Quantum.InstrumentBranch)
    (ha : after ∈ (constantControlProgram q program).run) :
    ∃ before ∈ program.run, before.history = after.history ∧
      ∀ (s t : BasisState) (amplitude : ℂ),
        before.kraus (Quantum.ket (upd s q true)) = amplitude • Quantum.ket (upd t q true) →
        after.kraus (Quantum.ket s) = amplitude • Quantum.ket (upd t q (s q)) := by
  obtain ⟨before,hb,hh,he,hcomm⟩ := constantControlProgram_intertwine q program h after ha
  refine ⟨before,hb,hh,?_⟩
  intro s t amplitude hresult
  have hlift := congrArg (fun f : Quantum.State →ₗ[ℂ] Quantum.State => f (Quantum.ket s)) he
  simp only [LinearMap.comp_apply,setControl_ket] at hlift
  rw [hresult] at hlift
  have hrestore := congrArg (setControl q (s q)) hlift
  have hset (v : BasisState) : upd (upd v q true) q (s q) = upd v q (s q) := by
    funext w
    by_cases hw : w = q <;> simp [upd,hw]
  have hcompose : (setControl q (s q)).comp (setControl q true) = setControl q (s q) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    change setControl q (s q) (setControl q true (Quantum.ket v)) = setControl q (s q) (Quantum.ket v)
    simp only [setControl_ket,hset]
  have hs : upd s q (s q) = s := by
    funext w
    by_cases hw : w = q <;> simp_all [upd]
  rw [map_smul,setControl_ket,hset] at hrestore
  change amplitude • Quantum.ket (upd t q (s q)) =
    ((setControl q (s q)).comp (setControl q true)) (after.kraus (Quantum.ket s)) at hrestore
  rw [hcompose] at hrestore
  have hc := congrArg (fun f : Quantum.State →ₗ[ℂ] Quantum.State => f (Quantum.ket s)) (hcomm (s q))
  simp only [LinearMap.comp_apply,setControl_ket,hs] at hc
  exact hc.trans hrestore.symm

/-- Specialization preserves gate well-formedness. -/
theorem constantControlGate_wellFormed (q : Wire) (g : Gate) (h : g.WellFormed) :
    (constantControlGate q g).WellFormed := by
  cases g with
  | CX c t => by_cases hc : c = q <;> simp_all [constantControlGate,Gate.WellFormed]
  | _ => exact h

/-- The emitted adaptive program is well formed whenever the input is. -/
theorem constantControlProgram_wellFormed (q : Wire) (program : Quantum.AdaptiveCircuit)
    (h : program.WellFormed) : (constantControlProgram q program).WellFormed := by
  induction program with
  | done => trivial
  | unitary circuit next ih =>
      refine ⟨?_,ih h.2⟩
      intro g hg
      obtain ⟨original,hm,rfl⟩ := List.mem_map.mp hg
      exact constantControlGate_wellFormed q original (h.1 original hm)
  | xMeasureReset t onFalse onTrue ihFalse ihTrue => exact ⟨ihFalse h.1,ihTrue h.2⟩

/-- Physical support loses precisely the eliminated control. -/
theorem constantControlGate_wires (q : Wire) (g : Gate)
    (h : constantControlSafe q g) (w : Wire) :
    w ∈ gateWires (constantControlGate q g) ↔ w ∈ gateWires g ∧ w ≠ q := by
  by_cases hw : w = q
  · subst w
    simp [constantControlGate_noControl q g h]
  · cases g with
    | CX c t => by_cases hc : c = q <;> simp [constantControlGate,gateWires,hc,hw]
    | _ => simp [constantControlGate,gateWires,hw]

/-- Physical support of all measurement branches loses precisely the control. -/
theorem constantControlProgram_wires (q : Wire) (program : Quantum.AdaptiveCircuit)
    (h : constantControlProgramSafe q program) (w : Wire) :
    w ∈ (constantControlProgram q program).wires ↔ w ∈ program.wires ∧ w ≠ q := by
  induction program with
  | done => simp [constantControlProgram,Quantum.AdaptiveCircuit.wires]
  | unitary circuit next ih =>
      have hc : w ∈ circuitWires (circuit.map (constantControlGate q)) ↔
          w ∈ circuitWires circuit ∧ w ≠ q := by
        simp only [circuitWires,List.mem_flatMap,List.mem_map]
        constructor
        · rintro ⟨g,⟨g,hg,rfl⟩,hw⟩
          have hh := (constantControlGate_wires q g (h.1 g hg) w).mp hw
          exact ⟨⟨g,hg,hh.1⟩,hh.2⟩
        · rintro ⟨⟨g,hg,hw⟩,hne⟩
          exact ⟨_,⟨g,hg,rfl⟩,(constantControlGate_wires q g (h.1 g hg) w).mpr ⟨hw,hne⟩⟩
      simp only [constantControlProgram,Quantum.AdaptiveCircuit.wires,List.mem_append,hc,ih h.2]
      tauto
  | xMeasureReset t onFalse onTrue ihFalse ihTrue =>
      simp only [constantControlProgram,Quantum.AdaptiveCircuit.wires,List.mem_cons,List.mem_append,
        ihFalse h.2.1,ihTrue h.2.2]
      have ht := h.1
      by_cases hw : w = t
      · subst w; simp [ht]
      · tauto

/-- Specialization does not add or remove measurement/reset events. -/
theorem constantControlProgram_measurements (q : Wire) (program : Quantum.AdaptiveCircuit) :
    (constantControlProgram q program).measurementCount = program.measurementCount := by
  induction program <;> simp_all [constantControlProgram,Quantum.AdaptiveCircuit.measurementCount]

/-- The pass replaces only CNOTs by X, so the coherent T count is unchanged. -/
theorem constantControlProgram_tCount (q : Wire) (program : Quantum.AdaptiveCircuit) :
    (constantControlProgram q program).tCount = program.tCount := by
  have hg (g : Gate) : tCost (constantControlGate q g) = tCost g := by
    cases g with
    | CX c t => by_cases hc : c = q <;> simp [constantControlGate,tCost,hc]
    | _ => rfl
  induction program with
  | done => rfl
  | unitary circuit next ih =>
      simp only [constantControlProgram,Quantum.AdaptiveCircuit.tCount,ih,tCount,List.map_map]
      congr 1
      congr 1
      exact List.map_congr_left (fun g _ => hg g)
  | xMeasureReset t onFalse onTrue ihFalse ihTrue =>
      simp only [constantControlProgram,Quantum.AdaptiveCircuit.tCount,ihFalse,ihTrue]

end ShorECDLP.Paper2607_13816
