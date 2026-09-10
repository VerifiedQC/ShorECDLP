import ShorECDLP.Framework.Quantum.CoherentRefinement
/-!
# Physical wire relabeling for adaptive circuits

A bijection changes the labels on gates and measure/reset nodes, while keeping
classical transcripts and normalized branch coefficients unchanged. This lets
an arithmetic composition reuse a different clean register bank without adding
swap gates. The transformation preserves physical well-formedness and resource
counts for the same transformed program.
-/

namespace ShorECDLP
noncomputable section

def Gate.relabel (e : Wire ≃ Wire) : Gate → Gate
  | .X t => .X (e t)
  | .H t => .H (e t)
  | .CX c t => .CX (e c) (e t)
  | .CCX a b t => .CCX (e a) (e b) (e t)
  | .P d k t => .P d k (e t)

namespace Quantum

def relabelBasis (e : Wire ≃ Wire) (s : BasisState) : BasisState := fun w => s (e.symm w)
def relabelState (e : Wire ≃ Wire) : State →ₗ[ℂ] State := Finsupp.lmapDomain ℂ ℂ (relabelBasis e)

@[simp] theorem relabelState_ket (e : Wire ≃ Wire) (s : BasisState) :
    relabelState e (ket s) = ket (relabelBasis e s) := by
  simp [relabelState,ket,Finsupp.lmapDomain_apply]

@[simp] theorem relabelBasis_at (e : Wire ≃ Wire) (s : BasisState) (w : Wire) :
    relabelBasis e s (e w) = s w := by simp [relabelBasis]

@[simp] theorem relabelBasis_upd (e : Wire ≃ Wire) (s : BasisState) (w : Wire) (b : Bool) :
    relabelBasis e (s[w ↦ b]) = (relabelBasis e s)[e w ↦ b] := by
  funext v
  by_cases h : v = e w
  · subst v; simp [relabelBasis,upd]
  · have hv : e.symm v ≠ w := by intro he; apply h; rw [← he]; simp
    simp [relabelBasis,upd,h,hv]

theorem applyGate_relabel (e : Wire ≃ Wire) (g : Gate) (psi : State) :
    applyGate (g.relabel e) (relabelState e psi) = relabelState e (applyGate g psi) := by
  induction psi using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | single s c =>
    have h : Finsupp.single s c = c • ket s := by simp [ket]
    rw [h]
    simp only [map_smul,relabelState_ket]
    congr 1
    cases g with
    | H t => cases hst : s t <;> simp [Gate.relabel,applyGate_ket,onKet,hst]
    | P d k t => cases hst : s t <;> simp [Gate.relabel,applyGate_ket,onKet,hst]
    | _ => simp [Gate.relabel,applyGate_ket,onKet]

theorem run_relabel (e : Wire ≃ Wire) (c : Circuit) (psi : State) :
    run (c.map (Gate.relabel e)) (relabelState e psi) = relabelState e (run c psi) := by
  induction c generalizing psi with
  | nil => rfl
  | cons g c ih => simp only [List.map_cons,run_cons,applyGate_relabel,ih]

theorem xResetKraus_relabel (e : Wire ≃ Wire) (t : Wire) (b : Bool) (psi : State) :
    xResetKraus (e t) b (relabelState e psi) = relabelState e (xResetKraus t b psi) := by
  induction psi using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | single s c =>
    have h : Finsupp.single s c = c • ket s := by simp [ket]
    rw [h]
    simp only [map_smul,relabelState_ket,xResetKraus_ket,relabelBasis_at,relabelBasis_upd]

@[simp] theorem relabelBasis_symm (e : Wire ≃ Wire) (s : BasisState) :
    relabelBasis e.symm (relabelBasis e s) = s := by funext w; simp [relabelBasis]

@[simp] theorem relabelState_symm (e : Wire ≃ Wire) (psi : State) :
    relabelState e.symm (relabelState e psi) = psi := by
  induction psi using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | single s c =>
    have h : Finsupp.single s c = c • ket s := by simp [ket]
    rw [h]
    simp

@[simp] theorem relabelState_symm_right (e : Wire ≃ Wire) (psi : State) :
    relabelState e (relabelState e.symm psi) = psi := by
  simpa only [Equiv.symm_symm] using relabelState_symm e.symm psi

def InstrumentBranch.relabel (e : Wire ≃ Wire) (b : InstrumentBranch) : InstrumentBranch where
  history := b.history
  kraus := (relabelState e).comp (b.kraus.comp (relabelState e.symm))

def AdaptiveCircuit.relabel (e : Wire ≃ Wire) : AdaptiveCircuit → AdaptiveCircuit
  | .done => .done
  | .unitary c p => .unitary (c.map (Gate.relabel e)) (p.relabel e)
  | .xMeasureReset t p q => .xMeasureReset (e t) (p.relabel e) (q.relabel e)

theorem AdaptiveCircuit.run_relabel (e : Wire ≃ Wire) (p : AdaptiveCircuit) :
    (p.relabel e).run = p.run.map (InstrumentBranch.relabel e) := by
  induction p with
  | done =>
    simp only [relabel,run,List.map_cons,List.map_nil]
    congr 2
    apply LinearMap.ext
    intro psi
    apply Finsupp.ext; intro s
    change psi s = (relabelState e (relabelState e.symm psi)) s
    rw [relabelState_symm_right]
  | unitary c p ih =>
    simp only [relabel,run,ih,List.map_map]
    congr 1
    funext b
    apply congrArg (InstrumentBranch.mk b.history)
    apply LinearMap.ext
    intro psi
    apply Finsupp.ext; intro s
    change (relabelState e (b.kraus (relabelState e.symm
      (Quantum.run (c.map (Gate.relabel e)) psi)))) s =
      (relabelState e (b.kraus (Quantum.run c (relabelState e.symm psi)))) s
    have h := Quantum.run_relabel e c (relabelState e.symm psi)
    rw [relabelState_symm_right] at h
    rw [h,relabelState_symm]
  | xMeasureReset t p q ihp ihq =>
    simp only [relabel,run,ihp,ihq,List.map_append,List.map_map]
    congr 1 <;> congr 1 <;> funext b <;>
      apply congrArg (InstrumentBranch.mk _) <;> apply LinearMap.ext <;> intro psi <;> apply Finsupp.ext <;> intro s
    · change (relabelState e (b.kraus (relabelState e.symm (xResetKraus (e t) false psi)))) s =
        (relabelState e (b.kraus (xResetKraus t false (relabelState e.symm psi)))) s
      have h := xResetKraus_relabel e t false (relabelState e.symm psi)
      rw [relabelState_symm_right] at h
      rw [h,relabelState_symm]
    · change (relabelState e (b.kraus (relabelState e.symm (xResetKraus (e t) true psi)))) s =
        (relabelState e (b.kraus (xResetKraus t true (relabelState e.symm psi)))) s
      have h := xResetKraus_relabel e t true (relabelState e.symm psi)
      rw [relabelState_symm_right] at h
      rw [h,relabelState_symm]


/-- Relabeling transports the same normalized branch coefficients. -/
theorem CoherentlyImplementsOn.relabel
    {program : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State} {Valid : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) (e : Wire ≃ Wire) :
    CoherentlyImplementsOn (program.relabel e)
      ((relabelState e).comp (ideal.comp (relabelState e.symm)))
      (fun s => Valid (relabelBasis e.symm s)) := by
  obtain ⟨coefficients,hbranches,hnorm⟩ := h
  refine ⟨coefficients,?_,hnorm⟩
  rw [AdaptiveCircuit.run_relabel]
  generalize he : program.run = branches at hbranches ⊢
  clear he hnorm
  induction hbranches with
  | nil => exact .nil
  | @cons b c bs cs hb hbs ih =>
    refine .cons ?_ ih
    intro s hs
    change relabelState e (b.kraus (relabelState e.symm (ket s))) =
      c • relabelState e (ideal (relabelState e.symm (ket s)))
    rw [relabelState_ket,hb _ hs,map_smul]

@[simp] theorem AdaptiveCircuit.relabel_seq (e : Wire ≃ Wire) (p q : AdaptiveCircuit) :
    (p.seq q).relabel e = (p.relabel e).seq (q.relabel e) := by
  induction p with
  | done => rfl
  | unitary c p ih => simp [seq,relabel,ih]
  | xMeasureReset t p q ihp ihq => simp [seq,relabel,ihp,ihq]

@[simp] theorem AdaptiveCircuit.relabel_wellFormed (e : Wire ≃ Wire) (p : AdaptiveCircuit) :
    (p.relabel e).WellFormed ↔ p.WellFormed := by
  have hg (g : Gate) : (g.relabel e).WellFormed ↔ g.WellFormed := by
    cases g <;> simp [Gate.relabel,Gate.WellFormed,e.injective.eq_iff]
  have hc (c : Circuit) : CircuitWellFormed (c.map (Gate.relabel e)) ↔ CircuitWellFormed c := by
    simp only [CircuitWellFormed,List.mem_map]
    constructor
    · intro h g hm; exact (hg g).1 (h _ ⟨g,hm,rfl⟩)
    · intro h g hm; obtain ⟨g,hm,rfl⟩ := hm; exact (hg g).2 (h g hm)
  induction p with
  | done => rfl
  | unitary c p ih => simp only [relabel,WellFormed,hc,ih]
  | xMeasureReset t p q ihp ihq => simp only [relabel,WellFormed,ihp,ihq]

@[simp] theorem AdaptiveCircuit.relabel_tCount (e : Wire ≃ Wire) (p : AdaptiveCircuit) :
    (p.relabel e).tCount = p.tCount := by
  have hc (c : Circuit) : ShorECDLP.tCount (c.map (Gate.relabel e)) = ShorECDLP.tCount c := by
    induction c with
    | nil => rfl
    | cons g c ih => cases g <;> simp [Gate.relabel,ShorECDLP.tCount_cons,tCost,ih]
  induction p with
  | done => rfl
  | unitary c p ih => simp only [relabel,tCount,hc,ih]
  | xMeasureReset t p q ihp ihq => simp only [relabel,tCount,ihp,ihq]

@[simp] theorem AdaptiveCircuit.relabel_measurementCount (e : Wire ≃ Wire) (p : AdaptiveCircuit) :
    (p.relabel e).measurementCount = p.measurementCount := by
  induction p with
  | done => rfl
  | unitary c p ih => exact ih
  | xMeasureReset t p q ihp ihq => simp only [relabel,measurementCount,ihp,ihq]


@[simp] theorem AdaptiveCircuit.relabel_wires (e : Wire ≃ Wire) (p : AdaptiveCircuit) :
    (p.relabel e).wires = p.wires.map e := by
  have hg (g : Gate) : gateWires (g.relabel e) = (gateWires g).map e := by
    cases g <;> rfl
  have hc (c : Circuit) : circuitWires (c.map (Gate.relabel e)) = (circuitWires c).map e := by
    induction c with
    | nil => rfl
    | cons g c ih => simpa only [List.map_cons,circuitWires,List.flatMap_cons,List.map_append,hg] using congrArg ((gateWires g).map e ++ ·) ih
  induction p with
  | done => rfl
  | unitary c p ih => simp only [relabel,wires,hc,ih,List.map_append]
  | xMeasureReset t p q ihp ihq => simp only [relabel,wires,ihp,ihq,List.map_cons,List.map_append]

@[simp] theorem AdaptiveCircuit.relabel_qubitCount (e : Wire ≃ Wire) (p : AdaptiveCircuit) :
    (p.relabel e).qubitCount = p.qubitCount := by
  simp only [qubitCount,relabel_wires,List.dedup_map_of_injective e.injective,List.length_map]

end Quantum
end
end ShorECDLP
