import ShorECDLP.Submission.«2607_13816».Challenge.LookupPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.BatchPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.PlacedBatch
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] batchOpCircuit endpointTranspositionCircuit

theorem endpointSelectGates_wellFormed {n : Nat} (control : Wire) (ports : List (Wire × EndpointBit n))
    (h : ∀ p ∈ ports, control ≠ p.1) : ∀ g ∈ endpointSelectGates control ports, g.WellFormed := by
  intro g hg
  obtain ⟨⟨w,b⟩,hp,hg⟩ := List.mem_flatMap.mp hg
  have hn := h (w,b) hp
  cases b with
  | inl b =>
    cases b with
    | false => simp [endpointSelectGate] at hg
    | true =>
      simp only [endpointSelectGate,List.mem_singleton] at hg
      subst g; exact hn
  | inr r =>
    simp only [endpointSelectGate,List.mem_singleton] at hg
    subst g
    exact hn

theorem batchLeaf_wellFormed {n : Nat} (row : Fin n) (base control : Wire)
    (selection : List (Fin 8 × Fin 5)) (hc : control < base) :
    ∀ g ∈ batchLeaf row base control selection, g.WellFormed := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · apply endpointSelectGates_wellFormed control _ ?_ g hg
    intro p hp he
    have hb := (batchPorts_bounds row base p.1 selection (List.mem_map.mpr ⟨p,hp,rfl⟩)).1
    dsimp only [Wire] at *; omega
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
    change control ≠ w
    have hb := (batchTags_bounds base w selection hw).1
    dsimp only [Wire] at *; omega

theorem batchOps_physical {n : Nat} (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::paths, w < base)
    (ops : List BatchOp) (hv : ∀ op ∈ ops, op.Valid) :
    ∀ op ∈ batchOps rows base tree control paths ops, op.Physical := by
  induction ops with
  | nil => intro op ho; cases ho
  | cons op ops ih =>
    have ht := ih (fun o ho => hv o (by simp [ho]))
    have hop := hv op (by simp)
    cases op with
    | query sources target =>
      rw [batchOps,List.forall_mem_append]
      exact ⟨unaryLookupOps_physical _ _ _ _ hl (fun l c hc => batchLeaf_wellFormed _ _ _ _ (hd c hc)),ht⟩
    | swap source target =>
      simp only [batchOps,List.forall_mem_cons]
      refine ⟨ordinaryOp_physical _ ?_,ht⟩
      unfold batchOpCircuit
      exact endpointTransposition_wellFormed _ _ _ _ _ (batchSwap_geometry base source target hop.1 hop.2)

theorem batchedEndpointProgram_wellFormed {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::paths, w < base) (start : Nat) :
    (batchedEndpointProgram rows base tree control paths start).2.WellFormed :=
  lookupProgram_wellFormed _ (batchOps_physical _ _ _ _ _ hl hd _ batchSchedule_valid) start

theorem relabelStraight_wellFormed {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    (relabelStraight e p).WellFormed ↔ p.WellFormed := by
  have hg (g : Gate) : (g.relabel e).WellFormed ↔ g.WellFormed := by
    cases g <;> simp [Gate.relabel,Gate.WellFormed,e.injective.eq_iff]
  have ht (g : TemplateGate n) : (relabelTemplateGate e g).WellFormed ↔ g.WellFormed := by
    cases g <;> simp only [relabelTemplateGate,TemplateGate.WellFormed,hg]
  induction p with
  | done => rfl
  | gate g p ih => simp only [relabelStraight,Straight.WellFormed,ht,ih]
  | recordGate i v g p ih => simp only [relabelStraight,Straight.WellFormed,hg,ih]
  | measure w p ih => exact ih


theorem relabelCompiled_wellFormed {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) :
    (relabelCompiled e p).2.WellFormed ↔ p.2.WellFormed :=
  relabelStraight_wellFormed e p.2


attribute [local irreducible] batchedEndpointProgram

theorem placedBatchProgram_wellFormed (w : OddWindow) (start : Nat) :
    (placedBatchProgram w start).2.WellFormed := by
  have hd : ∀ z ∈ 836::pointLookupPath, z < 1024 := by decide
  exact (relabelCompiled_wellFormed batchPlacement
    (batchedEndpointProgram (batchWindowRows w) 1024 batchWindowTree 836 pointLookupPath start)).mpr
    (batchedEndpointProgram_wellFormed _ _ _ _ _ batchWindowTree_layout hd start)
end ShorECDLP.Paper2607_13816.ChallengeMigration
