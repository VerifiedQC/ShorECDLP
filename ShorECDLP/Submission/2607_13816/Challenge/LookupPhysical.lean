import ShorECDLP.Submission.«2607_13816».Challenge.BatchCoherent
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge

def LookupOp.Physical {n : Nat} : LookupOp n → Prop
  | .gates gs => ∀ g ∈ gs, g.WellFormed
  | .erase a b _ => a ≠ b

theorem recordGates_wellFormed {n s e : Nat} (i : Fin s) (gs : Circuit) (next : Straight n s e)
    (hg : CircuitWellFormed gs) (hn : next.WellFormed) : (recordGates i gs next).WellFormed := by
  induction gs with
  | nil => exact hn
  | cons g gs ih => exact ⟨hg g (by simp),ih (fun g h => hg g (by simp [h]))⟩

theorem andEraseProgram_wellFormed (n start : Nat) (a b t : Wire) (h : a ≠ b) :
    (andEraseProgram n start a b t).WellFormed := by
  apply recordGates_wellFormed
  · simp [CircuitWellFormed,controlledZ,Gate.WellFormed,h]
  · trivial

theorem lookupProgram_wellFormed {n : Nat} (ops : List (LookupOp n))
    (h : ∀ op ∈ ops, op.Physical) (start : Nat) : (lookupProgram n ops start).WellFormed := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    have ho := h op (by simp)
    have ht := ih (fun o hm => h o (by simp [hm]))
    cases op with
    | gates gs => exact straight_append_wellFormed _ _ (gateProgram_wellFormed gs ho) (ht start)
    | erase a b t =>
      simp only [lookupProgram,castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (andEraseProgram_wellFormed n start a b t ho) (ht (start+1))

theorem ordinaryOp_physical {n : Nat} (gs : Circuit) (h : CircuitWellFormed gs) :
    (@ordinaryOp n gs).Physical := by
  intro g hg
  change g ∈ gs.map TemplateGate.literal at hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  exact h a ha

theorem unaryLookupOps_physical {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire) (hl : tree.Layout q paths)
    (hleaf : ∀ l c, c ∈ q::paths → ∀ g ∈ leaf l c, g.WellFormed) :
    ∀ op ∈ unaryLookupOps leaf tree q paths, op.Physical := by
  induction hl with
  | leaf l q paths hn => simpa only [unaryLookupOps,List.forall_mem_singleton] using hleaf l q (by simp)
  | node bit q path zero one rest hn hz ho ihz iho =>
    have hhead := (List.nodup_cons.mp hn).1
    have hcross := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
    have hbit : bit ∈ (UnaryActionTree.node bit zero one).indexWires.dedup := by
      simp [UnaryActionTree.indexWires]
    have hqb : q ≠ bit := by intro he; apply hhead; rw [he]; simp [hbit]
    have hqp : q ≠ path := by intro he; apply hhead; rw [he]; simp
    have hbp : bit ≠ path := by
      intro he
      exact hcross bit hbit path (by simp) he
    have hleaf' : ∀ l c, c ∈ path::rest → ∀ g ∈ leaf l c, g.WellFormed :=
      fun l c hc => hleaf l c (by simp [hc])
    have hx := ihz hleaf'
    have hy := iho hleaf'
    have hc : (@ordinaryOp n (computeZeroAnd q bit path)).Physical :=
      ordinaryOp_physical _ (by simp [computeZeroAnd,CircuitWellFormed,Gate.WellFormed,hqb,hqp,hbp])
    have hcx : (@ordinaryOp n ([Gate.CX q path])).Physical :=
      ordinaryOp_physical _ (by simp [CircuitWellFormed,Gate.WellFormed,hqp])
    have hxb : (@ordinaryOp n ([Gate.X bit])).Physical :=
      ordinaryOp_physical _ (by simp [CircuitWellFormed,Gate.WellFormed])
    simp only [unaryLookupOps,List.forall_mem_append,List.forall_mem_cons,List.mem_nil_iff,false_implies]
    exact ⟨⟨⟨⟨⟨hc,fun _ => trivial⟩,hx⟩,⟨hcx,fun _ => trivial⟩⟩,hy⟩,hcx,hxb,hqb,hxb,fun _ => trivial⟩
end ShorECDLP.Paper2607_13816.ChallengeMigration
