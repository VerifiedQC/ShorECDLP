import ShorECDLP.Submission.«2607_13816».Challenge.BatchExecution
import ShorECDLP.Submission.«2607_13816».Challenge.MatchingPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] endpointTranspositionCircuit batchOpCircuit

theorem batchQuery_wellFormed {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (selection : List (Fin 8 × Fin 5))
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+2565 ≤ w) :
    (unaryAction .inc (fun l q => batchLeafCircuit read (rows l) base q selection)
      tree control paths).WellFormed := by
  apply unaryAction_wellFormed _ _ _ _ _ hl
  intro l _ q hq g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact tableXorGates_wellFormed q _ (batchRawMask_outside _ _ _ _ _ (hd q hq)) g hg
  · apply tableXorGates_wellFormed q _ ?_ g hg
    split
    · exact batchTags_outside _ _ _ (hd q hq)
    · simp

theorem batchSource_wellFormed {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+2565 ≤ w)
    (ops : List BatchOp) (hv : ∀ op ∈ ops, op.Valid) :
    (batchSource read rows base tree control paths ops).WellFormed := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    have ht := ih (fun o ho => hv o (by simp [ho]))
    have h := hv op (by simp)
    cases op with
    | query sources target =>
      exact (batchQuery_wellFormed read rows base tree control paths _ hl hd).seq ht
    | swap source target =>
      refine ⟨?_,ht⟩
      unfold batchOpCircuit
      exact endpointTransposition_wellFormed _ _ _ _ _ (batchSwap_geometry base source target h.1 h.2)
end ShorECDLP.Paper2607_13816.ChallengeMigration
