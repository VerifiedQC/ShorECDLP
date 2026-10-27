import ShorECDLP.Submission.«2607_13816».Challenge.BatchExecution
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] batchStepCircuit batchOpCircuit endpointTranspositionCircuit

theorem batchStep_frame {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (op : BatchOp) (hv : op.Valid) (st : BasisState) (hs : BatchReady base control paths st)
    (w : Wire) (hw : w < base ∨ base+3078 ≤ w) :
    Classical.run (batchStepCircuit (readConstant coeffs Q) rows base tree control paths op) st w = st w := by
  cases op with
  | query sources target =>
    simp only [batchStepCircuit]
    apply batchQuery_frame _ _ _ _ _ _ _ (batchSelection_nodup sources target) hl
      (fun z hz => Or.inl (hd z hz)) st hs.1
    intro p hp i he
    have lo := batchWord_lower base p.2.castSucc i
    have hi := batchWord_bound base p.2.castSucc i
    dsimp [batchFlag] at hi
    dsimp only [Wire] at *
    omega
  | swap source target =>
    simp only [batchStepCircuit]
    apply (batchOpCircuit_model base source target hv.1 hv.2 st hs.2.1 hs.2.2.1).2.2.2
    intro i he
    have lo := batchWord_lower base target i
    have hi := batchWord_bound base target i
    dsimp [batchFlag] at hi
    dsimp only [Wire] at *
    omega

theorem batchUnitary_frame {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (ops : List BatchOp) (hv : ∀ op ∈ ops, op.Valid) (st : BasisState)
    (hs : BatchReady base control paths st) (w : Wire) (hw : w < base ∨ base+3078 ≤ w) :
    Classical.run (batchUnitary (readConstant coeffs Q) rows base tree control paths ops) st w = st w := by
  induction ops generalizing st with
  | nil => rfl
  | cons op ops ih =>
    rw [batchUnitary,Classical.run_append]
    rw [ih (fun o ho => hv o (by simp [ho])) _
      (batchStep_model coeffs Q rows base tree control paths hl hd op (hv op (by simp)) st hs).2.1]
    exact batchStep_frame coeffs Q rows base tree control paths hl hd op (hv op (by simp)) st hs w hw

theorem batchUnitary_fullFrame {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (st : BasisState) (hs : BatchReady base control paths st)
    (hz : ∀ j : Fin 6, j ≠ 5 → st ∘ batchWord base j = fun _ => false)
    (w : Wire) (hw : ∀ i, w ≠ batchWord base 5 i) :
    Classical.run (batchUnitary (readConstant coeffs Q) rows base tree control paths batchSchedule) st w = st w := by
  by_cases hout : w < base ∨ base+3078 ≤ w
  · exact batchUnitary_frame coeffs Q rows base tree control paths hl hd batchSchedule batchSchedule_valid st hs w hout
  · have hb : base ≤ w ∧ w < base+3078 := by dsimp only [Wire] at *; omega
    let j : Fin 6 := ⟨(w-base)/513,by dsimp only [Wire] at *; omega⟩
    let i : Fin 513 := ⟨(w-base)%513,Nat.mod_lt _ (by decide)⟩
    have he : w = batchWord base j i := by
      dsimp [batchWord,j,i]
      have h := Nat.mod_add_div (w-base) 513
      dsimp only [Wire] at *; omega
    have hj : j ≠ 5 := by
      intro h
      exact hw i (he.trans (congrArg (fun k => batchWord base k i) h))
    have ho := (batchUnitary_schedule coeffs Q rows base tree control paths hl hd st hs hz).2.1 j hj
    rw [he]
    exact (congrFun ho i).trans (congrFun (hz j hj) i).symm
end ShorECDLP.Paper2607_13816.ChallengeMigration
