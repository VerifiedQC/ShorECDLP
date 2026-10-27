import ShorECDLP.Submission.«2607_13816».Challenge.BatchQuery
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] endpointTranspositionCircuit
def BatchReady (base control : Wire) (paths : List Wire) (s : BasisState) : Prop :=
  Clean paths s ∧ Clean (batchScratch base) s ∧ s (batchFlag base) = false ∧ s control = true

def BatchOp.Valid : BatchOp → Prop
  | .query _ _ => True
  | .swap source target => source.val ≠ target.val ∧ target ≠ 4

theorem batchSchedule_valid : ∀ op ∈ batchSchedule, op.Valid := by simp [batchSchedule,BatchOp.Valid]

noncomputable def batchStepCircuit {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire) : BatchOp → Circuit
  | .query sources target => unaryActionUnitary .inc
      (fun l q => batchLeafCircuit read (rows l) base q (batchSelection sources target)) tree control paths
  | .swap source target => batchOpCircuit base source target

noncomputable def batchUnitary {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire) : List BatchOp → Circuit
  | [] => []
  | op :: ops => batchStepCircuit read rows base tree control paths op ++ batchUnitary read rows base tree control paths ops

theorem batchWord_lower (base : Wire) (j : Fin 6) (i : Fin 513) : base ≤ batchWord base j i := by
  dsimp [batchWord]; dsimp only [Wire]; omega

theorem batchStep_model {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (op : BatchOp) (hv : op.Valid) (st : BasisState) (hs : BatchReady base control paths st) :
    let out := Classical.run (batchStepCircuit (readConstant coeffs Q) rows base tree control paths op) st
    (∀ j, out ∘ batchWord base j = batchModelStep
      (normalizedEndpointWords coeffs Q (rows (tree.routeLabel st)))
      (fun k => st ∘ batchWord base k) op j) ∧
    BatchReady base control paths out ∧ (∀ w, w < base → out w = st w) := by
  dsimp only
  cases op with
  | query sources target =>
    simp only [batchStepCircuit]
    have hdis : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+2565 ≤ w :=
      fun w hw => Or.inl (hd w hw)
    have hf (w : Wire) (hw : w < base ∨ base+2565 ≤ w) :=
      batchQuery_frame (readConstant coeffs Q) rows base tree control paths _
        (batchSelection_nodup sources target) hl hdis st hs.1 w (by
          intro p hp i h
          have hlow := batchWord_lower base p.2.castSucc i
          have hhigh : batchWord base p.2.castSucc i < base+2565 := by
            dsimp [batchWord]; dsimp only [Wire] at *; omega
          dsimp only [Wire] at *; omega)
    refine ⟨?_,?_,fun w hw => hf w (Or.inl hw)⟩
    · intro j
      exact batchQuery_model coeffs Q rows base tree control paths sources target hl hdis st hs.1 hs.2.2.2 j
    · refine ⟨?_,?_,?_,?_⟩
      · intro w hw
        rw [hf w (Or.inl (hd w (by simp [hw])))]
        exact hs.1 w hw
      · intro w hw
        rw [hf w (Or.inr (by have h := batchScratch_above base w hw; dsimp [batchFlag] at h; dsimp only [Wire] at *; omega))]
        exact hs.2.1 w hw
      · rw [hf (batchFlag base) (Or.inr (by dsimp [batchFlag]; dsimp only [Wire]; omega))]
        exact hs.2.2.1
      · rw [hf control (Or.inl (hd control (by simp)))]
        exact hs.2.2.2
  | swap source target =>
    simp only [batchStepCircuit]
    have h := batchOpCircuit_model base source target hv.1 hv.2 st hs.2.1 hs.2.2.1
    have hf (w : Wire) (hw : w < base) := h.2.2.2 w (by
      intro i he; have := batchWord_lower base target i; dsimp only [Wire] at *; omega)
    refine ⟨h.1,?_,hf⟩
    refine ⟨?_,h.2.1,h.2.2.1,?_⟩
    · intro w hw
      rw [hf w (hd w (by simp [hw]))]
      exact hs.1 w hw
    · rw [hf control (hd control (by simp))]
      exact hs.2.2.2

attribute [local irreducible] batchStepCircuit batchOpCircuit

theorem batchUnitary_model {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (ops : List BatchOp) (hv : ∀ op ∈ ops, op.Valid) (st : BasisState)
    (hs : BatchReady base control paths st) :
    let out := Classical.run (batchUnitary (readConstant coeffs Q) rows base tree control paths ops) st
    (fun j => out ∘ batchWord base j) =
      ops.foldl (batchModelStep (normalizedEndpointWords coeffs Q (rows (tree.routeLabel st))))
        (fun k => st ∘ batchWord base k) ∧
    BatchReady base control paths out ∧ (∀ w, w < base → out w = st w) := by
  induction ops generalizing st with
  | nil => exact ⟨rfl,hs,fun _ _ => rfl⟩
  | cons op ops ih =>
    let mid := Classical.run (batchStepCircuit (readConstant coeffs Q) rows base tree control paths op) st
    have hstep := batchStep_model coeffs Q rows base tree control paths hl hd op (hv op (by simp)) st hs
    have htail := ih (fun q hq => hv q (by simp [hq])) mid hstep.2.1
    have hr : tree.routeLabel mid = tree.routeLabel st := by
      apply UnaryActionTree.routeLabel_congr
      intro w hw
      exact hstep.2.2 w (hd w (by simp [hw]))
    have hrows : (fun j => mid ∘ batchWord base j) =
        batchModelStep (normalizedEndpointWords coeffs Q (rows (tree.routeLabel st)))
          (fun k => st ∘ batchWord base k) op := funext hstep.1
    dsimp only at htail ⊢
    rw [batchUnitary,Classical.run_append]
    refine ⟨?_,htail.2.1,fun w hw => (htail.2.2 w hw).trans (hstep.2.2 w hw)⟩
    simpa only [hr,hrows,List.foldl_cons] using htail.1


theorem batchUnitary_schedule {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (st : BasisState) (hs : BatchReady base control paths st)
    (hzero : ∀ j : Fin 6, j ≠ 5 → st ∘ batchWord base j = fun _ => false) :
    let e := normalizedEndpointWords coeffs Q (rows (tree.routeLabel st))
    let out := Classical.run (batchUnitary (readConstant coeffs Q) rows base tree control paths batchSchedule) st
    (out ∘ batchWord base 5 = runFiniteSwaps
      (finiteMatchingSwaps [(e 0,e 4),(e 1,e 5),(e 2,e 6),(e 3,e 7)]) (st ∘ batchWord base 5)) ∧
    (∀ j : Fin 6, j ≠ 5 → out ∘ batchWord base j = fun _ => false) ∧
    BatchReady base control paths out ∧ (∀ w, w < base → out w = st w) := by
  have h := batchUnitary_model coeffs Q rows base tree control paths hl hd batchSchedule batchSchedule_valid st hs
  have hi : (fun j => st ∘ batchWord base j) = batchInitial (st ∘ batchWord base 5) := by
    funext j
    by_cases hj : j = 5
    · subst j; rfl
    · simpa only [batchInitial,if_neg hj] using hzero j hj
  have hm := h.1
  rw [hi] at hm
  change (fun j => _ ∘ batchWord base j) = batchModel _ _ at hm
  refine ⟨?_,?_,h.2⟩
  · exact (congrFun hm 5).trans (batchModel_data _ _)
  · intro j hj
    exact (congrFun hm j).trans (batchModel_clean _ _ j hj)

/-- The actual fixed gate sequence repairs the coordinate formula on every valid point. -/
theorem batchUnitary_finite {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (st : BasisState) (hs : BatchReady base control paths st)
    (hzero : ∀ j : Fin 6, j ≠ 5 → st ∘ batchWord base j = fun _ => false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs (rows (tree.routeLabel st))) = .some hC) (P : Point)
    (hdata : st ∘ batchWord base 5 = coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P))) :
    Classical.run (batchUnitary (readConstant coeffs Q) rows base tree control paths batchSchedule) st ∘
      batchWord base 5 = coordinateWordBits (fig14PointEncoding (P + .some hC)) := by
  have h := (batchUnitary_schedule coeffs Q rows base tree control paths hl hd st hs hzero).1
  rw [hdata] at h
  exact h.trans (normalizedEndpointWords_correct coeffs Q _ hC hrow P)

/-- The infinity row restores the data word unchanged. -/
theorem batchUnitary_infinity {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (st : BasisState) (hs : BatchReady base control paths st)
    (hzero : ∀ j : Fin 6, j ≠ 5 → st ∘ batchWord base j = fun _ => false)
    (hrow : constantPoint Q (coeffs (rows (tree.routeLabel st))) = 0) :
    Classical.run (batchUnitary (readConstant coeffs Q) rows base tree control paths batchSchedule) st ∘
      batchWord base 5 = st ∘ batchWord base 5 := by
  exact (batchUnitary_schedule coeffs Q rows base tree control paths hl hd st hs hzero).1.trans
    (normalizedEndpointWords_zero_action coeffs Q _ hrow _)
end ShorECDLP.Paper2607_13816.ChallengeMigration
