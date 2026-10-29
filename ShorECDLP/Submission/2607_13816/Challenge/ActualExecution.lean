import ShorECDLP.Submission.«2607_13816».Challenge.OuterExecution
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

noncomputable def actualFirstSource (Q : Point) : AdaptiveCircuit :=
  physicalPointLookup (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
    ((2^(16*15)) • G))
noncomputable def actualOddSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide))
noncomputable def actualLeftSources (Q : Point) : List AdaptiveCircuit :=
  actualFirstSource Q :: List.ofFn (fun k : Fin 15 => actualOddSource Q (.left ⟨14-k.val,by omega⟩))
noncomputable def actualRightSources (Q : Point) : List AdaptiveCircuit :=
  List.ofFn (fun k : Fin 13 => actualOddSource Q (.right ⟨12-k.val,by omega⟩))
noncomputable def actualRoundSource (Q : Point) : AdaptiveCircuit :=
  sourceOuterRound streamAddress.reverse (actualLeftSources Q) (actualRightSources Q) batchedResetWires

private theorem forall₂_ofFn {α β : Type} (R : α → β → Prop) {n : Nat}
    (a : Fin n → α) (b : Fin n → β) (h : ∀ i, R (a i) (b i)) : List.Forall₂ R (List.ofFn a) (List.ofFn b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih _ _ (fun i => h i.succ))

theorem actualLeftSources_run (Q : Point) (hQ : order • Q=0) :
    List.Forall₂ (fun w c => ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).run = c.run)
      actualLeftWindows (actualLeftSources Q) := by
  apply List.Forall₂.cons
  · exact fun start history => actualFirstWindow_run start Q hQ history
  · apply forall₂_ofFn
    intro k start history
    exact actualBatchedWindow_run _ start Q hQ history

theorem actualRightSources_run (Q : Point) (hQ : order • Q=0) :
    List.Forall₂ (fun w c => ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).run = c.run)
      actualRightWindows (actualRightSources Q) := by
  apply forall₂_ofFn
  intro k start history
  exact actualBatchedWindow_run _ start Q hQ history

attribute [local irreducible] actualLeftWindows actualRightWindows actualLeftSources actualRightSources

theorem batchedOuterPlan_round_run (Q : Point) (hQ : order • Q=0) (start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run =
      (actualRoundSource Q).run := by
  exact outerPlan_round_run batchedOuterPlan _ _ _ (actualLeftSources_run Q hQ) (actualRightSources_run Q hQ) start history

attribute [local irreducible] batchedOuterPlan actualRoundSource

theorem batchedOuterPlan_repeat_run (Q : Point) (hQ : order • Q=0) (count start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run =
      (repeatWindowProgram (actualRoundSource Q) count).run :=
  outerPlan_repeat_run _ _ _ (batchedOuterPlan_round_run Q hQ) count start history

end ShorECDLP.Paper2607_13816.ChallengeMigration
