import ShorECDLP.Submission.«2607_13816».Challenge.HistoryExecution
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

noncomputable def sourceOuterAxis (wires : List Wire) : List AdaptiveCircuit → List Bool → AdaptiveCircuit
  | [], _ => .done
  | call :: calls, prior => .unitary (wires.reverse.map Gate.H)
      (call.seq (fourierContinue .inverse wires prior (sourceOuterAxis wires calls)))

theorem prepareOuterBank_append_run {n s m e : Nat} (wires : List Wire)
    (p : Straight n s m) (q : Straight n m e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (((prepareOuterBank wires p).append q).instantiate read history).run =
      (AdaptiveCircuit.unitary (wires.map Gate.H) ((p.append q).instantiate read history)).run := by
  induction wires with
  | nil =>
    simp only [prepareOuterBank,List.foldr_nil,List.map_nil,AdaptiveCircuit.run]
    change _ = List.map (fun a => a) _
    rw [List.map_id']
  | cons w ws ih =>
    simp only [prepareOuterBank,List.foldr_cons,Straight.append,Straight.instantiate,
      TemplateGate.instantiate,AdaptiveCircuit.run,List.map_cons]
    rw [show (((ws.foldr (fun w p => Straight.gate (.literal (.H w)) p) p).append q).instantiate read history).run =
      (AdaptiveCircuit.unitary (ws.map Gate.H) ((p.append q).instantiate read history)).run from ih]
    simp only [AdaptiveCircuit.run,List.map_map]
    apply List.map_congr_left
    intro a ha
    cases a
    rfl

theorem bankPrior_map_historyAfter {s : Nat} (count : Nat) (prior : List (Fin s))
    (history : Fin s → Bool) (bits : List Bool) :
    (bankPrior count prior).map (historyAfter (s+count) history bits) = prior.map history := by
  simp only [bankPrior,List.map_map]
  apply List.map_congr_left
  intro i hi
  exact historyAfter_old _ _ _ i.isLt

theorem fourierBank_append_run {n e : Nat} (wires : Vector Wire 16) (start : Nat)
    (prior : List (Fin start)) (q : Straight n (start+16) e)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (((castFinish (by simp) (fourierProgram n .inverse wires.toList start prior)).append q).instantiate read history).run =
      (fourierOutcomes 16).flatMap (fun bits =>
        (q.instantiate read (historyAfter (start+16) history bits)).run.map
          (fun b => InstrumentBranch.seq ⟨bits,fourierBranch .inverse wires.toList (prior.map history) bits⟩ b)) := by
  rw [straight_append_run_history,castFinish_instantiate,fourierProgram_run,semiclassicalFourier_run,List.flatMap_map]
  simp

attribute [local irreducible] fourierProgram prepareOuterBank

theorem outerAxis_run {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n))
    (calls : List AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hc : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) ws calls)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((outerAxis wires ws start prior).instantiate read history).run =
      (sourceOuterAxis wires.toList calls (prior.map history)).run := by
  induction hc generalizing start with
  | nil => rfl
  | @cons w call ws calls hw hws ih =>
    simp only [outerAxis,castFinish_instantiate,prepareOuterBank_append_run,sourceOuterAxis,AdaptiveCircuit.run]
    congr 1
    rw [straight_append_run_history,hw]
    rw [AdaptiveCircuit.run_seq]
    unfold Instrument.seq
    apply List.flatMap_congr
    intro a ha
    rw [fourierBank_append_run]
    simp only [fourierContinue_run,Vector.length_toList]
    congr 1
    apply List.flatMap_congr
    intro bits hb
    rw [ih]
    rw [nextBankPrior_map_historyAfter _ _ _ _ ((fourierOutcomes_mem _ _).mp hb)]
    rw [bankPrior_map_historyAfter]
    have ho : prior.map (fun i => historyAfter (start+w.count) history a.history ⟨i.val,by omega⟩) = prior.map history := by
      apply List.map_congr_left
      intro i hi
      exact historyAfter_old _ _ _ i.isLt
    rw [ho]
noncomputable def sourceOuterRound (wires : List Wire) (left right : List AdaptiveCircuit)
    (reset : List Wire) : AdaptiveCircuit :=
  .unitary [.X 836] ((sourceOuterAxis wires left List.nil).seq
    ((sourceOuterAxis wires right List.nil).seq
      (.unitary [.X 836] (measureResetWithCorrection reset (fun _ => [])))))

theorem outerPlan_round_run {n : Nat} (p : OuterPlan n) (left right : List AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hl : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) p.left.toList left)
    (hr : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) p.right.toList right)
    (start : Nat) (history : Fin start → Bool) :
    ((p.round start).instantiate read history).run = (sourceOuterRound p.wires.toList left right p.reset).run := by
  have htail (cursor : Nat) (history : Fin cursor → Bool) :
      ((Straight.gate (.literal (.X 836)) (resetProgram n cursor p.reset)).instantiate read history).run =
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection p.reset (fun _ => []))).run := by
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.run,resetProgram_run]
  have hright (cursor : Nat) (history : Fin cursor → Bool) :
      (((outerAxis p.wires p.right.toList cursor List.nil).append
        (.gate (.literal (.X 836)) (resetProgram n (cursor+axisCount p.right.toList) p.reset))).instantiate read history).run =
        ((sourceOuterAxis p.wires.toList right List.nil).seq
          (.unitary [.X 836] (measureResetWithCorrection p.reset (fun _ => [])))).run := by
    rw [append_run_fixed _ _ _ _ _ (htail _),AdaptiveCircuit.run_seq,outerAxis_run _ _ _ _ hr]
    simp only [List.map_nil,AdaptiveCircuit.run_seq]
  simp only [OuterPlan.round,castFinish_instantiate,Straight.instantiate,TemplateGate.instantiate,sourceOuterRound,AdaptiveCircuit.run]
  congr 1
  rw [append_run_fixed _ _ _ _ _ (hright _),AdaptiveCircuit.run_seq,outerAxis_run _ _ _ _ hl]
  simp only [List.map_nil,AdaptiveCircuit.run_seq]

theorem outerPlan_repeat_run {n : Nat} (p : OuterPlan n) (source : AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hround : ∀ start history, ((p.round start).instantiate read history).run = source.run)
    (count start : Nat) (history : Fin start → Bool) :
    ((p.repeat count start).instantiate read history).run = (repeatWindowProgram source count).run := by
  induction count generalizing start with
  | zero => simp only [OuterPlan.repeat,castFinish_instantiate,repeatWindowProgram,Straight.instantiate]
  | succ k ih =>
    simp only [OuterPlan.repeat,castFinish_instantiate,repeatWindowProgram]
    rw [append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,hround,← AdaptiveCircuit.run_seq]

end ShorECDLP.Paper2607_13816.ChallengeMigration
