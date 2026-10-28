import ShorECDLP.Submission.«2607_13816».Challenge.ActualPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def historyAfter {s : Nat} (e : Nat) (history : Fin s → Bool) (bits : List Bool) : Fin e → Bool :=
  fun i => (List.ofFn history ++ bits).getD i.val false

theorem historyAfter_nil {s : Nat} (history : Fin s → Bool) : historyAfter s history List.nil = history := by
  funext i
  simp [historyAfter, i.isLt]

theorem historyAfter_cons {s e : Nat} (history : Fin s → Bool) (v : Bool) (bits : List Bool) :
    historyAfter e (Fin.lastCases v history) bits = historyAfter e history (v :: bits) := by
  funext i
  simp only [historyAfter,List.ofFn_succ',Fin.lastCases_castSucc,Fin.lastCases_last,
    List.concat_eq_append,List.append_assoc,List.singleton_append]

/-- Exact ordered branch composition, including the records supplied to the suffix. -/
theorem straight_append_run_history {n s m e : Nat} (p : Straight n s m) (q : Straight n m e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((p.append q).instantiate read history).run =
      (p.instantiate read history).run.flatMap (fun b =>
        (q.instantiate read (historyAfter m history b.history)).run.map (fun c => b.seq c)) := by
  induction p with
  | done =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,List.flatMap_cons,List.flatMap_nil,List.append_nil,historyAfter_nil]
    simp [InstrumentBranch.seq]
  | gate g p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    rfl
  | recordGate i v g p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    rfl
  | measure w p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,List.flatMap_append,Function.comp_def]
    simp only [historyAfter_cons]
    rfl
theorem historyAfter_old {s e : Nat} (history : Fin s → Bool) (bits : List Bool)
    (i : Fin e) (hi : i.val < s) : historyAfter e history bits i = history ⟨i.val,hi⟩ := by
  unfold historyAfter
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [hi]

theorem historyAfter_new {s e : Nat} (history : Fin s → Bool) (bits : List Bool)
    (i : Fin e) (hi : s ≤ i.val) : historyAfter e history bits i = bits.getD (i.val-s) false := by
  unfold historyAfter
  rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
  simp

/-- The Fourier suffix sees the exact new outcomes, not arithmetic-cleanup records. -/
theorem nextBankPrior_map_historyAfter {s : Nat} (count : Nat) (prior : List (Fin s))
    (history : Fin (s+count) → Bool) (bits : List Bool) (hl : bits.length = 16) :
    (nextBankPrior count prior).map (historyAfter (s+count+16) history bits) =
      bits.reverse ++ prior.map (fun i => history ⟨i.val,by omega⟩) := by
  simp only [nextBankPrior,List.map_append,List.map_reverse,List.map_ofFn,List.map_map]
  congr 1
  · congr 1
    have he : List.ofFn (fun i : Fin 16 => bits.getD i.val false) = bits := by
      apply List.ext_getElem
      · simpa using hl.symm
      · intro i hi hj
        simp only [List.getElem_ofFn]
        exact List.getD_eq_getElem _ false hj
    apply Eq.trans _ he
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_def]
    rw [historyAfter_new _ _ _ (by simp)]
    simp
  · apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def]
    exact historyAfter_old _ _ _ (by simpa using Nat.lt_add_right count i.isLt)

/-- The complete ordered instrument of a Fourier bank followed by any straight suffix. -/
theorem fourierProgram_append_run_history {n e : Nat} (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) (q : Straight n (start+ws.length) e)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (((fourierProgram n dir ws start prior).append q).instantiate read history).run =
      (fourierOutcomes ws.length).flatMap (fun bits =>
        (q.instantiate read (historyAfter (start+ws.length) history bits)).run.map
          (fun b => InstrumentBranch.seq ⟨bits,fourierBranch dir ws (prior.map history) bits⟩ b)) := by
  rw [straight_append_run_history,fourierProgram_run,semiclassicalFourier_run,List.flatMap_map]
end ShorECDLP.Paper2607_13816.ChallengeMigration
