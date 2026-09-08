import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout

/-! # Decoder routes stay inside their constructed source windows -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

private theorem route_bounds_of_labels (tree : UnaryActionTree) (k K : Nat)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K) (state : BasisState) :
    k ≤ tree.routeLabel state ∧ tree.routeLabel state ≤ K := by
  have hm := tree.routeLabel_mem_labels state
  rw [← UnaryActionTree.visitLabels_inc, hlabels] at hm
  simp only [zeroMapLabels_eq_range', List.mem_range'] at hm
  omega

/-- Every selected upper leaf lies inside the upper writer's source window, even
when the index bits do not represent a canonical arithmetic state. -/
theorem EndIterationRegisters.upperTree_route_bounds
    (registers : EndIterationRegisters) (windows : EndIterationWindows)
    (hkK : windows.k4 ≤ windows.K4) (state : BasisState) :
    windows.k4 ≤ (registers.upperTree windows).routeLabel state ∧
    (registers.upperTree windows).routeLabel state ≤ windows.K4 :=
  route_bounds_of_labels _ _ _ (registers.upperTree_visitLabels windows hkK) state

/-- Every selected lower leaf lies inside the lower writer's decoder window. -/
theorem EndIterationRegisters.lowerTree_route_bounds
    (registers : EndIterationRegisters) (n : Nat) (windows : EndIterationWindows)
    (hkK : windows.k5 ≤ windows.K5Decode n) (state : BasisState) :
    windows.k5 ≤ (registers.lowerTree n windows).routeLabel state ∧
    (registers.lowerTree n windows).routeLabel state ≤ windows.K5Decode n :=
  route_bounds_of_labels _ _ _ (registers.lowerTree_visitLabels n windows hkK) state

/-- Routing-range validity follows from nonempty construction windows alone.
It does not imply that the selected route equals the intended numeric index. -/
theorem indexedStepRoutesValid_of_windows
    (registers : IndexedStepRegisters) (n T : Nat) (state : BasisState)
    (hupper : (endIterationWindowsAt n T).k4 ≤ (endIterationWindowsAt n T).K4)
    (hlower : (endIterationWindowsAt n T).k5 ≤ (endIterationWindowsAt n T).K5Decode n) :
    IndexedStepRoutesValid registers n T state := by
  unfold IndexedStepRoutesValid indexedStepEndRoutes
  dsimp only
  exact ⟨(EndIterationRegisters.upperTree_route_bounds _ _ hupper _).1,
    (EndIterationRegisters.upperTree_route_bounds _ _ hupper _).2,
    (EndIterationRegisters.lowerTree_route_bounds _ _ _ hlower _).1,
    (EndIterationRegisters.lowerTree_route_bounds _ _ _ hlower _).2⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem production_route_windows : ∀ index : Fin 1620,
    (endIterationWindowsAt 256 (index.val + 1)).k4 ≤
      (endIterationWindowsAt 256 (index.val + 1)).K4 ∧
    (endIterationWindowsAt 256 (index.val + 1)).k5 ≤
      (endIterationWindowsAt 256 (index.val + 1)).K5Decode 256 := by
  decide

/-- Every production decoder route is inside its construction window at every one
of the 1,620 schedule indices, for arbitrary input states. This is a range theorem,
not an arithmetic interpretation or a reachable-state preservation theorem. -/
theorem secp256k1IndexedStepRoutesValid (T : Nat) (hT : 1 ≤ T) (hmax : T ≤ 1620)
    (state : BasisState) :
    IndexedStepRoutesValid indexedStepProductionRegisters 256 T state := by
  have hw := production_route_windows ⟨T - 1, by omega⟩
  have he : T - 1 + 1 = T := by omega
  simp only [he] at hw
  exact indexedStepRoutesValid_of_windows _ _ _ _ hw.1 hw.2

private theorem production_invariant_of_epoch (start count : Nat)
    (hlayout : IndexedScheduleLayout indexedStepProductionRegisters 256 start count)
    (state : BasisState) (hstart : 1 ≤ start) (hstop : start + count ≤ 1621)
    (hready : IndexedStepReady indexedStepProductionRegisters state)
    (hepoch : ∀ offset < count,
      IndexedStepEpochEncoded indexedStepProductionRegisters
        (indexedScheduleState indexedStepProductionRegisters 256 start offset state)) :
    IndexedScheduleInvariant indexedStepProductionRegisters 256 start count state := by
  induction hlayout generalizing state with
  | done start => exact .done _ _ hready
  | @step start count head tail ih =>
    have hroutes := secp256k1IndexedStepRoutesValid start hstart (by omega) state
    have hencoded := hepoch 0 (by omega)
    change IndexedStepEpochEncoded indexedStepProductionRegisters state at hencoded
    have hstep := indexedStepUnitary_correct_routed _ _ _ state head hready hencoded hroutes
    have hnext : IndexedStepReady indexedStepProductionRegisters
        (indexedStepRoutedState indexedStepProductionRegisters 256 start state) := by
      rw [← hstep.1]
      exact hstep.2
    refine .step hready hencoded hroutes (ih _ (by omega) (by omega) hnext ?_)
    intro offset hoffset
    exact hepoch (offset + 1) (by omega)

/-- For the production schedule, the initial scratch premise plus the borrowed-epoch
condition along the direct trace imply the scheduler's full operational invariant.
This isolates the remaining state-dependent obligation; it does not discharge it. -/
theorem secp256k1ScheduleInvariant_of_epochTrace (state : BasisState)
    (hready : IndexedStepReady indexedStepProductionRegisters state)
    (hepoch : ∀ offset < secp256k1ScheduleLength,
      IndexedStepEpochEncoded indexedStepProductionRegisters
        (indexedScheduleState indexedStepProductionRegisters 256 1 offset state)) :
    Secp256k1ScheduleInvariant indexedStepProductionRegisters state := by
  exact production_invariant_of_epoch _ _ secp256k1ScheduleLayout_production state
    (by decide) (by decide) hready hepoch

end
end ShorECDLP.Paper2607_13816
