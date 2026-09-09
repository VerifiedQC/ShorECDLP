import ShorECDLP.Submission.«2607_13816».EEA.DualLogical
import ShorECDLP.Submission.«2607_13816».EEA.DualRouting

/-! # Routed endpoint pulses in a synchronized scan -/
namespace ShorECDLP.Paper2607_13816
open Classical

private def pulses (order : UnaryOrder) : DualUnaryActionTree → Bool → Bool → BasisState → List (Nat × Bool × Bool)
  | .leaf label, a, b, _ => [(label,a,b)]
  | .node ia ib zero one, a, b, route =>
    let z := pulses order zero (a && !route ia) (b && !route ib) route
    let o := pulses order one (a && route ia) (b && route ib) route
    match order with
    | .inc => z ++ o
    | .dec => o ++ z

private theorem project_visits (tree : DualUnaryActionTree) (order : UnaryOrder) (second : Bool) :
    (tree.project second).visitLabels order = tree.visitLabels order := by
  induction tree with
  | leaf => rfl
  | node ia ib zero one ihz iho =>
    cases order <;> simp only [DualUnaryActionTree.project, UnaryActionTree.visitLabels,
      DualUnaryActionTree.visitLabels, ihz, iho]

private theorem pulses_project (tree : DualUnaryActionTree) (order : UnaryOrder)
    (a b second : Bool) (route : BasisState) :
    (pulses order tree a b route).map (fun p => (p.1, if second then p.2.2 else p.2.1)) =
      (tree.project second).visitPulses order (if second then b else a) route := by
  induction tree generalizing a b with
  | leaf => cases second <;> rfl
  | node ia ib zero one ihz iho =>
    have hz := ihz (a && !route ia) (b && !route ib)
    have ho := iho (a && route ia) (b && route ib)
    cases order <;> cases second <;>
      simp only [Bool.false_eq_true, if_false, if_true] at hz ho ⊢ <;>
      simp only [pulses, DualUnaryActionTree.project, UnaryActionTree.visitPulses,
        List.map_append, Bool.false_eq_true, if_false, if_true] <;> rw [hz, ho]

private theorem pulse_ext (xs ys : List (Nat × Bool × Bool))
    (ha : xs.map (fun p => (p.1,p.2.1)) = ys.map (fun p => (p.1,p.2.1)))
    (hb : xs.map (fun p => (p.1,p.2.2)) = ys.map (fun p => (p.1,p.2.2))) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at ha
  | cons x xs ih =>
    cases ys with
    | nil => simp at ha
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at ha hb
      have hxy : x=y := Prod.ext ha.1.1 (Prod.ext ha.1.2 hb.1.2)
      rw [hxy]
      exact congrArg (List.cons y) (ih ys ha.2 hb.2)

private theorem pulses_routes (tree : DualUnaryActionTree) (order : UnaryOrder)
    (a b : Bool) (route : BasisState) (hnd : tree.labels.Nodup) :
    pulses order tree a b route = (tree.visitLabels order).map (fun label =>
      (label, a && decide (label = (tree.project false).routeLabel route),
        b && decide (label = (tree.project true).routeLabel route))) := by
  have hn (second : Bool) : (tree.project second).labels.Nodup := by
    have hh := project_visits tree .inc second
    simp only [UnaryActionTree.visitLabels_inc, DualUnaryActionTree.visitLabels_inc] at hh
    rw [hh]
    exact hnd
  apply pulse_ext
  · have hh := pulses_project tree order a b false route
    simp only [Bool.false_eq_true, if_false] at hh
    rw [UnaryActionTree.visitPulses_eq_route order _ a route (hn false), project_visits] at hh
    simpa only [Bool.false_eq_true, if_false, List.map_map, Function.comp_apply] using hh
  · have hh := pulses_project tree order a b true route
    simp only [if_true] at hh
    rw [UnaryActionTree.visitPulses_eq_route order _ b route (hn true), project_visits] at hh
    simpa only [if_true, List.map_map, Function.comp_apply] using hh

private theorem logical_fold (tree : DualUnaryActionTree) (order : UnaryOrder)
    (leaf : Nat → Bool → Bool → BasisState → BasisState) (a b : Bool) (route state : BasisState) :
    tree.runLogicalTree order leaf a b route state =
      (pulses order tree a b route).foldl (fun s p => leaf p.1 p.2.1 p.2.2 s) state := by
  induction tree generalizing a b state with
  | leaf => rfl
  | node ia ib zero one ihz iho =>
    cases order <;> simp only [DualUnaryActionTree.runLogicalTree, pulses, List.foldl_append]
    · rw [iho, ihz]
    · rw [ihz, iho]

/-- The synchronized logical execution is an ordered scan with one equality pulse per bank. -/
theorem DualUnaryActionTree.runLogicalTree_eq_fold_routes
    (tree : DualUnaryActionTree) (order : UnaryOrder)
    (leaf : Nat → Bool → Bool → BasisState → BasisState) (a b : Bool) (route state : BasisState)
    (hnd : tree.labels.Nodup) :
    tree.runLogicalTree order leaf a b route state =
      (tree.visitLabels order).foldl (fun s label =>
        leaf label (a && decide (label = (tree.project false).routeLabel route))
          (b && decide (label = (tree.project true).routeLabel route)) s) state := by
  rw [logical_fold, pulses_routes tree order a b route hnd, List.foldl_map]

/-- The same physical circuit executes the routed-label fold and restores its decoder interface. -/
theorem run_dualUnaryActionUnitary_as_routedFold
    (order : UnaryOrder) (leaf : Nat → Wire → Wire → Circuit)
    (logicalLeaf : Nat → Bool → Bool → BasisState → BasisState)
    (tree : DualUnaryActionTree) (ca cb : Wire) (pa pb dynamicWires protectedWires cleanWires : List Wire)
    (state : BasisState) (hnodup : tree.labels.Nodup) (hlayout : tree.Layout ca cb pa pb)
    (hleaf : DualUnaryLeafPreservesOn leaf tree.labels dynamicWires protectedWires)
    (hlogical : ∀ label ∈ tree.labels, ∀ a b, a ∈ dynamicWires → b ∈ dynamicWires →
      ∀ s t, Clean cleanWires s → AgreesOutside protectedWires s t →
        AgreesOutside protectedWires (run (leaf label a b) s)
          (logicalLeaf label (s a) (s b) t))
    (hlogicalPreserves : ∀ label ∈ tree.labels, ∀ a b state wire, wire ∈ protectedWires →
      logicalLeaf label a b state wire = state wire)
    (hroles : ∀ w ∈ tree.decoderWires ca cb pa pb, w ∈ protectedWires)
    (hdynamic : ∀ w ∈ tree.decoderWires ca cb pa pb, w ∈ dynamicWires)
    (hsubset : ∀ w ∈ dynamicWires, w ∈ protectedWires)
    (hcleanA : Clean pa state) (hcleanB : Clean pb state)
    (hworkRoles : ∀ w ∈ cleanWires, w ∈ protectedWires)
    (hworkPaths : ∀ w ∈ cleanWires, w ∉ pa ++ pb)
    (hworkClean : Clean cleanWires state) :
    run (dualUnaryActionUnitary order leaf tree ca cb pa pb) state =
      (tree.visitLabels order).foldl (fun s label =>
        logicalLeaf label (state ca && decide (label = (tree.project false).routeLabel state))
          (state cb && decide (label = (tree.project true).routeLabel state)) s) state := by
  rw [run_dualUnaryActionUnitary_as_runLogicalTree order leaf logicalLeaf tree ca cb pa pb
    dynamicWires protectedWires cleanWires state hlayout hleaf hlogical hlogicalPreserves hroles hdynamic hsubset hcleanA hcleanB
    hworkRoles hworkPaths hworkClean]
  exact tree.runLogicalTree_eq_fold_routes order logicalLeaf (state ca) (state cb) state state hnodup

end ShorECDLP.Paper2607_13816
