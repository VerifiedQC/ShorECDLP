import ShorECDLP.Submission.«2607_13816».EEA.DualUnaryAction

/-! # Logical execution of synchronized decoder traversals -/
namespace ShorECDLP.Paper2607_13816
open Classical

/-- Source-ordered leaf execution with two Boolean decoder pulses and frozen index bits. -/
def DualUnaryActionTree.runLogicalTree
    (order : UnaryOrder) (leaf : Nat → Bool → Bool → BasisState → BasisState) :
    DualUnaryActionTree → Bool → Bool → BasisState → BasisState → BasisState
  | .leaf label, a, b, _, state => leaf label a b state
  | .node ia ib zero one, a, b, route, state =>
    let za := a && !route ia
    let zb := b && !route ib
    let oa := a && route ia
    let ob := b && route ib
    match order with
    | .inc => one.runLogicalTree order leaf oa ob route
        (zero.runLogicalTree order leaf za zb route state)
    | .dec => zero.runLogicalTree order leaf za zb route
        (one.runLogicalTree order leaf oa ob route state)

private theorem logical_preserves
    (order : UnaryOrder) (leaf : Nat → Bool → Bool → BasisState → BasisState)
    (tree : DualUnaryActionTree) (a b : Bool) (route state : BasisState) (protectedWires : List Wire)
    (h : ∀ label ∈ tree.labels, ∀ a b state wire, wire ∈ protectedWires →
      leaf label a b state wire = state wire) :
    ∀ wire ∈ protectedWires, tree.runLogicalTree order leaf a b route state wire = state wire := by
  induction tree generalizing a b state with
  | leaf label => exact h label (by simp [DualUnaryActionTree.labels]) a b state
  | node ia ib zero one ihz iho =>
    have hz : ∀ label ∈ zero.labels, ∀ a b state wire, wire ∈ protectedWires →
        leaf label a b state wire = state wire := by
      intro label hl
      exact h label (by simp [DualUnaryActionTree.labels, hl])
    have ho : ∀ label ∈ one.labels, ∀ a b state wire, wire ∈ protectedWires →
        leaf label a b state wire = state wire := by
      intro label hl
      exact h label (by simp [DualUnaryActionTree.labels, hl])
    intro wire hw
    cases order <;> simp only [DualUnaryActionTree.runLogicalTree]
    · rw [iho _ _ _ ho wire hw, ihz _ _ _ hz wire hw]
    · rw [ihz _ _ _ hz wire hw, iho _ _ _ ho wire hw]

private theorem physical_preserves
    (order : UnaryOrder) (leaf : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (ca cb : Wire) (pa pb protectedWires : List Wire) (state : BasisState)
    (hlayout : tree.Layout ca cb pa pb)
    (hleaf : DualUnaryLeafPreservesOn leaf tree.labels protectedWires protectedWires)
    (hroles : ∀ wire ∈ tree.decoderWires ca cb pa pb, wire ∈ protectedWires)
    (ha : Clean pa state) (hb : Clean pb state) :
    ∀ wire ∈ protectedWires,
      tree.runLeafState order (fun label a b s => run (leaf label a b) s) ca cb pa pb state wire =
        state wire := by
  rw [← run_dualUnaryActionUnitary_as_runLeafState_on order leaf
    (fun label a b s => run (leaf label a b) s) tree ca cb pa pb protectedWires state hlayout
    (by intro label hl a b ha hb state; rfl) hleaf hroles ha hb]
  exact dualUnaryActionUnitary_preservesOn order leaf tree ca cb pa pb protectedWires protectedWires state
    hlayout hleaf hroles hroles ha hb

private theorem update_outside {protectedWires : List Wire} {state logical : BasisState}
    (h : AgreesOutside protectedWires state logical) (w : Wire) (b : Bool) (hw : w ∈ protectedWires) :
    AgreesOutside protectedWires (state[w ↦ b]) logical := by
  intro other ho
  rw [upd_other _ _ _ (by intro he; subst other; exact ho hw)]
  exact h other ho

private theorem child_roles
    (ia ib ca cb pa pb : Wire) (zero one : DualUnaryActionTree) (ra rb protectedWires : List Wire)
    (h : ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).decoderWires ca cb (pa::ra) (pb::rb),
      w ∈ protectedWires) :
    (∀ w ∈ zero.decoderWires pa pb ra rb, w ∈ protectedWires) ∧
      (∀ w ∈ one.decoderWires pa pb ra rb, w ∈ protectedWires) := by
  constructor <;> intro w hw <;> apply h w <;>
    simp only [DualUnaryActionTree.decoderWires, List.mem_append, List.mem_dedup,
      DualUnaryActionTree.indexAWires, DualUnaryActionTree.indexBWires, List.mem_cons] at hw ⊢ <;> aesop

private theorem indices_ne_paths
    (ia ib ca cb pa pb : Wire) (zero one : DualUnaryActionTree) (ra rb : List Wire)
    (h : ((DualUnaryActionTree.node ia ib zero one).decoderWires ca cb (pa::ra) (pb::rb)).Nodup) :
    ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
        (DualUnaryActionTree.node ia ib zero one).indexBWires, w ≠ pa ∧ w ≠ pb := by
  have ha := List.nodup_append.mp (List.nodup_append.mp h).2.1
  have hb := List.nodup_append.mp ha.2.1
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact ⟨ha.2.2 w (by simpa using hw) pa (by simp),
      ha.2.2 w (by simpa using hw) pb (by simp)⟩
  · exact ⟨hb.2.2 w (by simpa using hw) pa (by simp),
      hb.2.2 w (by simpa using hw) pb (by simp)⟩

private theorem logical_outside
    (order : UnaryOrder) (leaf : Nat → Wire → Wire → Circuit)
    (logicalLeaf : Nat → Bool → Bool → BasisState → BasisState)
    (tree : DualUnaryActionTree) (ca cb : Wire) (pa pb protectedWires cleanWires : List Wire)
    (state route logical : BasisState) (activeA activeB : Bool)
    (hlayout : tree.Layout ca cb pa pb)
    (hleaf : DualUnaryLeafPreservesOn leaf tree.labels protectedWires protectedWires)
    (hlogical : ∀ label ∈ tree.labels, ∀ a b, a ∈ protectedWires → b ∈ protectedWires →
      ∀ s t, Clean cleanWires s → AgreesOutside protectedWires s t →
        AgreesOutside protectedWires (run (leaf label a b) s)
          (logicalLeaf label (s a) (s b) t))
    (hroles : ∀ w ∈ tree.decoderWires ca cb pa pb, w ∈ protectedWires)
    (houtside : AgreesOutside protectedWires state logical)
    (hca : state ca = activeA) (hcb : state cb = activeB)
    (hroute : ∀ w ∈ tree.indexAWires ++ tree.indexBWires, state w = route w)
    (hcleanA : Clean pa state) (hcleanB : Clean pb state)
    (hworkRoles : ∀ w ∈ cleanWires, w ∈ protectedWires)
    (hworkPaths : ∀ w ∈ cleanWires, w ∉ pa ++ pb)
    (hworkClean : Clean cleanWires state) :
    AgreesOutside protectedWires
      (tree.runLeafState order (fun label a b s => run (leaf label a b) s) ca cb pa pb state)
      (tree.runLogicalTree order logicalLeaf activeA activeB route logical) := by
  induction hlayout generalizing state logical activeA activeB with
  | leaf label ca cb pa pb hlocal =>
    simpa only [DualUnaryActionTree.runLeafState, DualUnaryActionTree.runLogicalTree, hca, hcb]
      using hlogical label (by simp [DualUnaryActionTree.labels]) ca cb
        (hroles ca (by simp [DualUnaryActionTree.decoderWires]))
        (hroles cb (by simp [DualUnaryActionTree.decoderWires])) state logical hworkClean houtside
  | node ia ib ca cb pa pb zero one ra rb hlocal hz ho ihz iho =>
    obtain ⟨hcai,hcapa,hiapa,hcbi,hcbpb,hibpb,hpapb,hpara,hparb,hpbra,hpbrb,
      hcapb,hiapb,hcbpa,hibpa⟩ := DualUnaryActionTree.Layout.nodeParts ia ib ca cb pa pb zero one ra rb hlocal
    have roles := child_roles ia ib ca cb pa pb zero one ra rb protectedWires hroles
    have hpa : pa ∈ protectedWires := hroles pa (by simp [DualUnaryActionTree.decoderWires])
    have hpb : pb ∈ protectedWires := hroles pb (by simp [DualUnaryActionTree.decoderWires])
    have hcam : ca ∈ protectedWires := hroles ca (by simp [DualUnaryActionTree.decoderWires])
    have hcbm : cb ∈ protectedWires := hroles cb (by simp [DualUnaryActionTree.decoderWires])
    have hrouteia : state ia = route ia := hroute ia (by simp [DualUnaryActionTree.indexAWires])
    have hrouteib : state ib = route ib := hroute ib (by simp [DualUnaryActionTree.indexBWires])
    have hindices := indices_ne_paths ia ib ca cb pa pb zero one ra rb hlocal
    have hindexProtected : ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
        (DualUnaryActionTree.node ia ib zero one).indexBWires, w ∈ protectedWires := by
      intro w hw
      apply hroles w
      simp only [DualUnaryActionTree.decoderWires, List.mem_append, List.mem_dedup]
      rcases List.mem_append.mp hw with hw | hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inl hw))
    have workChild : ∀ w ∈ cleanWires, w ∉ ra ++ rb := by
      intro w hw hm
      apply hworkPaths w hw
      simp only [List.mem_append, List.mem_cons]
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl (Or.inr hm)
      · exact Or.inr (Or.inr hm)
    have workNeA : ∀ w ∈ cleanWires, w ≠ pa := by
      intro w hw he; subst w; exact hworkPaths pa hw (by simp)
    have workNeB : ∀ w ∈ cleanWires, w ≠ pb := by
      intro w hw he; subst w; exact hworkPaths pb hw (by simp)
    have leafz : DualUnaryLeafPreservesOn leaf zero.labels protectedWires protectedWires := by
      intro label hl; exact hleaf label (by simp [DualUnaryActionTree.labels, hl])
    have leafo : DualUnaryLeafPreservesOn leaf one.labels protectedWires protectedWires := by
      intro label hl; exact hleaf label (by simp [DualUnaryActionTree.labels, hl])
    have logz : ∀ label ∈ zero.labels, ∀ a b, a ∈ protectedWires → b ∈ protectedWires →
        ∀ s t, Clean cleanWires s → AgreesOutside protectedWires s t → AgreesOutside protectedWires
          (run (leaf label a b) s) (logicalLeaf label (s a) (s b) t) := by
      intro label hl; exact hlogical label (by simp [DualUnaryActionTree.labels, hl])
    have logo : ∀ label ∈ one.labels, ∀ a b, a ∈ protectedWires → b ∈ protectedWires →
        ∀ s t, Clean cleanWires s → AgreesOutside protectedWires s t → AgreesOutside protectedWires
          (run (leaf label a b) s) (logicalLeaf label (s a) (s b) t) := by
      intro label hl; exact hlogical label (by simp [DualUnaryActionTree.labels, hl])
    let first := state[pa ↦ state ca && !state ia]
      [pb ↦ (state[pa ↦ state ca && !state ia]) cb && !(state[pa ↦ state ca && !state ia]) ib]
    let switch := fun s : BasisState => applyGate (.CX cb pb) (applyGate (.CX ca pa) s)
    have firstA : first pa = (activeA && !route ia) := by
      simp [first, upd, hpapb, hca, hrouteia]
    have firstB : first pb = (activeB && !route ib) := by
      simp [first, upd, hcbpa, hibpa, hcb, hrouteib]
    have firstCA : first ca = activeA := by simp [first, upd, hcapa, hcapb, hca]
    have firstCB : first cb = activeB := by simp [first, upd, hcbpa, hcbpb, hcb]
    have firstOutside : AgreesOutside protectedWires first logical :=
      update_outside (update_outside houtside pa _ hpa) pb _ hpb
    have firstCleanA : Clean ra first := by
      intro w hw
      have hwa : w ≠ pa := by intro he; subst w; exact hpara hw
      have hwb : w ≠ pb := by intro he; subst w; exact hpbra hw
      simp only [first, upd, hwa, hwb, ite_false]
      exact hcleanA w (by simp [hw])
    have firstCleanB : Clean rb first := by
      intro w hw
      have hwa : w ≠ pa := by intro he; subst w; exact hparb hw
      have hwb : w ≠ pb := by intro he; subst w; exact hpbrb hw
      simp only [first, upd, hwa, hwb, ite_false]
      exact hcleanB w (by simp [hw])
    have firstWork : Clean cleanWires first := by
      intro w hw
      simp only [first, upd, workNeA w hw, workNeB w hw, ite_false]
      exact hworkClean w hw
    have firstRoute : ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
        (DualUnaryActionTree.node ia ib zero one).indexBWires, first w = route w := by
      intro w hw
      obtain ⟨ha,hb⟩ := hindices w hw
      simp only [first, upd, ha, hb, ite_false]
      exact hroute w hw
    have switchA (s : BasisState) : switch s pa = (s pa ^^ s ca) := by
      simp [switch, applyGate, upd, hpapb]
    have switchB (s : BasisState) : switch s pb = (s pb ^^ s cb) := by
      simp [switch, applyGate, upd, Ne.symm hpapb, hcbpa]
    have switchCA (s : BasisState) : switch s ca = s ca := by
      simp [switch, applyGate, upd, hcapa, hcapb]
    have switchCB (s : BasisState) : switch s cb = s cb := by
      simp [switch, applyGate, upd, hcbpa, hcbpb]
    have switchOutside (s t : BasisState) (h : AgreesOutside protectedWires s t) :
        AgreesOutside protectedWires (switch s) t :=
      update_outside (update_outside h pa _ hpa) pb _ hpb
    have switchCleanA (s : BasisState) (h : Clean ra s) : Clean ra (switch s) := by
      intro w hw
      have hwa : w ≠ pa := by intro he; subst w; exact hpara hw
      have hwb : w ≠ pb := by intro he; subst w; exact hpbra hw
      simp only [switch, applyGate, upd, hwa, hwb, ite_false]
      exact h w hw
    have switchCleanB (s : BasisState) (h : Clean rb s) : Clean rb (switch s) := by
      intro w hw
      have hwa : w ≠ pa := by intro he; subst w; exact hparb hw
      have hwb : w ≠ pb := by intro he; subst w; exact hpbrb hw
      simp only [switch, applyGate, upd, hwa, hwb, ite_false]
      exact h w hw
    have switchWork (s : BasisState) (h : Clean cleanWires s) : Clean cleanWires (switch s) := by
      intro w hw
      simp only [switch, applyGate, upd, workNeA w hw, workNeB w hw, ite_false]
      exact h w hw
    have switchRoute (s : BasisState)
        (h : ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
          (DualUnaryActionTree.node ia ib zero one).indexBWires, s w = route w) :
        ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
          (DualUnaryActionTree.node ia ib zero one).indexBWires, switch s w = route w := by
      intro w hw
      obtain ⟨ha,hb⟩ := hindices w hw
      simp only [switch, applyGate, upd, ha, hb, ite_false]
      exact h w hw
    have routeZero (s : BasisState)
        (h : ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
          (DualUnaryActionTree.node ia ib zero one).indexBWires, s w = route w) :
        ∀ w ∈ zero.indexAWires ++ zero.indexBWires, s w = route w := by
      intro w hw; apply h w
      simp only [DualUnaryActionTree.indexAWires, DualUnaryActionTree.indexBWires,
        List.mem_append, List.mem_cons] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inr (Or.inl hw))
    have routeOne (s : BasisState)
        (h : ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
          (DualUnaryActionTree.node ia ib zero one).indexBWires, s w = route w) :
        ∀ w ∈ one.indexAWires ++ one.indexBWires, s w = route w := by
      intro w hw; apply h w
      simp only [DualUnaryActionTree.indexAWires, DualUnaryActionTree.indexBWires,
        List.mem_append, List.mem_cons] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (Or.inr (Or.inr hw))
      · exact Or.inr (Or.inr (Or.inr hw))
    have switchCommute (s : BasisState) :
        applyGate (.CX ca pa) (applyGate (.CX cb pb) s) = switch s := by
      funext w
      by_cases hwa : w=pa
      · subst w; simp [switch, applyGate, upd, hpapb, hcapb]
      · by_cases hwb : w=pb
        · subst w; simp [switch, applyGate, upd, Ne.symm hpapb, hcbpa]
        · simp [switch, applyGate, upd, hwa, hwb]
    have toggleZero (a b : Bool) : ((a && !b) ^^ a) = (a && b) := by
      cases a <;> cases b <;> decide
    have toggleOne (a b : Bool) : ((a && b) ^^ a) = (a && !b) := by
      cases a <;> cases b <;> decide
    cases order
    · let z := zero.runLeafState .inc (fun label a b s => run (leaf label a b) s) pa pb ra rb first
      let lz := zero.runLogicalTree .inc logicalLeaf (activeA && !route ia) (activeB && !route ib) route logical
      have zout : AgreesOutside protectedWires z lz :=
        ihz first logical _ _ leafz logz roles.1 firstOutside firstA firstB
          (routeZero first firstRoute) firstCleanA firstCleanB workChild firstWork
      have zp := physical_preserves .inc leaf zero pa pb ra rb protectedWires first hz leafz roles.1
        firstCleanA firstCleanB
      change ∀ w ∈ protectedWires, z w = first w at zp
      have za : Clean ra z := by
        intro w hw; rw [zp w (roles.1 w (by simp [DualUnaryActionTree.decoderWires, hw]))]
        exact firstCleanA w hw
      have zb : Clean rb z := by
        intro w hw; rw [zp w (roles.1 w (by simp [DualUnaryActionTree.decoderWires, hw]))]
        exact firstCleanB w hw
      have zr : ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
          (DualUnaryActionTree.node ia ib zero one).indexBWires, z w = route w := by
        intro w hw; rw [zp w (hindexProtected w hw)]; exact firstRoute w hw
      have zw : Clean cleanWires z := by
        intro w hw; rw [zp w (hworkRoles w hw)]; exact firstWork w hw
      have sa : switch z pa = (activeA && route ia) := by
        rw [switchA, zp pa hpa, zp ca hcam, firstA, firstCA, toggleZero]
      have sb : switch z pb = (activeB && route ib) := by
        rw [switchB, zp pb hpb, zp cb hcbm, firstB, firstCB, toggleZero]
      let o := one.runLeafState .inc (fun label a b s => run (leaf label a b) s) pa pb ra rb (switch z)
      have oout := iho (switch z) lz _ _ leafo logo roles.2 (switchOutside z lz zout) sa sb
        (routeOne _ (switchRoute z zr)) (switchCleanA z za) (switchCleanB z zb)
        workChild (switchWork z zw)
      change AgreesOutside protectedWires
        ((applyGate (.CX ca pa) (applyGate (.CX cb pb) o))[pb ↦ false][pa ↦ false])
        (one.runLogicalTree .inc logicalLeaf (activeA && route ia) (activeB && route ib) route lz)
      apply update_outside ?_ pa false hpa
      apply update_outside ?_ pb false hpb
      simp only [applyGate]
      apply update_outside ?_ pa _ hpa
      apply update_outside ?_ pb _ hpb
      exact oout
    · let sf := switch first
      have sa : sf pa = (activeA && route ia) := by
        change switch first pa = _
        rw [switchA, firstA, firstCA, toggleZero]
      have sb : sf pb = (activeB && route ib) := by
        change switch first pb = _
        rw [switchB, firstB, firstCB, toggleZero]
      let o := one.runLeafState .dec (fun label a b s => run (leaf label a b) s) pa pb ra rb sf
      let lo := one.runLogicalTree .dec logicalLeaf (activeA && route ia) (activeB && route ib) route logical
      have oout : AgreesOutside protectedWires o lo :=
        iho sf logical _ _ leafo logo roles.2 (switchOutside first logical firstOutside) sa sb
          (routeOne sf (switchRoute first firstRoute))
          (switchCleanA first firstCleanA) (switchCleanB first firstCleanB)
          workChild (switchWork first firstWork)
      have op := physical_preserves .dec leaf one pa pb ra rb protectedWires sf ho leafo roles.2
        (switchCleanA first firstCleanA) (switchCleanB first firstCleanB)
      change ∀ w ∈ protectedWires, o w = sf w at op
      have oa : Clean ra o := by
        intro w hw; rw [op w (roles.2 w (by simp [DualUnaryActionTree.decoderWires, hw]))]
        exact switchCleanA first firstCleanA w hw
      have ob : Clean rb o := by
        intro w hw; rw [op w (roles.2 w (by simp [DualUnaryActionTree.decoderWires, hw]))]
        exact switchCleanB first firstCleanB w hw
      have oor : ∀ w ∈ (DualUnaryActionTree.node ia ib zero one).indexAWires ++
          (DualUnaryActionTree.node ia ib zero one).indexBWires, o w = route w := by
        intro w hw; rw [op w (hindexProtected w hw)]; exact switchRoute first firstRoute w hw
      have ow : Clean cleanWires o := by
        intro w hw; rw [op w (hworkRoles w hw)]; exact switchWork first firstWork w hw
      have za : switch o pa = (activeA && !route ia) := by
        rw [switchA, op pa hpa, op ca hcam, sa]
        change ((activeA && route ia) ^^ switch first ca) = _
        rw [switchCA, firstCA, toggleOne]
      have zb : switch o pb = (activeB && !route ib) := by
        rw [switchB, op pb hpb, op cb hcbm, sb]
        change ((activeB && route ib) ^^ switch first cb) = _
        rw [switchCB, firstCB, toggleOne]
      have zout := ihz (switch o) lo _ _ leafz logz roles.1 (switchOutside o lo oout) za zb
        (routeZero _ (switchRoute o oor)) (switchCleanA o oa) (switchCleanB o ob)
        workChild (switchWork o ow)
      change AgreesOutside protectedWires
        ((zero.runLeafState .dec (fun label a b s => run (leaf label a b) s) pa pb ra rb
          (applyGate (.CX ca pa) (applyGate (.CX cb pb) o)))[pb ↦ false][pa ↦ false])
        (zero.runLogicalTree .dec logicalLeaf (activeA && !route ia) (activeB && !route ib) route lo)
      rw [switchCommute]
      exact update_outside (update_outside zout pb false hpb) pa false hpa

/-- The actual synchronized decoder traversal equals its source-ordered Boolean-pulse
execution. Physical leaves preserve the declared decoder interface and simulate logical
leaves outside that interface; logical leaves preserve it too. Both clean path stacks
and the possibly shared root controls are restored in the complete-state equality. -/
theorem run_dualUnaryActionUnitary_as_runLogicalTree
    (order : UnaryOrder) (leaf : Nat → Wire → Wire → Circuit)
    (logicalLeaf : Nat → Bool → Bool → BasisState → BasisState)
    (tree : DualUnaryActionTree) (ca cb : Wire) (pa pb protectedWires cleanWires : List Wire)
    (state : BasisState) (hlayout : tree.Layout ca cb pa pb)
    (hleaf : DualUnaryLeafPreservesOn leaf tree.labels protectedWires protectedWires)
    (hlogical : ∀ label ∈ tree.labels, ∀ a b, a ∈ protectedWires → b ∈ protectedWires →
      ∀ s t, Clean cleanWires s → AgreesOutside protectedWires s t →
        AgreesOutside protectedWires (run (leaf label a b) s)
          (logicalLeaf label (s a) (s b) t))
    (hlogicalPreserves : ∀ label ∈ tree.labels, ∀ a b state wire, wire ∈ protectedWires →
      logicalLeaf label a b state wire = state wire)
    (hroles : ∀ w ∈ tree.decoderWires ca cb pa pb, w ∈ protectedWires)
    (hcleanA : Clean pa state) (hcleanB : Clean pb state)
    (hworkRoles : ∀ w ∈ cleanWires, w ∈ protectedWires)
    (hworkPaths : ∀ w ∈ cleanWires, w ∉ pa ++ pb)
    (hworkClean : Clean cleanWires state) :
    run (dualUnaryActionUnitary order leaf tree ca cb pa pb) state =
      tree.runLogicalTree order logicalLeaf (state ca) (state cb) state state := by
  have hr := run_dualUnaryActionUnitary_as_runLeafState_on order leaf
    (fun label a b s => run (leaf label a b) s) tree ca cb pa pb protectedWires state hlayout
    (by intro label hl a b ha hb state; rfl) hleaf hroles hcleanA hcleanB
  have ho := logical_outside order leaf logicalLeaf tree ca cb pa pb protectedWires cleanWires
    state state state (state ca) (state cb) hlayout hleaf hlogical hroles
    (by intro w hw; rfl) rfl rfl (by intro w hw; rfl) hcleanA hcleanB hworkRoles hworkPaths hworkClean
  have hp := dualUnaryActionUnitary_preservesOn order leaf tree ca cb pa pb protectedWires
    protectedWires state hlayout hleaf hroles hroles hcleanA hcleanB
  have hl := logical_preserves order logicalLeaf tree (state ca) (state cb) state state
    protectedWires hlogicalPreserves
  funext wire
  by_cases hw : wire ∈ protectedWires
  · rw [hp wire hw, hl wire hw]
  · rw [hr]
    exact ho wire hw

end ShorECDLP.Paper2607_13816
