import ShorECDLP.Submission.«2607_13816».EEA.DualUnaryAction
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Size

/-!
# Certified highest-varying-bit tree construction

The pinned supplement normalizes unary labels with `sorted(set(labels))`, chooses the highest
bit on which the current labels vary, and recursively prunes empty halves.  `buildAt` implements
the same construction as a scan of aligned power-of-two blocks: an empty half is discarded and a
node at bit `depth` is emitted exactly when both halves survive.  Starting at base zero makes this
the supplement's highest-varying-bit split without trusting the Python builder.

The public certificates prove that every requested in-range label occurs exactly once, leaf order
is the sorted deduplicated label list, `.inc` visits that list forward, `.dec` visits it backward,
and every stored index wire comes from a strictly smaller bit position.  For the source's
top-special range, the last fact keeps the separately handled top bit out of its corresponding
index bank, including the singleton-main-tree edge case.  Cross-bank separation remains a later
full-register layout obligation.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

namespace DualUnaryActionTree

def optionLabels : Option DualUnaryActionTree → List Nat
  | none => []
  | some tree => tree.labels

def combine (indexBitA indexBitB : Wire) :
    Option DualUnaryActionTree → Option DualUnaryActionTree →
      Option DualUnaryActionTree
  | none, none => none
  | some zero, none => some zero
  | none, some one => some one
  | some zero, some one => some (.node indexBitA indexBitB zero one)

@[simp]
  theorem optionLabels_combine
    (indexBitA indexBitB : Wire)
    (zero one : Option DualUnaryActionTree) :
    optionLabels (combine indexBitA indexBitB zero one) =
      optionLabels zero ++ optionLabels one := by
  cases zero <;> cases one <;>
    simp [combine, optionLabels, DualUnaryActionTree.labels]

def labelsInBlock (labels : Finset Nat) (depth base : Nat) : Finset Nat :=
  labels.filter fun label ↦ base ≤ label ∧ label < base + 2 ^ depth

def buildAt (indexA indexB : Nat → Wire) :
    Nat → Nat → Finset Nat → Option DualUnaryActionTree
  | 0, base, labels =>
      if base ∈ labels then some (.leaf base) else none
  | depth + 1, base, labels =>
      combine (indexA depth) (indexB depth)
        (buildAt indexA indexB depth base labels)
        (buildAt indexA indexB depth (base + 2 ^ depth) labels)

private theorem block_succ_iff
    (depth base label : Nat) :
    (base ≤ label ∧ label < base + 2 ^ (depth + 1)) ↔
      (base ≤ label ∧ label < base + 2 ^ depth) ∨
      (base + 2 ^ depth ≤ label ∧
        label < base + 2 ^ depth + 2 ^ depth) := by
  rw [Nat.pow_succ]
  omega

theorem mem_optionLabels_buildAt
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (depth base label : Nat) :
    label ∈ optionLabels (buildAt indexA indexB depth base labels) ↔
      label ∈ labels ∧ base ≤ label ∧ label < base + 2 ^ depth := by
  induction depth generalizing base with
  | zero =>
      by_cases hbase : base ∈ labels
      · constructor
        · intro hlabel
          simp [buildAt, optionLabels, DualUnaryActionTree.labels, hbase] at hlabel
          subst label
          simp [hbase]
        · rintro ⟨hmem, hlow, hhigh⟩
          have : label = base := by omega
          subst label
          simp [buildAt, optionLabels, DualUnaryActionTree.labels, hbase]
      · constructor
        · simp [buildAt, optionLabels, hbase]
        · rintro ⟨hmem, hlow, hhigh⟩
          have : label = base := by omega
          subst label
          exact (hbase hmem).elim
  | succ depth ih =>
      rw [buildAt, optionLabels_combine, List.mem_append,
        ih, ih, block_succ_iff]
      aesop

theorem optionLabels_buildAt_pairwise
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (depth base : Nat) :
    (optionLabels (buildAt indexA indexB depth base labels)).Pairwise (· < ·) := by
  induction depth generalizing base with
  | zero =>
      by_cases hbase : base ∈ labels <;>
        simp [buildAt, optionLabels, DualUnaryActionTree.labels, hbase]
  | succ depth ih =>
      rw [buildAt, optionLabels_combine, List.pairwise_append]
      refine ⟨ih base, ih (base + 2 ^ depth), ?_⟩
      intro left hleft right hright
      have hl := (mem_optionLabels_buildAt
        indexA indexB labels depth base left).1 hleft
      have hr := (mem_optionLabels_buildAt
        indexA indexB labels depth (base + 2 ^ depth) right).1 hright
      exact lt_of_lt_of_le hl.2.2 hr.2.1

theorem exists_mem_labels (tree : DualUnaryActionTree) :
    ∃ label, label ∈ tree.labels := by
  induction tree with
  | leaf label =>
      exact ⟨label, by simp [DualUnaryActionTree.labels]⟩
  | node indexBitA indexBitB zero one ihZero ihOne =>
      obtain ⟨label, hlabel⟩ := ihZero
      exact ⟨label, List.mem_append_left one.labels hlabel⟩

theorem buildAt_eq_none_iff
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (depth base : Nat) :
    buildAt indexA indexB depth base labels = none ↔
      labelsInBlock labels depth base = ∅ := by
  constructor
  · intro hnone
    apply Finset.eq_empty_iff_forall_notMem.2
    intro label hlabel
    have hmember :
        label ∈ optionLabels (buildAt indexA indexB depth base labels) :=
      (mem_optionLabels_buildAt indexA indexB labels depth base label).2 <| by
        simpa [labelsInBlock] using hlabel
    rw [hnone] at hmember
    simp [optionLabels] at hmember
  · intro hempty
    cases hbuild : buildAt indexA indexB depth base labels with
    | none => rfl
    | some tree =>
        obtain ⟨label, hlabel⟩ := exists_mem_labels tree
        have hmember : label ∈ labelsInBlock labels depth base := by
          simp only [labelsInBlock, Finset.mem_filter]
          exact (mem_optionLabels_buildAt
            indexA indexB labels depth base label).1 <| by
              simpa [optionLabels, hbuild] using hlabel
        rw [hempty] at hmember
        simp at hmember

/-- Certificate for the exact source construction.  At each candidate bit, an empty half is
pruned; a node using that bit is emitted precisely when both aligned halves are inhabited. -/
inductive SourceBuilt (indexA indexB : Nat → Wire) (labels : Finset Nat) :
    Nat → Nat → DualUnaryActionTree → Prop where
  | leaf (base : Nat) (hbase : base ∈ labels) :
      SourceBuilt indexA indexB labels 0 base (.leaf base)
  | onlyZero (depth base : Nat) (zero : DualUnaryActionTree)
      (hzero : SourceBuilt indexA indexB labels depth base zero)
      (hone : labelsInBlock labels depth (base + 2 ^ depth) = ∅) :
      SourceBuilt indexA indexB labels (depth + 1) base zero
  | onlyOne (depth base : Nat) (one : DualUnaryActionTree)
      (hzero : labelsInBlock labels depth base = ∅)
      (hone : SourceBuilt indexA indexB labels depth
        (base + 2 ^ depth) one) :
      SourceBuilt indexA indexB labels (depth + 1) base one
  | node (depth base : Nat) (zero one : DualUnaryActionTree)
      (hzero : SourceBuilt indexA indexB labels depth base zero)
      (hone : SourceBuilt indexA indexB labels depth
        (base + 2 ^ depth) one) :
      SourceBuilt indexA indexB labels (depth + 1) base
        (.node (indexA depth) (indexB depth) zero one)

theorem buildAt_sourceBuilt
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (depth base : Nat)
    (tree : DualUnaryActionTree)
    (hbuild : buildAt indexA indexB depth base labels = some tree) :
    SourceBuilt indexA indexB labels depth base tree := by
  induction depth generalizing base tree with
  | zero =>
      by_cases hbase : base ∈ labels
      · simp [buildAt, hbase] at hbuild
        subst tree
        exact .leaf base hbase
      · simp [buildAt, hbase] at hbuild
  | succ depth ih =>
      rw [buildAt] at hbuild
      cases hzero : buildAt indexA indexB depth base labels with
      | none =>
          cases hone : buildAt indexA indexB depth
              (base + 2 ^ depth) labels with
          | none => simp [hzero, hone, combine] at hbuild
          | some one =>
              simp [hzero, hone, combine] at hbuild
              subst tree
              exact .onlyOne depth base one
                ((buildAt_eq_none_iff indexA indexB labels depth base).1 hzero)
                (ih (base + 2 ^ depth) one hone)
      | some zero =>
          cases hone : buildAt indexA indexB depth
              (base + 2 ^ depth) labels with
          | none =>
              simp [hzero, hone, combine] at hbuild
              subst tree
              exact .onlyZero depth base zero (ih base zero hzero)
                ((buildAt_eq_none_iff indexA indexB labels depth
                  (base + 2 ^ depth)).1 hone)
          | some one =>
              simp [hzero, hone, combine] at hbuild
              subst tree
              exact .node depth base zero one
                (ih base zero hzero) (ih (base + 2 ^ depth) one hone)

def pathDepth : DualUnaryActionTree → Nat
  | .leaf _ => 0
  | .node _ _ zero one => 1 + max zero.pathDepth one.pathDepth

theorem SourceBuilt.pathDepth_le
    {indexA indexB : Nat → Wire} {labels : Finset Nat}
    {depth base : Nat} {tree : DualUnaryActionTree}
    (hbuilt : SourceBuilt indexA indexB labels depth base tree) :
    tree.pathDepth ≤ depth := by
  induction hbuilt with
  | leaf => simp [pathDepth]
  | onlyZero depth base zero hzero hone ih => omega
  | onlyOne depth base one hzero hone ih => omega
  | node depth base zero one hzero hone ihZero ihOne =>
      simp only [pathDepth]
      omega

theorem SourceBuilt.indexAWires
    {indexA indexB : Nat → Wire} {labels : Finset Nat}
    {depth base : Nat} {tree : DualUnaryActionTree}
    (hbuilt : SourceBuilt indexA indexB labels depth base tree) :
    ∀ {wire}, wire ∈ tree.indexAWires →
      ∃ bit, bit < depth ∧ wire = indexA bit := by
  induction hbuilt with
  | leaf => simp [DualUnaryActionTree.indexAWires]
  | onlyZero depth base zero hzero hone ih =>
      intro wire hwire
      obtain ⟨bit, hbit, rfl⟩ := ih hwire
      exact ⟨bit, Nat.lt_succ_of_lt hbit, rfl⟩
  | onlyOne depth base one hzero hone ih =>
      intro wire hwire
      obtain ⟨bit, hbit, rfl⟩ := ih hwire
      exact ⟨bit, Nat.lt_succ_of_lt hbit, rfl⟩
  | node depth base zero one hzero hone ihZero ihOne =>
      intro wire hwire
      simp only [DualUnaryActionTree.indexAWires,
        List.mem_cons, List.mem_append] at hwire
      rcases hwire with rfl | hwire | hwire
      · exact ⟨depth, Nat.lt_succ_self depth, rfl⟩
      · obtain ⟨bit, hbit, heq⟩ := ihZero hwire
        exact ⟨bit, Nat.lt_succ_of_lt hbit, heq⟩
      · obtain ⟨bit, hbit, heq⟩ := ihOne hwire
        exact ⟨bit, Nat.lt_succ_of_lt hbit, heq⟩

theorem SourceBuilt.indexBWires
    {indexA indexB : Nat → Wire} {labels : Finset Nat}
    {depth base : Nat} {tree : DualUnaryActionTree}
    (hbuilt : SourceBuilt indexA indexB labels depth base tree) :
    ∀ {wire}, wire ∈ tree.indexBWires →
      ∃ bit, bit < depth ∧ wire = indexB bit := by
  induction hbuilt with
  | leaf => simp [DualUnaryActionTree.indexBWires]
  | onlyZero depth base zero hzero hone ih =>
      intro wire hwire
      obtain ⟨bit, hbit, rfl⟩ := ih hwire
      exact ⟨bit, Nat.lt_succ_of_lt hbit, rfl⟩
  | onlyOne depth base one hzero hone ih =>
      intro wire hwire
      obtain ⟨bit, hbit, rfl⟩ := ih hwire
      exact ⟨bit, Nat.lt_succ_of_lt hbit, rfl⟩
  | node depth base zero one hzero hone ihZero ihOne =>
      intro wire hwire
      simp only [DualUnaryActionTree.indexBWires,
        List.mem_cons, List.mem_append] at hwire
      rcases hwire with rfl | hwire | hwire
      · exact ⟨depth, Nat.lt_succ_self depth, rfl⟩
      · obtain ⟨bit, hbit, heq⟩ := ihZero hwire
        exact ⟨bit, Nat.lt_succ_of_lt hbit, heq⟩
      · obtain ⟨bit, hbit, heq⟩ := ihOne hwire
        exact ⟨bit, Nat.lt_succ_of_lt hbit, heq⟩

def visitLabels : UnaryOrder → DualUnaryActionTree → List Nat
  | _, .leaf label => [label]
  | .inc, .node _ _ zero one => visitLabels .inc zero ++ visitLabels .inc one
  | .dec, .node _ _ zero one => visitLabels .dec one ++ visitLabels .dec zero

@[simp]
theorem visitLabels_inc (tree : DualUnaryActionTree) :
    visitLabels .inc tree = tree.labels := by
  induction tree with
  | leaf => rfl
  | node indexBitA indexBitB zero one ihZero ihOne =>
      simp [visitLabels, DualUnaryActionTree.labels, ihZero, ihOne]

@[simp]
theorem visitLabels_dec (tree : DualUnaryActionTree) :
    visitLabels .dec tree = tree.labels.reverse := by
  induction tree with
  | leaf => rfl
  | node indexBitA indexBitB zero one ihZero ihOne =>
      simp [visitLabels, DualUnaryActionTree.labels, ihZero, ihOne]

theorem buildAt_labels_eq_sort
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (depth base : Nat)
    (tree : DualUnaryActionTree)
    (hbuild : buildAt indexA indexB depth base labels = some tree) :
    tree.labels = (labelsInBlock labels depth base).sort (· ≤ ·) := by
  have hsortedLT : tree.labels.Pairwise (· < ·) := by
    simpa [optionLabels, hbuild] using
      optionLabels_buildAt_pairwise indexA indexB labels depth base
  have hsortedLE : tree.labels.Pairwise (· ≤ ·) :=
    hsortedLT.imp fun h ↦ Nat.le_of_lt h
  have hfinset : tree.labels.toFinset = labelsInBlock labels depth base := by
    ext label
    simp only [List.mem_toFinset, labelsInBlock, Finset.mem_filter]
    simpa [optionLabels, hbuild] using
      mem_optionLabels_buildAt indexA indexB labels depth base label
  calc
    tree.labels = tree.labels.toFinset.sort (· ≤ ·) := by
      symm
      exact (List.toFinset_sort (r := (· ≤ ·)) hsortedLT.nodup).2 hsortedLE
    _ = (labelsInBlock labels depth base).sort (· ≤ ·) := by rw [hfinset]

def build (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat) : Option DualUnaryActionTree :=
  buildAt indexA indexB width 0 labels

theorem build_labels_eq_sort
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree)
    (hbound : ∀ label ∈ labels, label < 2 ^ width) :
    tree.labels = labels.sort (· ≤ ·) := by
  rw [build] at hbuild
  rw [buildAt_labels_eq_sort indexA indexB labels width 0 tree hbuild]
  congr 1
  apply Finset.filter_eq_self.2
  intro label hlabel
  exact ⟨Nat.zero_le label, by simpa using hbound label hlabel⟩

theorem build_labels_pairwise
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree) :
    tree.labels.Pairwise (· < ·) := by
  rw [build] at hbuild
  simpa [optionLabels, hbuild] using
    optionLabels_buildAt_pairwise indexA indexB labels width 0

theorem build_labels_nodup
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree) :
    tree.labels.Nodup :=
  (build_labels_pairwise indexA indexB width labels tree hbuild).nodup

theorem build_exists
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (hnonempty : labels.Nonempty)
    (hbound : ∀ label ∈ labels, label < 2 ^ width) :
    ∃ tree, build indexA indexB width labels = some tree := by
  obtain ⟨label, hlabel⟩ := hnonempty
  have hmember : label ∈ optionLabels (build indexA indexB width labels) := by
    rw [build]
    exact (mem_optionLabels_buildAt
      indexA indexB labels width 0 label).2
        ⟨hlabel, Nat.zero_le label, by simpa using hbound label hlabel⟩
  cases hbuild : build indexA indexB width labels with
  | none =>
      rw [hbuild] at hmember
      simp [optionLabels] at hmember
  | some tree => exact ⟨tree, rfl⟩

theorem build_sourceBuilt
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree) :
    SourceBuilt indexA indexB labels width 0 tree := by
  exact buildAt_sourceBuilt indexA indexB labels width 0 tree hbuild

theorem build_pathDepth_le
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree) :
    tree.pathDepth ≤ width :=
  (build_sourceBuilt indexA indexB width labels tree hbuild).pathDepth_le

theorem build_indexAWires
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree)
    {wire : Wire} (hwire : wire ∈ tree.indexAWires) :
    ∃ bit, bit < width ∧ wire = indexA bit :=
  (build_sourceBuilt indexA indexB width labels tree hbuild).indexAWires hwire

theorem build_indexBWires
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree)
    {wire : Wire} (hwire : wire ∈ tree.indexBWires) :
    ∃ bit, bit < width ∧ wire = indexB bit :=
  (build_sourceBuilt indexA indexB width labels tree hbuild).indexBWires hwire

/-- The separate top-special endpoint bit is outside the main pruned tree whenever register
indices map injectively to wires. -/
theorem build_topIndexA_not_mem
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree)
    (hinjective : Function.Injective indexA) :
    indexA width ∉ tree.indexAWires := by
  intro hmem
  obtain ⟨bit, hbit, heq⟩ :=
    build_indexAWires indexA indexB width labels tree hbuild hmem
  have : width = bit := hinjective heq
  omega

theorem build_topIndexB_not_mem
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree)
    (hinjective : Function.Injective indexB) :
    indexB width ∉ tree.indexBWires := by
  intro hmem
  obtain ⟨bit, hbit, heq⟩ :=
    build_indexBWires indexA indexB width labels tree hbuild hmem
  have : width = bit := hinjective heq
  omega

theorem build_visitLabels_inc
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree)
    (hbound : ∀ label ∈ labels, label < 2 ^ width) :
    tree.visitLabels .inc = labels.sort (· ≤ ·) := by
  rw [visitLabels_inc,
    build_labels_eq_sort indexA indexB width labels tree hbuild hbound]

theorem build_visitLabels_dec
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : Finset Nat)
    (tree : DualUnaryActionTree)
    (hbuild : build indexA indexB width labels = some tree)
    (hbound : ∀ label ∈ labels, label < 2 ^ width) :
    tree.visitLabels .dec = (labels.sort (· ≤ ·)).reverse := by
  rw [visitLabels_dec,
    build_labels_eq_sort indexA indexB width labels tree hbuild hbound]

/-- Python's `max(1, max(labels).bit_length())`, stated with Lean's `Nat.size`. -/
def sourceWidth (labels : Finset Nat) : Nat :=
  if hlabels : labels.Nonempty then
    max 1 (labels.max' hlabels).size
  else 1

theorem sourceWidth_pos (labels : Finset Nat) : 0 < sourceWidth labels := by
  by_cases hlabels : labels.Nonempty
  · rw [sourceWidth, dif_pos hlabels]
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  · simp [sourceWidth, hlabels]

theorem label_lt_two_pow_sourceWidth
    (labels : Finset Nat) (label : Nat) (hlabel : label ∈ labels) :
    label < 2 ^ sourceWidth labels := by
  have hlabels : labels.Nonempty := ⟨label, hlabel⟩
  rw [sourceWidth, dif_pos hlabels]
  apply Nat.size_le.mp
  exact le_trans
    (Nat.size_le_size (Finset.le_max' labels label hlabel))
    (Nat.le_max_right 1 (labels.max' hlabels).size)

theorem sourceWidth_le
    (labels : Finset Nat) (width : Nat)
    (hwidth : 0 < width)
    (hbound : ∀ label ∈ labels, label < 2 ^ width) :
    sourceWidth labels ≤ width := by
  by_cases hlabels : labels.Nonempty
  · rw [sourceWidth, dif_pos hlabels]
    apply max_le
    · omega
    · apply Nat.size_le.mpr
      exact hbound (labels.max' hlabels) (Finset.max'_mem labels hlabels)
  · simp [sourceWidth, hlabels]
    omega

/-- Exact source-width builder over a deduplicated set of labels. -/
def buildSource (indexA indexB : Nat → Wire)
    (labels : Finset Nat) : Option DualUnaryActionTree :=
  build indexA indexB (sourceWidth labels) labels

theorem buildSource_exists
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (hnonempty : labels.Nonempty) :
    ∃ tree, buildSource indexA indexB labels = some tree := by
  exact build_exists indexA indexB (sourceWidth labels) labels hnonempty
    (label_lt_two_pow_sourceWidth labels)

theorem buildSource_labels_eq_sort
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (tree : DualUnaryActionTree)
    (hbuild : buildSource indexA indexB labels = some tree) :
    tree.labels = labels.sort (· ≤ ·) := by
  exact build_labels_eq_sort indexA indexB (sourceWidth labels) labels tree hbuild
    (label_lt_two_pow_sourceWidth labels)

theorem buildSource_visitLabels_inc
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (tree : DualUnaryActionTree)
    (hbuild : buildSource indexA indexB labels = some tree) :
    tree.visitLabels .inc = labels.sort (· ≤ ·) := by
  exact build_visitLabels_inc indexA indexB (sourceWidth labels) labels tree hbuild
    (label_lt_two_pow_sourceWidth labels)

theorem buildSource_visitLabels_dec
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (tree : DualUnaryActionTree)
    (hbuild : buildSource indexA indexB labels = some tree) :
    tree.visitLabels .dec = (labels.sort (· ≤ ·)).reverse := by
  exact build_visitLabels_dec indexA indexB (sourceWidth labels) labels tree hbuild
    (label_lt_two_pow_sourceWidth labels)

theorem buildSource_pathDepth_le
    (indexA indexB : Nat → Wire)
    (labels : Finset Nat) (tree : DualUnaryActionTree)
    (hbuild : buildSource indexA indexB labels = some tree) :
    tree.pathDepth ≤ sourceWidth labels :=
  build_pathDepth_le indexA indexB (sourceWidth labels) labels tree hbuild

/-- In the source's top-special interval, the main labels are `0, ..., 2^depth - 1` and the
separately handled endpoint bit is `depth`.  That bit is absent from the corresponding A-index
bank, including `depth = 0`, where the main tree is the singleton leaf zero. -/
theorem buildSource_topSpecial_indexA_not_mem
    (indexA indexB : Nat → Wire)
    (depth : Nat) (tree : DualUnaryActionTree)
    (hbuild : buildSource indexA indexB (Finset.range (2 ^ depth)) = some tree)
    (hinjective : Function.Injective indexA) :
    indexA depth ∉ tree.indexAWires := by
  cases depth with
  | zero =>
      simp [buildSource, sourceWidth, build, buildAt, combine] at hbuild
      subst tree
      simp [DualUnaryActionTree.indexAWires]
  | succ depth =>
      intro hmem
      obtain ⟨bit, hbit, heq⟩ := build_indexAWires indexA indexB
        (sourceWidth (Finset.range (2 ^ (depth + 1))))
        (Finset.range (2 ^ (depth + 1))) tree hbuild hmem
      have hwidth : sourceWidth (Finset.range (2 ^ (depth + 1))) ≤ depth + 1 :=
        sourceWidth_le _ _ (Nat.succ_pos depth) (by
          intro label hlabel
          simpa using hlabel)
      have : depth + 1 = bit := hinjective heq
      omega

/-- B-index-bank counterpart of `buildSource_topSpecial_indexA_not_mem`. -/
theorem buildSource_topSpecial_indexB_not_mem
    (indexA indexB : Nat → Wire)
    (depth : Nat) (tree : DualUnaryActionTree)
    (hbuild : buildSource indexA indexB (Finset.range (2 ^ depth)) = some tree)
    (hinjective : Function.Injective indexB) :
    indexB depth ∉ tree.indexBWires := by
  cases depth with
  | zero =>
      simp [buildSource, sourceWidth, build, buildAt, combine] at hbuild
      subst tree
      simp [DualUnaryActionTree.indexBWires]
  | succ depth =>
      intro hmem
      obtain ⟨bit, hbit, heq⟩ := build_indexBWires indexA indexB
        (sourceWidth (Finset.range (2 ^ (depth + 1))))
        (Finset.range (2 ^ (depth + 1))) tree hbuild hmem
      have hwidth : sourceWidth (Finset.range (2 ^ (depth + 1))) ≤ depth + 1 :=
        sourceWidth_le _ _ (Nat.succ_pos depth) (by
          intro label hlabel
          simpa using hlabel)
      have : depth + 1 = bit := hinjective heq
      omega

/-- Width-explicit list wrapper: Python's `sorted(set(labels))` is `labels.toFinset.sort`. -/
def buildFromList (indexA indexB : Nat → Wire)
    (width : Nat) (labels : List Nat) : Option DualUnaryActionTree :=
  build indexA indexB width labels.toFinset

theorem buildFromList_visitLabels_inc
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : List Nat)
    (tree : DualUnaryActionTree)
    (hbuild : buildFromList indexA indexB width labels = some tree)
    (hbound : ∀ label ∈ labels, label < 2 ^ width) :
    tree.visitLabels .inc = labels.toFinset.sort (· ≤ ·) := by
  apply build_visitLabels_inc indexA indexB width labels.toFinset tree hbuild
  intro label hlabel
  exact hbound label (by simpa using hlabel)

/-- The supplement-facing entry point: deduplicate the input list and derive its source bit width. -/
def buildSourceFromList (indexA indexB : Nat → Wire)
    (labels : List Nat) : Option DualUnaryActionTree :=
  buildSource indexA indexB labels.toFinset

theorem buildSourceFromList_visitLabels_inc
    (indexA indexB : Nat → Wire)
    (labels : List Nat) (tree : DualUnaryActionTree)
    (hbuild : buildSourceFromList indexA indexB labels = some tree) :
    tree.visitLabels .inc = labels.toFinset.sort (· ≤ ·) :=
  buildSource_visitLabels_inc indexA indexB labels.toFinset tree hbuild

theorem buildSourceFromList_visitLabels_dec
    (indexA indexB : Nat → Wire)
    (labels : List Nat) (tree : DualUnaryActionTree)
    (hbuild : buildSourceFromList indexA indexB labels = some tree) :
    tree.visitLabels .dec = (labels.toFinset.sort (· ≤ ·)).reverse :=
  buildSource_visitLabels_dec indexA indexB labels.toFinset tree hbuild

theorem buildFromList_visitLabels_dec
    (indexA indexB : Nat → Wire)
    (width : Nat) (labels : List Nat)
    (tree : DualUnaryActionTree)
    (hbuild : buildFromList indexA indexB width labels = some tree)
    (hbound : ∀ label ∈ labels, label < 2 ^ width) :
    tree.visitLabels .dec = (labels.toFinset.sort (· ≤ ·)).reverse := by
  apply build_visitLabels_dec indexA indexB width labels.toFinset tree hbuild
  intro label hlabel
  exact hbound label (by simpa using hlabel)

/-- Closed regression: duplicate removal and the skipped common high bit agree with `_split_bit`.
The first emitted node is bit one, not the common bit two. -/
theorem buildSourceFromList_highestVaryingBit_regression :
    buildSourceFromList (fun bit : Nat => bit) (fun bit : Nat => 100 + bit)
        (7 :: 5 :: 6 :: 7 :: []) =
      some (.node 1 101 (.leaf 5) (.node 0 100 (.leaf 6) (.leaf 7))) := by
  decide

end DualUnaryActionTree

end

end ShorECDLP.Paper2607_13816
