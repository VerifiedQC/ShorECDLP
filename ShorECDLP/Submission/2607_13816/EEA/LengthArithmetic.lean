import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks

/-! # Arithmetic interpretation of the grouped length writers -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem length_xor_combine (bits : List Bool) (a b : Nat) :
    xorConstantBits (xorConstantBits bits a) b = xorConstantBits bits (a ^^^ b) := by
  induction bits generalizing a b with
  | nil => rfl
  | cons bit bits ih =>
    simp only [xorConstantBits, Nat.testBit_xor, Nat.xor_div_two]
    rw [ih]
    cases ha : a.testBit 0 <;> cases hb : b.testBit 0 <;> simp

private theorem length_allFalse_append (xs ys : List Bool) :
    allFalse (xs ++ ys) = (allFalse xs && allFalse ys) := by
  induction xs with
  | nil => simp [allFalse]
  | cons x xs ih => simp [allFalse, ih, Bool.and_assoc]

private theorem length_suffix_append (xs ys : List Bool) :
    suffixZeroFlags (xs ++ ys) =
      gateWord (allFalse ys) (suffixZeroFlags xs) ++ suffixZeroFlags ys := by
  induction xs with
  | nil => simp [suffixZeroFlags, gateWord]
  | cons x xs ih =>
    simp [suffixZeroFlags, length_allFalse_append, ih, gateWord,
      Bool.and_comm, Bool.and_left_comm]

private theorem length_prefix_cons (b : Bool) (bits : List Bool) :
    prefixZeroFlags (b :: bits) = (!b) :: gateWord (!b) (prefixZeroFlags bits) := by
  simp [prefixZeroFlags, List.reverse_cons, length_suffix_append,
    suffixZeroFlags, allFalse, gateWord, List.map_reverse]

private theorem length_write_false (f : Nat → Nat) (labels : List Nat)
    (selectors bits : List Bool) :
    constantWriteWord f labels (gateWord false selectors) bits = bits := by
  induction labels generalizing selectors bits with
  | nil => rfl
  | cons label labels ih =>
    cases selectors with
    | nil => rfl
    | cons selector selectors =>
      simp only [gateWord, List.map_cons, Bool.false_and, constantWriteWord, gatedXorConstantBits_false]
      exact ih selectors bits

private theorem length_prefix_telescope (f : Nat → Nat) (k : Nat)
    (source target : List Bool) :
    constantWriteWord (fun label => f label ^^^ f (label + 1))
      (List.range' k source.length) (prefixZeroFlags source)
      (xorConstantBits target (f k)) =
    xorConstantBits target (f (k + source.findIdx id)) := by
  induction source generalizing k target with
  | nil => simp [prefixZeroFlags, suffixZeroFlags, constantWriteWord]
  | cons b source ih =>
    rw [List.length_cons, List.range'_succ, length_prefix_cons]
    cases b with
    | false =>
      simp only [Bool.not_false, gateWord, Bool.true_and, List.map_id',
        constantWriteWord, gatedXorConstantBits_true]
      rw [length_xor_combine, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, ih]
      simp [List.findIdx_cons, Nat.add_comm, Nat.add_left_comm]
    | true =>
      simp only [Bool.not_true, constantWriteWord, gatedXorConstantBits_false]
      rw [length_write_false]
      simp [List.findIdx_cons]


private theorem length_write_congr (f g : Nat → Nat) (labels : List Nat)
    (selectors target : List Bool) (h : ∀ label ∈ labels, f label = g label) :
    constantWriteWord f labels selectors target = constantWriteWord g labels selectors target := by
  induction labels generalizing selectors target with
  | nil => rfl
  | cons label labels ih =>
    cases selectors with
    | nil => rfl
    | cons selector selectors =>
      simp only [constantWriteWord]
      rw [h label (by simp)]
      exact ih selectors _ (by intro x hx; exact h x (by simp [hx]))

/-- The enabled right-length writer XORs the encoding of the first set position.
An all-zero decoded range writes the all-ones sentinel. -/
theorem rightLengthWordAction_firstSet (n width k K : Nat) (hkK : k ≤ K)
    (source target : List Bool) (hlen : source.length = K - k + 1) :
    rightLengthWordAction n width k K true source target =
      xorConstantBits target (if source.findIdx id < source.length then
        rightLengthValue n width (k + source.findIdx id) else 2^width - 1) := by
  let f : Nat → Nat := fun label =>
    if label ≤ K then rightLengthValue n width label else 2^width - 1
  have hlabels : zeroMapLabels k K = List.range' k source.length := by
    rw [zeroMapLabels_eq_range', hlen]
    congr 1
    omega
  have hdelta : ∀ label ∈ List.range' k source.length,
      rightLengthWriteValue n width K label = f label ^^^ f (label + 1) := by
    intro label hm
    simp only [List.mem_range'] at hm
    have hle : label ≤ K := by omega
    by_cases he : label = K
    · subst label
      simp [rightLengthWriteValue, f]
    · have hlt : label + 1 ≤ K := by omega
      simp [rightLengthWriteValue, he, f, hle, hlt]
  have hbase : f k = rightLengthValue n width k := by simp [f, hkK]
  unfold rightLengthWordAction
  simp only [gateWord, Bool.true_and, List.map_id', gatedXorConstantBits_true]
  rw [hlabels, ← hbase, length_write_congr _ _ _ _ _ hdelta, length_prefix_telescope]
  congr 1
  have hi : source.findIdx id ≤ source.length := List.findIdx_le_length
  by_cases hfind : source.findIdx id < source.length
  · have hle : k + source.findIdx id ≤ K := by omega
    simp [f, hfind, hle]
  · have hgt : ¬k + source.findIdx id ≤ K := by omega
    simp [f, hfind, hgt]


/-- The actual grouped lower writer XORs the first-set-position length encoding,
including the all-zero sentinel case, into an arbitrary target word. -/
theorem rightLengthXorWrite_firstSet
    (n k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) (henabled : state control = true) :
    let source := lowerRangeBits true boundary (zeroMapLabels k K) bitAt state
    wireValues targets
        (run (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) state) =
      xorConstantBits (wireValues targets state)
        (if source.findIdx id < source.length then
          rightLengthValue n targets.length (k + source.findIdx id)
        else 2^targets.length - 1) := by
  dsimp only
  rw [rightLengthXorWrite_wordAction n k K boundary hkK hboundary tree control
    rangeAccumulator temporary path bitAt dirtyAt targets state hlayout hlabels hroute
    hcleanPath hcleanRange hcleanTemporary, henabled]
  apply rightLengthWordAction_firstSet n targets.length k K hkK
  rw [lowerRangeBits_length, zeroMapLabels_eq_range', List.length_range']
  omega

end ShorECDLP.Paper2607_13816
