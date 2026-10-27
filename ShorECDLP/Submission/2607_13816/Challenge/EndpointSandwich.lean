import ShorECDLP.Submission.«2607_13816».Challenge.EndpointQROM
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

/-- A middle operation may change data, but cannot change the selected table row. -/
theorem endpointXorPair_sandwich (a b : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (ha : ∀ l, (a l).Nodup) (hb : ∀ l, (b l).Nodup)
    (hda : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ a l)
    (hdb : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ b l)
    (middle : Circuit) (s : BasisState) (hc : Clean paths s)
    (hm : ∀ w ∈ control::tree.indexWires.dedup++paths,
      Classical.run middle (Classical.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s) w =
      Classical.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s w) :
    let load := unaryActionUnitary .inc
      (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths
    Classical.run (load ++ middle ++ load) s =
      tableXorState (b (tree.routeLabel s)) (s control)
        (tableXorState (a (tree.routeLabel s)) (s control)
          (Classical.run middle (Classical.run load s))) := by
  dsimp only
  let load := unaryActionUnitary .inc
    (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths
  let ready := Classical.run load s
  let changed := Classical.run middle ready
  have hf (w : Wire) (hw : w ∈ control::tree.indexWires.dedup++paths) : changed w = s w := by
    exact (hm w hw).trans (endpointXorPair_frame a b tree control paths hl ha hb hda hdb s hc w
      (fun l => hda l w hw) (fun l => hdb l w hw))
  have hclean : Clean paths changed := by
    intro w hw
    rw [hf w (by simp [hw])]
    exact hc w hw
  have hr : tree.routeLabel changed = tree.routeLabel s := by
    apply UnaryActionTree.routeLabel_congr
    intro w hw
    exact hf w (by simp [hw])
  have hcontrol : changed control = s control := hf control (by simp)
  simp only [Classical.run_append]
  change Classical.run load changed = _
  rw [endpointXorPair_run a b tree control paths hl ha hb hda hdb changed hclean,hr,hcontrol]


theorem endpointXorPair_sandwich_outside (a b : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (ha : ∀ l, (a l).Nodup) (hb : ∀ l, (b l).Nodup)
    (hda : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ a l)
    (hdb : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ b l)
    (middle : Circuit) (s : BasisState) (hc : Clean paths s)
    (hm : ∀ w ∈ control::tree.indexWires.dedup++paths,
      Classical.run middle (Classical.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s) w =
      Classical.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s w)
    (w : Wire) (hwa : ∀ l, w ∉ a l) (hwb : ∀ l, w ∉ b l) :
    let load := unaryActionUnitary .inc
      (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths
    Classical.run (load ++ middle ++ load) s w = Classical.run middle (Classical.run load s) w := by
  dsimp only
  rw [endpointXorPair_sandwich a b tree control paths hl ha hb hda hdb middle s hc hm,
    tableXorState_outside _ _ _ w (hwb _),tableXorState_outside _ _ _ w (hwa _)]

theorem endpointXorPair_sandwich_restore (a b : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (ha : ∀ l, (a l).Nodup) (hb : ∀ l, (b l).Nodup)
    (hda : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ a l)
    (hdb : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ b l)
    (middle : Circuit) (s : BasisState) (hc : Clean paths s)
    (hm : ∀ w ∈ control::tree.indexWires.dedup++paths,
      Classical.run middle (Classical.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s) w =
      Classical.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s w)
    (w : Wire)
    (hw : Classical.run middle (Classical.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s) w =
      Classical.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s w) :
    let load := unaryActionUnitary .inc
      (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths
    Classical.run (load ++ middle ++ load) s w = s w := by
  dsimp only
  rw [endpointXorPair_sandwich a b tree control paths hl ha hb hda hdb middle s hc hm]
  simp only [tableXorState,hw]
  rw [endpointXorPair_run a b tree control paths hl ha hb hda hdb s hc]
  simp only [tableXorState]
  cases s w <;> cases s control <;> cases decide (w ∈ a (tree.routeLabel s)) <;>
    cases decide (w ∈ b (tree.routeLabel s)) <;> rfl

theorem normalizedEndpointWords_correct {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (row : Fin n) {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) (P : Point) :
    let a := normalizedEndpointWords coeffs Q row;
    runFiniteSwaps (finiteMatchingSwaps [(a 0,a 4),(a 1,a 5),(a 2,a 6),(a 3,a 7)])
      (coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P))) =
      coordinateWordBits (fig14PointEncoding (P + .some hC)) := by
  dsimp only
  simp only [normalizedEndpointWords_finite coeffs Q row hC hrow]
  exact readEndpointWords_correct coeffs Q row hC hrow P

theorem normalizedEndpointWords_zero_action {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (row : Fin n) (hrow : constantPoint Q (coeffs row) = 0)
    (word : Fin 513 → Bool) :
    let a := normalizedEndpointWords coeffs Q row;
    runFiniteSwaps (finiteMatchingSwaps [(a 0,a 4),(a 1,a 5),(a 2,a 6),(a 3,a 7)]) word = word := by
  classical
  dsimp only
  simp only [normalizedEndpointWords_infinity coeffs Q row hrow,finiteMatchingSwaps_apply]
  simp [finiteMatchingPermutation]

noncomputable def endpointQuery {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) : Circuit :=
  unaryActionUnitary .inc
    (fun l q => endpointLookupLeafCircuit (readConstant coeffs Q) (rows l) base q) tree control paths

theorem endpointQuery_frame {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (s : BasisState) (hc : Clean paths s) (w : Wire) (hw : w < base ∨ base+4104 ≤ w) :
    Classical.run (endpointQuery coeffs Q rows base tree control paths) s w = s w := by
  apply endpointXorPair_frame _ _ tree control paths hl
    (fun l => endpointRawMask_nodup _ _ (endpointPortWires_nodup _ _))
    (by intro l; split <;> simp [endpointTagWires_nodup])
    (by intro l w hw; exact endpointRawMask_outside _ _ _ _ (hd w hw))
    (by intro l w hw; split; exact endpointTagWires_outside _ _ (hd w hw); simp) s hc w
  · intro l
    exact endpointRawMask_outside _ _ _ _ hw
  · intro l
    dsimp only
    split
    · exact endpointTagWires_outside _ _ hw
    · simp

theorem endpointQuery_ready {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (s : BasisState) (hc : Clean paths s) (hon : s control = true)
    (hz : ∀ j i, s (endpointRows base j i) = false) (j : Fin 8) :
    Classical.run (endpointQuery coeffs Q rows base tree control paths) s ∘ endpointRows base j =
      normalizedEndpointWords coeffs Q (rows (tree.routeLabel s)) j := by
  funext i
  change Classical.run (endpointQuery coeffs Q rows base tree control paths) s (endpointRows base j i) = _
  unfold endpointQuery
  rw [endpointLookup_word coeffs Q rows base tree control paths hl hd s hc j i,hon,hz j i]
  simp

theorem endpointQuery_matching_data {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (s : BasisState) (hc : Clean paths s) (hon : s control = true)
    (hz : ∀ j i, s (endpointRows base j i) = false)
    (hs : Clean (matchingScratch base) s) (hf : s (matchingFlag base) = false) :
    let ready := Classical.run (endpointQuery coeffs Q rows base tree control paths) s
    let a := normalizedEndpointWords coeffs Q (rows (tree.routeLabel s))
    Classical.run (matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base))
      ready ∘ matchingRows base 8 =
      runFiniteSwaps (finiteMatchingSwaps [(a 0,a 4),(a 1,a 5),(a 2,a 6),(a 3,a 7)])
        (s ∘ matchingRows base 8) := by
  dsimp only
  let ready := Classical.run (endpointQuery coeffs Q rows base tree control paths) s
  have hclean : Clean (matchingScratch base) ready := by
    intro w hw
    have hb := matchingScratch_above base w hw
    dsimp only [ready]
    rw [endpointQuery_frame coeffs Q rows base tree control paths hl hd s hc w
      (Or.inr (by simp only [matchingFlag,Wire] at *; omega))]
    exact hs w hw
  have hflag : ready (matchingFlag base) = false := by
    dsimp only [ready]
    rw [endpointQuery_frame coeffs Q rows base tree control paths hl hd s hc _
      (Or.inr (by change (base + 4104 : Nat) ≤ base + 4617; simp only [Wire] at *; omega)),hf]
  have hdata : ready ∘ matchingRows base 8 = s ∘ matchingRows base 8 := by
    funext i
    exact endpointQuery_frame coeffs Q rows base tree control paths hl hd s hc _
      (Or.inr (by simp [matchingRows]))
  have hout := (matchingCircuit_correct (matchingRows base) (matchingFlag base) (matchingScratch base)
    (matchingNetwork_geometry base) (matchingRows_apart base) ready hclean hflag).1
  have hwords (j : Fin 8) : ready ∘ endpointRows base j =
      normalizedEndpointWords coeffs Q (rows (tree.routeLabel s)) j :=
    endpointQuery_ready coeffs Q rows base tree control paths hl hd s hc hon hz j
  have h0 := hwords 0
  have h1 := hwords 1
  have h2 := hwords 2
  have h3 := hwords 3
  have h4 := hwords 4
  have h5 := hwords 5
  have h6 := hwords 6
  have h7 := hwords 7
  change ready ∘ matchingRows base 0 = _ at h0
  change ready ∘ matchingRows base 1 = _ at h1
  change ready ∘ matchingRows base 2 = _ at h2
  change ready ∘ matchingRows base 3 = _ at h3
  change ready ∘ matchingRows base 4 = _ at h4
  change ready ∘ matchingRows base 5 = _ at h5
  change ready ∘ matchingRows base 6 = _ at h6
  change ready ∘ matchingRows base 7 = _ at h7
  rw [h0,h1,h2,h3,h4,h5,h6,h7,hdata] at hout
  exact hout

noncomputable def endpointQueryMatching {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) : Circuit :=
  let load := endpointQuery coeffs Q rows base tree control paths
  load ++ matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base) ++ load

theorem endpointQueryMatching_frame {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (hdata : ∀ w ∈ control::tree.indexWires.dedup++paths, ∀ i, w ≠ matchingRows base 8 i)
    (s : BasisState) (hc : Clean paths s)
    (hs : Clean (matchingScratch base) (Classical.run (endpointQuery coeffs Q rows base tree control paths) s))
    (hf : Classical.run (endpointQuery coeffs Q rows base tree control paths) s (matchingFlag base) = false)
    (w : Wire) (hw : ∀ i, w ≠ matchingRows base 8 i) :
    Classical.run (endpointQueryMatching coeffs Q rows base tree control paths) s w = s w := by
  have hm := matchingCircuit_frame (matchingRows base) (matchingFlag base) (matchingScratch base)
    (matchingNetwork_geometry base) (matchingRows_apart base)
    (Classical.run (endpointQuery coeffs Q rows base tree control paths) s) hs hf
  apply endpointXorPair_sandwich_restore _ _ tree control paths hl
    (fun l => endpointRawMask_nodup _ _ (endpointPortWires_nodup _ _))
    (by intro l; split <;> simp [endpointTagWires_nodup])
    (by intro l w hw; exact endpointRawMask_outside _ _ _ _ (hd w hw))
    (by intro l w hw; split; exact endpointTagWires_outside _ _ (hd w hw); simp)
    _ s hc (fun v hv => hm v (hdata v hv)) w (hm w hw)

theorem endpointQuery_sandwich_outside {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (middle : Circuit) (s : BasisState) (hc : Clean paths s)
    (hm : ∀ v ∈ control::tree.indexWires.dedup++paths,
      Classical.run middle (Classical.run (endpointQuery coeffs Q rows base tree control paths) s) v =
      Classical.run (endpointQuery coeffs Q rows base tree control paths) s v)
    (w : Wire) (hw : w < base ∨ base+4104 ≤ w) :
    let load := endpointQuery coeffs Q rows base tree control paths
    Classical.run (load ++ middle ++ load) s w = Classical.run middle (Classical.run load s) w := by
  apply endpointXorPair_sandwich_outside _ _ tree control paths hl
    (fun l => endpointRawMask_nodup _ _ (endpointPortWires_nodup _ _))
    (by intro l; split <;> simp [endpointTagWires_nodup])
    (by intro l w hw; exact endpointRawMask_outside _ _ _ _ (hd w hw))
    (by intro l w hw; split; exact endpointTagWires_outside _ _ (hd w hw); simp)
    middle s hc hm w
  · intro l
    exact endpointRawMask_outside _ _ _ _ hw
  · intro l
    split
    · exact endpointTagWires_outside _ _ hw
    · simp

theorem endpointQuery_sandwich_data {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (middle : Circuit) (s : BasisState) (hc : Clean paths s)
    (hm : ∀ v ∈ control::tree.indexWires.dedup++paths,
      Classical.run middle (Classical.run (endpointQuery coeffs Q rows base tree control paths) s) v =
      Classical.run (endpointQuery coeffs Q rows base tree control paths) s v) :
    let load := endpointQuery coeffs Q rows base tree control paths
    Classical.run (load ++ middle ++ load) s ∘ matchingRows base 8 =
      Classical.run middle (Classical.run load s) ∘ matchingRows base 8 := by
  funext i
  exact endpointQuery_sandwich_outside coeffs Q rows base tree control paths hl hd middle s hc hm
    (matchingRows base 8 i) (Or.inr (by simp [matchingRows]))

theorem endpointQueryMatching_data_after {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (hdata : ∀ w ∈ control::tree.indexWires.dedup++paths, ∀ i, w ≠ matchingRows base 8 i)
    (s : BasisState) (hc : Clean paths s)
    (hs : Clean (matchingScratch base) (Classical.run (endpointQuery coeffs Q rows base tree control paths) s))
    (hf : Classical.run (endpointQuery coeffs Q rows base tree control paths) s (matchingFlag base) = false) :
    Classical.run (endpointQueryMatching coeffs Q rows base tree control paths) s ∘ matchingRows base 8 =
      Classical.run (matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base))
        (Classical.run (endpointQuery coeffs Q rows base tree control paths) s) ∘ matchingRows base 8 := by
  have hm := matchingCircuit_frame (matchingRows base) (matchingFlag base) (matchingScratch base)
    (matchingNetwork_geometry base) (matchingRows_apart base)
    (Classical.run (endpointQuery coeffs Q rows base tree control paths) s) hs hf
  exact endpointQuery_sandwich_data coeffs Q rows base tree control paths hl hd
    (matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base)) s hc
    (fun v hv => hm v (hdata v hv))

end ShorECDLP.Paper2607_13816.ChallengeMigration
