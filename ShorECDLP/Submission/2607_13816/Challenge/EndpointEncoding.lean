import ShorECDLP.Submission.«2607_13816».Challenge.EndpointLoad
import ShorECDLP.Submission.«2607_13816».Challenge.MatchingPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

def coordinateWordBits (v : Bool × (Fp × Fp)) (i : Fin 513) : Bool :=
  if i.val < 256 then v.2.1.val.testBit i.val
  else if i.val < 512 then v.2.2.val.testBit (i.val-256)
  else v.1

theorem coordinateWordBits_injective : Function.Injective coordinateWordBits := by
  intro a b h
  have ht := congrFun h (512 : Fin 513)
  have hx : a.2.1.val = b.2.1.val := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 256
    · have hh := congrFun h (⟨i, by omega⟩ : Fin 513)
      simpa [coordinateWordBits, hi] using hh
    · have ha : a.2.1.val < 2^i := (ZMod.val_lt _).trans_le
        (show p ≤ 2^i from (by
          have hp : p < 2^256 := by decide
          exact hp.le.trans (Nat.pow_le_pow_right (by decide) (by omega))))
      have hb : b.2.1.val < 2^i := (ZMod.val_lt _).trans_le
        (show p ≤ 2^i from (by
          have hp : p < 2^256 := by decide
          exact hp.le.trans (Nat.pow_le_pow_right (by decide) (by omega))))
      rw [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]
  have hy : a.2.2.val = b.2.2.val := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 256
    · have hh := congrFun h (⟨i+256, by omega⟩ : Fin 513)
      have h1 : ¬ i+256 < 256 := by omega
      have h2 : i+256 < 512 := by omega
      simpa [coordinateWordBits, h1, h2] using hh
    · have ha : a.2.2.val < 2^i := (ZMod.val_lt _).trans_le
        (show p ≤ 2^i from (by
          have hp : p < 2^256 := by decide
          exact hp.le.trans (Nat.pow_le_pow_right (by decide) (by omega))))
      have hb : b.2.2.val < 2^i := (ZMod.val_lt _).trans_le
        (show p ≤ 2^i from (by
          have hp : p < 2^256 := by decide
          exact hp.le.trans (Nat.pow_le_pow_right (by decide) (by omega))))
      rw [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]
  exact Prod.ext (by simpa [coordinateWordBits] using ht)
    (Prod.ext (ZMod.val_injective p hx) (ZMod.val_injective p hy))

theorem coordinateWordBits_swap (a b x : Bool × (Fp × Fp)) :
    Equiv.swap (coordinateWordBits a) (coordinateWordBits b) (coordinateWordBits x) =
      coordinateWordBits (Equiv.swap a b x) := by
  classical
  by_cases ha : x = a
  · subst x; simp
  by_cases hb : x = b
  · subst x; simp
  rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha (coordinateWordBits_injective h))
    (fun h => hb (coordinateWordBits_injective h)), Equiv.swap_apply_of_ne_of_ne ha hb]

theorem coordinateWordBits_matching (ps : List ((Bool × (Fp × Fp)) × (Bool × (Fp × Fp))))
    (x : Bool × (Fp × Fp)) :
    finiteMatchingPermutation (ps.map (fun p => (coordinateWordBits p.1, coordinateWordBits p.2)))
      (coordinateWordBits x) = coordinateWordBits (finiteMatchingPermutation ps x) := by
  classical
  induction ps generalizing x with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, finiteMatchingPermutation, Equiv.trans_apply, ih,
      coordinateWordBits_swap]

theorem coordinateFieldValue_lt (P : Point) (f : PointField) : fieldValue P f < p := by
  have hp : 1 < p := by decide
  cases f <;> simp only [fieldValue]
  all_goals first | exact ZMod.val_lt _ | split <;> omega

theorem endpointFieldWord_read {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (tag : EndpointBit n) (fx fy : Option PointField) (i : Fin 513) :
    EndpointBit.read (readConstant coeffs Q) (endpointFieldWord row tag fx fy i) =
      coordinateWordBits
        (EndpointBit.read (readConstant coeffs Q) tag,
          (fx.map (fun f => (fieldValue (constantPoint Q (coeffs row)) f : Fp))).getD 0,
          (fy.map (fun f => (fieldValue (constantPoint Q (coeffs row)) f : Fp))).getD 0) i := by
  have hf (f : PointField) :
      (fieldValue (constantPoint Q (coeffs row)) f : Fp).val =
        fieldValue (constantPoint Q (coeffs row)) f := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (coordinateFieldValue_lt _ _)]
  by_cases hx : i.val < 256
  · cases fx <;> simp [endpointFieldWord, coordinateWordBits, hx,
      EndpointBit.read, readConstant, hf]
  · by_cases hy : i.val < 512
    · cases fy <;> simp [endpointFieldWord, coordinateWordBits, hx, hy,
        EndpointBit.read, readConstant, hf]
    · simp [endpointFieldWord, coordinateWordBits, hx, hy]

theorem doubleInfinity_bit (P : Point) :
    (fieldValue P .doubleInfinity).testBit 0 = decide (fieldValue P .doubleInfinity = 1) := by
  simp only [fieldValue, doubledCoordinates]
  by_cases h : (pointCoordinates (P+P)).1 = true <;> simp [h]

noncomputable def readEndpointWords {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (row : Fin n)
    (j : Fin 8) : Fin 513 → Bool :=
  fun i => EndpointBit.read (readConstant coeffs Q) (exceptionalEndpointWords row j i)

theorem readEndpointWords_pairs {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) :
    let a := readEndpointWords coeffs Q row;
    [(a 0,a 4),(a 1,a 5),(a 2,a 6),(a 3,a 7)] =
      (protectedExceptionPairs (constantPoint Q (coeffs row))).map
        (fun p => (coordinateWordBits p.1, coordinateWordBits p.2)) := by
  dsimp only
  unfold readEndpointWords
  simp [exceptionalEndpointWords, protectedExceptionPairs]
  simp_rw [endpointFieldWord_read]
  simp only [EndpointBit.read, readConstant, Option.map_some,
    Option.getD_some, Option.map_none, Option.getD_none, exceptionFieldCoordinates]
  simp only [Fin.val_zero, doubleInfinity_bit]
  simp


theorem readEndpointWords_correct {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) (P : Point) :
    let a := readEndpointWords coeffs Q row;
    runFiniteSwaps (finiteMatchingSwaps [(a 0,a 4),(a 1,a 5),(a 2,a 6),(a 3,a 7)])
      (coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P))) =
      coordinateWordBits (fig14PointEncoding (P + .some hC)) := by
  classical
  dsimp only
  rw [readEndpointWords_pairs, finiteMatchingSwaps_apply, coordinateWordBits_matching, hrow]
  have h := protectedExceptionPairs_correct hC P
  rw [finiteMatchingSwaps_apply] at h
  rw [h]

def endpointRows (base : Wire) (j : Fin 8) : Fin 513 → Wire :=
  matchingRows base ⟨j.val, by omega⟩

theorem endpointPortWires {n : Nat} (row : Fin n) (base : Wire) :
    (exceptionalEndpointPorts row (endpointRows base)).map Prod.fst =
      List.ofFn (fun i : Fin 4104 => base + i.val) := by
  simp only [exceptionalEndpointPorts, List.map_flatten, List.map_ofFn, Function.comp_def]
  rw [List.ofFn_mul' (m := 513) (n := 8)]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext i
  simp [endpointRows, matchingRows, Nat.add_assoc]

theorem endpointPortWires_nodup {n : Nat} (row : Fin n) (base : Wire) :
    ((exceptionalEndpointPorts row (endpointRows base)).map Prod.fst).Nodup := by
  rw [endpointPortWires]
  apply List.nodup_ofFn.mpr
  intro i j h
  exact Fin.ext (Nat.add_left_cancel h)

noncomputable def endpointValues {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) : List (Wire × Bool) :=
  (exceptionalEndpointPorts row (endpointRows base)).map
    (fun p => (p.1, EndpointBit.read (readConstant coeffs Q) p.2))

theorem endpointValues_wires {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) :
    (endpointValues coeffs Q row base).map Prod.fst =
      List.ofFn (fun i : Fin 4104 => base + i.val) := by
  rw [endpointValues, List.map_map]
  exact endpointPortWires row base

theorem endpointValues_mem {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (j : Fin 8) (i : Fin 513) :
    (endpointRows base j i, readEndpointWords coeffs Q row j i) ∈
      endpointValues coeffs Q row base := by
  apply List.mem_map.mpr
  refine ⟨(endpointRows base j i, exceptionalEndpointWords row j i), ?_, rfl⟩
  apply List.mem_flatten.mpr
  refine ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩

theorem endpointValues_nodup {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) :
    ((endpointValues coeffs Q row base).map Prod.fst).Nodup := by
  rw [endpointValues_wires]
  exact List.nodup_ofFn.mpr (fun i j h => Fin.ext (Nat.add_left_cancel h))

theorem endpointLoad_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (st : BasisState)
    (hz : ∀ j i, st (endpointRows base j i) = false) (j : Fin 8) :
    Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base j =
      readEndpointWords coeffs Q row j := by
  funext i
  rw [Function.comp_apply, bitLoadCircuit_value _ (endpointValues_nodup _ _ _ _) _ _ _
    (endpointValues_mem coeffs Q row base j i), hz]
  simp


theorem endpointLoad_frame_above {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (st : BasisState) (w : Wire) (hw : base+4104 ≤ w) :
    Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st w = st w := by
  apply bitLoadCircuit_frame
  rw [endpointValues_wires]
  intro h
  obtain ⟨i, he⟩ := List.mem_ofFn.mp h
  simp only [Wire] at *
  omega

/-- A semantic instance of the fixed protected loads and the value-independent network. -/
noncomputable def loadedMatchingCircuit {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) : Circuit :=
  let load := bitLoadCircuit (endpointValues coeffs Q row base)
  load ++ matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base) ++ load

/-- Unloading restores every loaded wire whenever the middle circuit preserves it. -/
theorem bitLoad_sandwich_restore (ps : List (Wire × Bool))
    (hn : (ps.map Prod.fst).Nodup) (middle : Circuit) (st : BasisState)
    (hm : ∀ w ∈ ps.map Prod.fst,
      Classical.run middle (Classical.run (bitLoadCircuit ps) st) w =
        Classical.run (bitLoadCircuit ps) st w) :
    ∀ w ∈ ps.map Prod.fst,
      Classical.run (bitLoadCircuit ps ++ middle ++ bitLoadCircuit ps) st w = st w := by
  intro w hw
  obtain ⟨⟨v,b⟩, hp, he⟩ := List.mem_map.mp hw
  change v = w at he
  subst v
  simp only [Classical.run_append]
  rw [bitLoadCircuit_value ps hn _ w b hp, hm w hw, bitLoadCircuit_value ps hn st w b hp]
  cases st w <;> cases b <;> rfl

theorem bitLoad_sandwich_outside (ps : List (Wire × Bool))
    (middle : Circuit) (st : BasisState) (w : Wire) (hw : w ∉ ps.map Prod.fst) :
    Classical.run (bitLoadCircuit ps ++ middle ++ bitLoadCircuit ps) st w =
      Classical.run middle (Classical.run (bitLoadCircuit ps) st) w := by
  simp only [Classical.run_append]
  exact bitLoadCircuit_frame ps _ w hw

theorem bitLoad_matching_correct {n : Nat} (ps : List (Wire × Bool))
    (hn : (ps.map Prod.fst).Nodup) (rows : MatchingSlot → Fin n → Wire)
    (flag : Wire) (scratch : List Wire)
    (geometries : ∀ m ∈ matchingNetwork,
      EndpointGeometry (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch)
    (apart : ∀ i j, i ≠ j → ∀ k l, rows i k ≠ rows j l)
    (hports : ∀ w ∈ ps.map Prod.fst, ∃ j, j ≠ 8 ∧ ∃ i, w = rows j i)
    (hdata : ∀ i, rows 8 i ∉ ps.map Prod.fst)
    (st : BasisState)
    (hc : Clean scratch (Classical.run (bitLoadCircuit ps) st))
    (hz : Classical.run (bitLoadCircuit ps) st flag = false) :
    let ready := Classical.run (bitLoadCircuit ps) st;
    let out := Classical.run (bitLoadCircuit ps ++ matchingCircuit rows flag scratch ++ bitLoadCircuit ps) st;
    out ∘ rows 8 = runFiniteSwaps (finiteMatchingSwaps
      [(ready ∘ rows 0,ready ∘ rows 4),(ready ∘ rows 1,ready ∘ rows 5),
       (ready ∘ rows 2,ready ∘ rows 6),(ready ∘ rows 3,ready ∘ rows 7)]) (st ∘ rows 8) ∧
    (∀ w ∈ ps.map Prod.fst, out w = st w) := by
  have h := matchingCircuit_correct rows flag scratch geometries apart
    (Classical.run (bitLoadCircuit ps) st) hc hz
  have ht : Classical.run (bitLoadCircuit ps) st ∘ rows 8 = st ∘ rows 8 :=
    funext (fun i => bitLoadCircuit_frame ps st (rows 8 i) (hdata i))
  have ho : Classical.run (bitLoadCircuit ps ++ matchingCircuit rows flag scratch ++ bitLoadCircuit ps) st ∘ rows 8 =
      Classical.run (matchingCircuit rows flag scratch) (Classical.run (bitLoadCircuit ps) st) ∘ rows 8 :=
    funext (fun i => bitLoad_sandwich_outside ps _ st (rows 8 i) (hdata i))
  refine ⟨ho.trans ?_, bitLoad_sandwich_restore ps hn _ st ?_⟩
  · simpa only [ht] using h.1
  · intro w hw
    obtain ⟨j,hj,i,rfl⟩ := hports w hw
    exact congrFun (h.2.1 j hj) i


theorem endpointValues_ports {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (w : Wire)
    (hw : w ∈ (endpointValues coeffs Q row base).map Prod.fst) :
    ∃ j : MatchingSlot, j ≠ 8 ∧ ∃ i : Fin 513, w = matchingRows base j i := by
  rw [endpointValues_wires] at hw
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
  have hj : k.val / 513 < 8 := by omega
  refine ⟨⟨k.val / 513, by omega⟩, ?_, ⟨k.val % 513, Nat.mod_lt _ (by decide)⟩, ?_⟩
  · intro he
    have hv : k.val / 513 = 8 := congrArg Fin.val he
    omega
  · simp only [matchingRows]
    have hm := Nat.mod_add_div k.val 513
    simp only [Wire] at *
    omega

theorem endpointValues_outside {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (w : Wire) (hw : base+4104 ≤ w) :
    w ∉ (endpointValues coeffs Q row base).map Prod.fst := by
  rw [endpointValues_wires]
  intro h
  obtain ⟨i, he⟩ := List.mem_ofFn.mp h
  simp only [Wire] at *
  omega

theorem loadedMatching_data {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (st : BasisState)
    (he : ∀ j i, st (endpointRows base j i) = false)
    (hs : Clean (matchingScratch base) st) (hf : st (matchingFlag base) = false) :
    let a := readEndpointWords coeffs Q row;
    Classical.run (loadedMatchingCircuit coeffs Q row base) st ∘ matchingRows base 8 =
      runFiniteSwaps (finiteMatchingSwaps [(a 0,a 4),(a 1,a 5),(a 2,a 6),(a 3,a 7)])
        (st ∘ matchingRows base 8) ∧
    (∀ w ∈ (endpointValues coeffs Q row base).map Prod.fst,
      Classical.run (loadedMatchingCircuit coeffs Q row base) st w = st w) := by
  have hfb : base+4104 ≤ matchingFlag base := by simp [matchingFlag]
  have hc : Clean (matchingScratch base)
      (Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st) := by
    intro w hw
    rw [endpointLoad_frame_above coeffs Q row base st w
      (hfb.trans (matchingScratch_above base w hw).le)]
    exact hs w hw
  have hz : Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st
      (matchingFlag base) = false := by
    rw [endpointLoad_frame_above coeffs Q row base st _ hfb, hf]
  have h := bitLoad_matching_correct (endpointValues coeffs Q row base)
    (endpointValues_nodup coeffs Q row base) (matchingRows base) (matchingFlag base)
    (matchingScratch base) (matchingNetwork_geometry base) (matchingRows_apart base)
    (endpointValues_ports coeffs Q row base)
    (fun i => endpointValues_outside coeffs Q row base _ (by simp [matchingRows])) st hc hz
  have hwords := endpointLoad_word coeffs Q row base st he
  refine ⟨?_, h.2⟩
  have hd := h.1
  change Classical.run (loadedMatchingCircuit coeffs Q row base) st ∘ matchingRows base 8 =
    runFiniteSwaps (finiteMatchingSwaps
      [(Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base 0,
        Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base 4),
       (Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base 1,
        Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base 5),
       (Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base 2,
        Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base 6),
       (Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base 3,
        Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st ∘ endpointRows base 7)])
      (st ∘ matchingRows base 8) at hd
  simpa only [hwords] using hd


theorem matchingCircuit_frame {n : Nat}
    (rows : MatchingSlot → Fin n → Wire) (flag : Wire) (scratch : List Wire)
    (geometries : ∀ m ∈ matchingNetwork,
      EndpointGeometry (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch)
    (apart : ∀ i j, i ≠ j → ∀ k l, rows i k ≠ rows j l)
    (st : BasisState) (hc : Clean scratch st) (hz : st flag = false)
    (w : Wire) (hw : ∀ i, w ≠ rows 8 i) :
    Classical.run (matchingCircuit rows flag scratch) st w = st w := by
  have h := matchingCircuit_correct rows flag scratch geometries apart st hc hz
  by_cases hr : ∃ j i, w = rows j i
  · obtain ⟨j,i,rfl⟩ := hr
    have hj : j ≠ 8 := by intro he; subst j; exact hw i rfl
    exact congrFun (h.2.1 j hj) i
  · exact h.2.2.2.2 w (by simpa using hr)

theorem bitLoad_matching_frame {n : Nat} (ps : List (Wire × Bool))
    (hn : (ps.map Prod.fst).Nodup) (rows : MatchingSlot → Fin n → Wire)
    (flag : Wire) (scratch : List Wire)
    (geometries : ∀ m ∈ matchingNetwork,
      EndpointGeometry (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch)
    (apart : ∀ i j, i ≠ j → ∀ k l, rows i k ≠ rows j l)
    (hports : ∀ w ∈ ps.map Prod.fst, ∀ i, w ≠ rows 8 i)
    (st : BasisState)
    (hc : Clean scratch (Classical.run (bitLoadCircuit ps) st))
    (hz : Classical.run (bitLoadCircuit ps) st flag = false)
    (w : Wire) (hw : ∀ i, w ≠ rows 8 i) :
    Classical.run (bitLoadCircuit ps ++ matchingCircuit rows flag scratch ++ bitLoadCircuit ps) st w = st w := by
  have hm := matchingCircuit_frame rows flag scratch geometries apart
    (Classical.run (bitLoadCircuit ps) st) hc hz
  by_cases hp : w ∈ ps.map Prod.fst
  · exact bitLoad_sandwich_restore ps hn _ st (fun v hv => hm v (hports v hv)) w hp
  · rw [bitLoad_sandwich_outside ps _ st w hp, hm w hw, bitLoadCircuit_frame ps st w hp]

theorem loadedMatching_frame {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (st : BasisState)
    (hs : Clean (matchingScratch base) st) (hf : st (matchingFlag base) = false)
    (w : Wire) (hw : ∀ i, w ≠ matchingRows base 8 i) :
    Classical.run (loadedMatchingCircuit coeffs Q row base) st w = st w := by
  have hfb : base+4104 ≤ matchingFlag base := by simp [matchingFlag]
  have hc : Clean (matchingScratch base)
      (Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st) := by
    intro v hv
    rw [endpointLoad_frame_above coeffs Q row base st v
      (hfb.trans (matchingScratch_above base v hv).le)]
    exact hs v hv
  have hz : Classical.run (bitLoadCircuit (endpointValues coeffs Q row base)) st
      (matchingFlag base) = false := by
    rw [endpointLoad_frame_above coeffs Q row base st _ hfb, hf]
  apply bitLoad_matching_frame _ (endpointValues_nodup coeffs Q row base)
    (matchingRows base) (matchingFlag base) (matchingScratch base)
    (matchingNetwork_geometry base) (matchingRows_apart base) ?_ st hc hz w hw
  intro v hv i he
  exact endpointValues_outside coeffs Q row base (matchingRows base 8 i)
    (by simp [matchingRows]) (he ▸ hv)

theorem loadedMatching_point {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (st : BasisState)
    (he : ∀ j i, st (endpointRows base j i) = false)
    (hs : Clean (matchingScratch base) st) (hf : st (matchingFlag base) = false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) (P : Point)
    (hin : st ∘ matchingRows base 8 = coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P))) :
    Classical.run (loadedMatchingCircuit coeffs Q row base) st ∘ matchingRows base 8 =
      coordinateWordBits (fig14PointEncoding (P + .some hC)) := by
  have h := (loadedMatching_data coeffs Q row base st he hs hf).1
  rw [hin] at h
  exact h.trans (readEndpointWords_correct coeffs Q row hC hrow P)


def loadedMatchingGates {n : Nat} (row : Fin n) (base : Wire) : List (TemplateGate n) :=
  let load := endpointLoadGates (exceptionalEndpointPorts row (endpointRows base))
  load ++ (matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base)).map
    (fun g => .whenBit ⟨row, .infinity, 0⟩ false g) ++ load

theorem guardedCircuit_instantiate {n : Nat} (read : ConstantBit n → Bool)
    (ref : ConstantBit n) (c : Circuit) :
    (c.map (fun g => TemplateGate.whenBit ref false g)).flatMap (TemplateGate.instantiate read) =
      if read ref then [] else c := by
  induction c with
  | nil => cases read ref <;> rfl
  | cons g gs ih => cases h : read ref <;>
      simp [List.map_cons, List.flatMap_cons, TemplateGate.instantiate, h, ih]

theorem loadedMatchingGates_finite {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) :
    (loadedMatchingGates row base).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      loadedMatchingCircuit coeffs Q row base := by
  simp only [loadedMatchingGates, List.flatMap_append, endpointLoadGates_instantiate,
    guardedCircuit_instantiate]
  have hr : readConstant coeffs Q ⟨row, .infinity, 0⟩ = false := by
    simp only [readConstant, hrow, fieldValue, pointCoordinates]
    rfl
  rw [hr]
  rfl

theorem loadedMatchingGates_infinity {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (hrow : constantPoint Q (coeffs row) = 0) (st : BasisState) :
    Classical.run ((loadedMatchingGates row base).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q))) st = st := by
  simp only [loadedMatchingGates, List.flatMap_append, endpointLoadGates_instantiate,
    guardedCircuit_instantiate]
  have hr : readConstant coeffs Q ⟨row, .infinity, 0⟩ = true := by
    simp only [readConstant, hrow, fieldValue, pointCoordinates]
    rfl
  rw [hr]
  simp only [↓reduceIte, List.append_nil, Classical.run_append]
  exact bitLoadCircuit_involutive (endpointValues coeffs Q row base)
    (endpointValues_nodup coeffs Q row base) st

theorem bitLoadCircuit_HPFree (ps : List (Wire × Bool)) : Classical.HPFree (bitLoadCircuit ps) := by
  induction ps with
  | nil => exact Classical.hpFree_nil
  | cons p ps ih =>
    rcases p with ⟨w,b⟩
    cases b <;> simp [bitLoadCircuit, Classical.hpFree_cons, Classical.IsClassicalGate, ih]

theorem loadedMatchingCircuit_quantum {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (st : BasisState) :
    Quantum.run (loadedMatchingCircuit coeffs Q row base) (ket st) =
      ket (Classical.run (loadedMatchingCircuit coeffs Q row base) st) := by
  apply Quantum.run_ket_agrees_classical
  simp only [loadedMatchingCircuit, Classical.hpFree_append, bitLoadCircuit_HPFree,
    matchingCircuit, matchingMovesCircuit_HPFree, and_self]


theorem endpointLoadGates_wellFormed {n : Nat} (ports : List (Wire × EndpointBit n)) :
    ∀ g ∈ endpointLoadGates ports, g.WellFormed := by
  intro g hg
  obtain ⟨p,hp,hg⟩ := List.mem_flatMap.mp hg
  rcases p with ⟨w,b⟩
  cases b with
  | inl b =>
    cases b <;> simp only [endpointLoadGate, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst g
    trivial
  | inr r =>
    simp only [endpointLoadGate, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst g
    trivial

theorem loadedMatchingGates_wellFormed {n : Nat} (row : Fin n) (base : Wire) :
    ∀ g ∈ loadedMatchingGates row base, g.WellFormed := by
  intro g hg
  simp only [loadedMatchingGates, List.mem_append] at hg
  rcases hg with (hl | hm) | hl
  · exact endpointLoadGates_wellFormed _ g hl
  · obtain ⟨gate,hgate,rfl⟩ := List.mem_map.mp hm
    exact matchingCircuit_wellFormed _ _ _ (matchingNetwork_geometry base) gate hgate
  · exact endpointLoadGates_wellFormed _ g hl

/-- A zero-measurement fixed straight program; infinity bypasses the matching network. -/
def loadedMatchingProgram {n : Nat} (row : Fin n) (base : Wire) (cursor : Nat) :
    Straight n cursor cursor := gateProgram (loadedMatchingGates row base)

theorem gateProgram_wellFormed {n cursor : Nat} (gs : List (TemplateGate n))
    (h : ∀ g ∈ gs, g.WellFormed) : (gateProgram (cursor := cursor) gs).WellFormed := by
  induction gs with
  | nil => trivial
  | cons g gs ih =>
    exact ⟨h g (by simp), ih (fun g hg => h g (by simp [hg]))⟩

-- Keep elaboration from expanding the large fixed list while applying generic lemmas.
attribute [local irreducible] loadedMatchingGates

theorem loadedMatchingProgram_wellFormed {n : Nat} (row : Fin n) (base : Wire) (cursor : Nat) :
    (loadedMatchingProgram row base cursor).WellFormed := by
  have h := @gateProgram_wellFormed n cursor (@loadedMatchingGates n row base)
    (@loadedMatchingGates_wellFormed n row base)
  have e : loadedMatchingProgram row base cursor = gateProgram (cursor := cursor) (loadedMatchingGates row base) := rfl
  exact Eq.mpr (congrArg (fun p : Straight n cursor cursor => p.WellFormed) e) h

theorem loadedMatchingProgram_finite {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (cursor : Nat) (history : Fin cursor → Bool)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) :
    ((loadedMatchingProgram row base cursor).instantiate (readConstant coeffs Q) history).run =
      (AdaptiveCircuit.unitary (loadedMatchingCircuit coeffs Q row base) .done).run := by
  rw [loadedMatchingProgram, gateProgram_run, loadedMatchingGates_finite coeffs Q row base hC hrow]


theorem loadedMatchingGates_HPFree {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) :
    Classical.HPFree ((loadedMatchingGates row base).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q))) := by
  simp only [loadedMatchingGates, List.flatMap_append, endpointLoadGates_instantiate,
    guardedCircuit_instantiate, Classical.hpFree_append, bitLoadCircuit_HPFree]
  split
  · simp [Classical.hpFree_nil]
  · simp only [matchingCircuit, matchingMovesCircuit_HPFree, and_self]

theorem loadedMatchingGates_infinity_quantum {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (hrow : constantPoint Q (coeffs row) = 0) (st : BasisState) :
    Quantum.run ((loadedMatchingGates row base).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q))) (ket st) = ket st := by
  rw [Quantum.run_ket_agrees_classical _ _ (loadedMatchingGates_HPFree coeffs Q row base),
    loadedMatchingGates_infinity coeffs Q row base hrow st]

theorem loadedMatchingProgram_measurements {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (cursor : Nat) (history : Fin cursor → Bool) :
    ((loadedMatchingProgram row base cursor).instantiate (readConstant coeffs Q) history).measurementCount = 0 := by
  rw [Straight.measurementCount, Nat.sub_self]
end ShorECDLP.Paper2607_13816.ChallengeMigration
