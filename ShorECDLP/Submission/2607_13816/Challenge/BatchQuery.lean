import ShorECDLP.Submission.«2607_13816».Challenge.BatchState
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

theorem batchWord_injective (base : Wire) (j : Fin 6) : Function.Injective (batchWord base j) := by
  intro i k h; exact Fin.ext (Nat.add_left_cancel h)

theorem batchWord_pair_injective (base : Wire) :
    Function.Injective (fun p : Fin 5 × Fin 513 => batchWord base p.1.castSucc p.2) := by
  rintro ⟨j,i⟩ ⟨k,l⟩ h
  dsimp [batchWord] at h
  have hj : j.val = k.val := by dsimp only [Wire] at *; omega
  have hi : i.val = l.val := by dsimp only [Wire] at *; omega
  exact Prod.ext (Fin.ext hj) (Fin.ext hi)

theorem batchPorts_nodup {n : Nat} (row : Fin n) (base : Wire) (selection : List (Fin 8 × Fin 5))
    (hn : (selection.map Prod.snd).Nodup) : ((batchPorts row base selection).map Prod.fst).Nodup := by
  simp only [batchPorts,List.map_flatMap,List.map_ofFn,Function.comp_def]
  apply List.nodup_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro p hp
    exact List.nodup_ofFn.mpr (batchWord_injective base _)
  · have hpair := List.pairwise_map.mp hn
    apply hpair.imp
    intro p q hne
    apply List.disjoint_left.mpr
    intro w hp hq
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hp
    obtain ⟨k,hk⟩ := List.mem_ofFn.mp hq
    have he := batchWord_pair_injective base (a₁ := (p.2,i)) (a₂ := (q.2,k)) (hi.trans hk.symm)
    exact hne (congrArg Prod.fst he)

theorem batchTags_nodup (base : Wire) (selection : List (Fin 8 × Fin 5))
    (hn : (selection.map Prod.snd).Nodup) : (batchTags base selection).Nodup := by
  have hf : ((selection.filter (fun p => endpointTagMask p.1 512)).map Prod.snd).Nodup :=
    hn.sublist (List.filter_sublist.map Prod.snd)
  have hm := hf.map (f:=fun j : Fin 5 => batchWord base j.castSucc 512) (by
    intro j k h
    exact congrArg Prod.fst (batchWord_pair_injective base (a₁ := (j,512)) (a₂ := (k,512)) h))
  simpa only [batchTags,List.map_map,Function.comp_def] using hm

theorem batchSelection_nodup (sources : Bool) (target : Fin 4) :
    ((batchSelection sources target).map Prod.snd).Nodup := by
  cases sources <;> simp [batchSelection]

theorem batchPorts_bounds {n : Nat} (row : Fin n) (base w : Wire)
    (selection : List (Fin 8 × Fin 5)) (hw : w ∈ (batchPorts row base selection).map Prod.fst) :
    base ≤ w ∧ w < base+2565 := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
  obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hp
  cases hi
  dsimp [batchWord]
  dsimp only [Wire] at *
  omega

theorem batchTags_bounds (base w : Wire) (selection : List (Fin 8 × Fin 5))
    (hw : w ∈ batchTags base selection) : base ≤ w ∧ w < base+2565 := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
  dsimp [batchWord]
  dsimp only [Wire] at *
  omega

theorem batchRawMask_outside {n : Nat} (read : ConstantBit n → Bool) (row : Fin n)
    (base w : Wire) (selection : List (Fin 8 × Fin 5)) (hw : w < base ∨ base+2565 ≤ w) :
    w ∉ endpointRawMask read (batchPorts row base selection) := by
  intro h
  obtain ⟨p,hp,he⟩ := List.mem_map.mp h
  have hb := batchPorts_bounds row base w selection (List.mem_map.mpr ⟨p,(List.mem_filter.mp hp).1,he⟩)
  dsimp only [Wire] at *; omega

theorem batchTags_outside (base w : Wire) (selection : List (Fin 8 × Fin 5))
    (hw : w < base ∨ base+2565 ≤ w) : w ∉ batchTags base selection := by
  intro h
  have hb := batchTags_bounds base w selection h
  dsimp only [Wire] at *; omega

theorem batchQuery_coherent {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (selection : List (Fin 8 × Fin 5)) (hn : (selection.map Prod.snd).Nodup)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+2565 ≤ w) :
    CoherentlyImplementsOn
      (unaryAction .inc (fun l q => batchLeafCircuit read (rows l) base q selection) tree control paths)
      (Quantum.run (unaryActionUnitary .inc
        (fun l q => batchLeafCircuit read (rows l) base q selection) tree control paths)) (Clean paths) := by
  apply endpointXorPair_coherent _ _ _ _ _ hl
  · intro l; exact endpointRawMask_nodup _ _ (batchPorts_nodup _ _ _ hn)
  · intro l; split <;> simp [batchTags_nodup base selection hn]
  · intro l w hw; exact batchRawMask_outside _ _ _ _ _ (hd w hw)
  · intro l w hw; split
    · exact batchTags_outside _ _ _ (hd w hw)
    · simp
theorem batchRawMask_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (selection : List (Fin 8 × Fin 5))
    (hn : (selection.map Prod.snd).Nodup) (p : Fin 8 × Fin 5) (hp : p ∈ selection) (i : Fin 513) :
    decide (batchWord base p.2.castSucc i ∈ endpointRawMask (readConstant coeffs Q)
      (batchPorts row base selection)) = readEndpointWords coeffs Q row p.1 i := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  apply endpointRawMask_mem _ _ (batchPorts_nodup row base selection hn)
  exact List.mem_flatMap.mpr ⟨p,hp,List.mem_ofFn.mpr ⟨i,rfl⟩⟩

theorem batchTags_word (base : Wire) (selection : List (Fin 8 × Fin 5))
    (hn : (selection.map Prod.snd).Nodup) (p : Fin 8 × Fin 5) (hp : p ∈ selection) (i : Fin 513) :
    decide (batchWord base p.2.castSucc i ∈ batchTags base selection) = endpointTagMask p.1 i := by
  by_cases hi : i = 512
  · subst i
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro hm
      obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
      have hs := (List.mem_filter.mp hq).1
      have hw := batchWord_pair_injective base (a₁ := (q.2,512)) (a₂ := (p.2,512)) he
      have hh : q = p := List.inj_on_of_nodup_map hn hs hp (congrArg Prod.fst hw)
      simpa [hh] using (List.mem_filter.mp hq).2
    · intro hm
      exact List.mem_map.mpr ⟨p,List.mem_filter.mpr ⟨hp,hm⟩,rfl⟩
  · have hval : i.val ≠ 512 := fun h => hi (Fin.ext h)
    have hm : batchWord base p.2.castSucc i ∉ batchTags base selection := by
      intro h
      obtain ⟨q,hq,he⟩ := List.mem_map.mp h
      have hw := batchWord_pair_injective base (a₁ := (q.2,512)) (a₂ := (p.2,i)) he
      exact hi (congrArg Prod.snd hw).symm
    simp [hm,endpointTagMask,hval]

theorem batchQuery_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (selection : List (Fin 8 × Fin 5)) (hn : (selection.map Prod.snd).Nodup)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+2565 ≤ w)
    (s : BasisState) (hc : Clean paths s) (p : Fin 8 × Fin 5) (hp : p ∈ selection) (i : Fin 513) :
    Classical.run (unaryActionUnitary .inc
      (fun l q => batchLeafCircuit (readConstant coeffs Q) (rows l) base q selection) tree control paths)
      s (batchWord base p.2.castSucc i) =
      xor (s (batchWord base p.2.castSucc i))
        (s control && normalizedEndpointWords coeffs Q (rows (tree.routeLabel s)) p.1 i) := by
  rw [show (fun l q => batchLeafCircuit (readConstant coeffs Q) (rows l) base q selection) =
    (fun l q => tableXorGates q (endpointRawMask (readConstant coeffs Q) (batchPorts (rows l) base selection)) ++
      tableXorGates q (if readConstant coeffs Q ⟨rows l,.infinity,0⟩ then batchTags base selection else [])) from rfl]
  rw [endpointXorPair_run _ _ tree control paths hl
    (fun l => endpointRawMask_nodup _ _ (batchPorts_nodup _ _ _ hn))
    (by intro l; split <;> simp [batchTags_nodup base selection hn])
    (by intro l w hw; exact batchRawMask_outside _ _ _ _ _ (hd w hw))
    (by intro l w hw; split; exact batchTags_outside _ _ _ (hd w hw); simp) s hc]
  simp only [tableXorState, batchRawMask_word coeffs Q _ base selection hn p hp i,normalizedEndpointWords]
  cases h : readConstant coeffs Q ⟨rows (tree.routeLabel s),.infinity,0⟩ <;>
    simp only [Bool.false_eq_true,if_false,List.not_mem_nil,decide_false,if_true,
      batchTags_word base selection hn p hp i,Bool.and_false,Bool.and_true,Bool.xor_false]
  cases s (batchWord base p.2.castSucc i) <;> cases s control <;>
    cases readEndpointWords coeffs Q (rows (tree.routeLabel s)) p.1 i <;> cases endpointTagMask p.1 i <;> rfl

theorem batchWord_apart (base : Wire) (j k : Fin 6) (hne : j ≠ k) (a b : Fin 513) :
    batchWord base j a ≠ batchWord base k b := by
  have h : j.val ≠ k.val := fun h => hne (Fin.ext h)
  dsimp [batchWord]; dsimp only [Wire] at *; omega

theorem batchWord_bound (base : Wire) (j : Fin 6) (i : Fin 513) :
    batchWord base j i < batchFlag base := by
  dsimp [batchWord,batchFlag]; dsimp only [Wire] at *; omega

theorem batchScratch_above (base w : Wire) (hw : w ∈ batchScratch base) : batchFlag base < w := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  dsimp [batchFlag]; dsimp only [Wire]; omega

theorem batchWord_layout (base : Wire) (j : Fin 6) :
    EqConstLayout (List.ofFn (batchWord base j)) (batchFlag base) (batchScratch base) := by
  refine ⟨?_,?_⟩
  · simp only [List.length_ofFn,batchScratch]; decide
  · apply List.nodup_append.mpr
    refine ⟨List.nodup_ofFn.mpr (batchWord_injective base j),?_,?_⟩
    · apply List.nodup_cons.mpr
      refine ⟨?_,List.nodup_ofFn.mpr ?_⟩
      · intro h; exact (Nat.lt_irrefl _) (batchScratch_above base _ h)
      · intro i k h; exact Fin.ext (Nat.add_left_cancel h)
    · intro w hw v hv he
      subst v
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      rcases List.mem_cons.mp hv with he | ht
      · exact (Nat.ne_of_lt (batchWord_bound base j i)) he
      · exact Nat.lt_asymm (batchScratch_above base _ ht) (batchWord_bound base j i)

theorem batchSwap_geometry (base : Wire) (source : Fin 4) (target : Fin 6)
    (hs : source.val ≠ target.val) (ht : target ≠ 4) :
    EndpointGeometry (batchWord base ⟨source.val,by omega⟩) (batchWord base 4)
      (batchWord base target) (batchFlag base) (batchScratch base) := by
  refine ⟨batchWord_injective base _,?_,?_,batchWord_layout base _,?_⟩
  · intro i j
    exact ⟨batchWord_apart base _ _ (fun h => hs (congrArg Fin.val h)) i j,
      batchWord_apart base _ _ ht.symm i j⟩
  · intro i
    exact ⟨(Nat.ne_of_lt (batchWord_bound base _ i)).symm,
      (Nat.ne_of_lt (batchWord_bound base _ i)).symm,(Nat.ne_of_lt (batchWord_bound base _ i)).symm⟩
  · intro w hw i
    have h := batchScratch_above base w hw
    exact ⟨(Nat.ne_of_lt ((batchWord_bound base _ i).trans h)).symm,
      (Nat.ne_of_lt ((batchWord_bound base _ i).trans h)).symm,
      (Nat.ne_of_lt ((batchWord_bound base _ i).trans h)).symm⟩

attribute [local irreducible] endpointTranspositionCircuit

theorem batchOpCircuit_model (base : Wire) (source : Fin 4) (target : Fin 6)
    (hs : source.val ≠ target.val) (ht : target ≠ 4) (st : BasisState)
    (hc : Clean (batchScratch base) st) (hz : st (batchFlag base) = false) :
    let out := Classical.run (batchOpCircuit base source target) st
    (∀ j, out ∘ batchWord base j = batchSwap source target (fun k => st ∘ batchWord base k) j) ∧
      Clean (batchScratch base) out ∧ out (batchFlag base) = false ∧
      (∀ w, (∀ i, w ≠ batchWord base target i) → out w = st w) := by
  dsimp only
  unfold batchOpCircuit
  have h := endpointTransposition_correct _ _ _ _ _ (batchSwap_geometry base source target hs ht) st hc hz
  refine ⟨?_,?_,h.2.1,h.2.2⟩
  · intro j
    by_cases hj : j = target
    · subst j; simpa [batchSwap,Function.update] using h.1
    · simp only [batchSwap,Function.update_of_ne hj]
      funext i
      exact h.2.2 _ (fun k => batchWord_apart base j target hj i k)
  · intro w hw
    rw [h.2.2 w (fun i => (batchSwap_geometry base source target hs ht).scratchApart w hw i |>.2.2)]
    exact hc w hw

theorem batchRawMask_frame {n : Nat} (read : ConstantBit n → Bool) (row : Fin n)
    (base w : Wire) (selection : List (Fin 8 × Fin 5))
    (hw : ∀ p ∈ selection, ∀ i, w ≠ batchWord base p.2.castSucc i) :
    w ∉ endpointRawMask read (batchPorts row base selection) := by
  intro h
  obtain ⟨p,hp,he⟩ := List.mem_map.mp h
  obtain ⟨q,hq,hi⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hi
  cases hi
  exact hw q hq i he.symm

theorem batchTags_frame (base w : Wire) (selection : List (Fin 8 × Fin 5))
    (hw : ∀ p ∈ selection, ∀ i, w ≠ batchWord base p.2.castSucc i) : w ∉ batchTags base selection := by
  intro h
  obtain ⟨p,hp,he⟩ := List.mem_map.mp h
  exact hw p (List.mem_filter.mp hp).1 512 he.symm

theorem batchQuery_frame {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (selection : List (Fin 8 × Fin 5)) (hn : (selection.map Prod.snd).Nodup)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+2565 ≤ w)
    (s : BasisState) (hc : Clean paths s) (w : Wire)
    (hw : ∀ p ∈ selection, ∀ i, w ≠ batchWord base p.2.castSucc i) :
    Classical.run (unaryActionUnitary .inc
      (fun l q => batchLeafCircuit read (rows l) base q selection) tree control paths) s w = s w := by
  exact endpointXorPair_frame _ _ tree control paths hl
    (fun l => endpointRawMask_nodup _ _ (batchPorts_nodup _ _ _ hn))
    (by intro l; split <;> simp [batchTags_nodup base selection hn])
    (by intro l v hv; exact batchRawMask_outside _ _ _ _ _ (hd v hv))
    (by intro l v hv; split; exact batchTags_outside _ _ _ (hd v hv); simp) s hc w
    (fun l => batchRawMask_frame _ _ _ _ _ hw)
    (by intro l; split; exact batchTags_frame _ _ _ hw; simp)

theorem batchQuery_model {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (sources : Bool) (target : Fin 4) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+2565 ≤ w)
    (s : BasisState) (hc : Clean paths s) (hq : s control = true) (j : Fin 6) :
    (Classical.run (unaryActionUnitary .inc
      (fun l q => batchLeafCircuit (readConstant coeffs Q) (rows l) base q (batchSelection sources target))
      tree control paths) s) ∘ batchWord base j =
    batchLoad (normalizedEndpointWords coeffs Q (rows (tree.routeLabel s))) sources target
      (fun k => s ∘ batchWord base k) j := by
  have hw (p : Fin 8 × Fin 5) (hp : p ∈ batchSelection sources target) (i : Fin 513) :=
    batchQuery_word coeffs Q rows base tree control paths _ (batchSelection_nodup sources target)
      hl hd s hc p hp i
  have hf (j : Fin 6) (hjs : ∀ p ∈ batchSelection sources target, j ≠ p.2.castSucc) (i : Fin 513) :=
    batchQuery_frame (readConstant coeffs Q) rows base tree control paths _
      (batchSelection_nodup sources target) hl hd s hc (batchWord base j i)
      (fun p hp k => batchWord_apart base j p.2.castSucc (hjs p hp) i k)
  funext i
  by_cases hj : j.val < 4
  · cases sources with
    | false =>
      have hframe := hf j (by
        intro p hp
        simp only [batchSelection,Bool.false_eq_true,ite_false,List.nil_append,List.mem_singleton] at hp
        subst p
        intro h; have he := congrArg Fin.val h; simp only [Fin.val_castSucc] at he; omega) i
      simpa [batchLoad,hj] using hframe
    | true =>
      let p : Fin 8 × Fin 5 := (⟨j.val,by omega⟩,⟨j.val,by omega⟩)
      have hp : p ∈ batchSelection true target := by
        have hj' : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by omega
        rcases hj' with h | h | h | h <;> simp [p,batchSelection,Fin.ext_iff,h]
      have hword := hw p hp i
      simpa [batchLoad,hj,p,hq,Function.comp_def] using hword
  · by_cases he : j = 4
    · subst j
      let p : Fin 8 × Fin 5 := (⟨4+target.val,by omega⟩,4)
      have hword := hw p (by simp [p,batchSelection]) i
      simpa [batchLoad,p,hq,Function.comp_def] using hword
    · have hv : j.val=5 := by have := j.isLt; have : j.val ≠ 4 := fun h => he (Fin.ext h); omega
      have hframe := hf j (by
        intro p hp h
        have heq := congrArg Fin.val h
        have := p.2.isLt
        simp only [Fin.val_castSucc] at heq
        omega) i
      simpa [batchLoad,hj,he] using hframe

end ShorECDLP.Paper2607_13816.ChallengeMigration
