import ShorECDLP.Submission.«2607_13816».Window.RawEntry
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem first_count (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    ((fourierOutcomes 16).filter (fun bs =>
      ¬reducedRawExclusions P Q hP hQ hrP hrQ
        (phaseWordState (List.range' 855 16) bs s))).length ≤ 112 := by
  let xs := (fourierOutcomes 16).filter (fun bs =>
      ¬reducedRawExclusions P Q hP hQ hrP hrQ
        (phaseWordState (List.range' 855 16) bs s))
  let f (bs : List Bool) : Fin 65536 := ⟨boolWordToNat bs % 65536, Nat.mod_lt _ (by norm_num)⟩
  have hb (bs : List Bool) (h : bs ∈ xs) : bs.length=16 :=
    (fourierOutcomes_mem _ _).mp (List.mem_of_mem_filter h)
  have hv (bs : List Bool) (h : bs ∈ xs) : (f bs).val=boolWordToNat bs := by
    apply Nat.mod_eq_of_lt
    have ht := boolWordToNat_lt_pow_two bs
    simpa [hb bs h] using ht
  have he (bs : List Bool) (h : bs ∈ xs) : constantBits 16 (f bs).val=bs := by
    apply boolWordToNat_injective_of_length (by simp [hb bs h])
    rw [boolWordToNat_constantBits, Nat.mod_eq_of_lt (f bs).isLt, hv bs h]
  have hi : Set.InjOn f (xs.toFinset : Set (List Bool)) := by
    intro a ha b hb' hab
    have ha' := List.mem_toFinset.mp ha
    have hb'' := List.mem_toFinset.mp hb'
    apply boolWordToNat_injective_of_length ((hb a ha').trans (hb b hb'').symm)
    have hh := congrArg Fin.val hab
    simpa only [hv a ha', hv b hb''] using hh
  have hm : Set.MapsTo f (xs.toFinset : Set (List Bool))
      (Finset.univ.filter (fun a : Fin 65536 =>
        ¬reducedRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s))) := by
    intro bs hbs
    have h := List.mem_toFinset.mp hbs
    change f bs ∈ (Finset.univ.filter (fun a : Fin 65536 =>
      ¬reducedRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s)))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [rawFirstWordState, he bs h, decide_eq_true_eq] using (List.mem_filter.mp h).2
  have hc := Finset.card_le_card_of_injOn f hm hi
  have hn : xs.Nodup := (fourierOutcomes_nodup _).filter _
  rw [List.toFinset_card_of_nodup hn] at hc
  exact hc.trans (reducedRawExclusions_firstWord_card P Q hP hQ hrP hrQ s)

private theorem word_update (ws : List Wire) (bs : List Bool) (s : BasisState)
    (q : Wire) (b : Bool) (hq : q∉ws) :
    phaseWordState ws bs (s[q ↦ b]) = (phaseWordState ws bs s)[q ↦ b] := by
  induction ws generalizing bs s with
  | nil => rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons c cs =>
      have hh : q≠w ∧ q∉ws := by simpa only [List.mem_cons,not_or] using hq
      have he : (s[q ↦ b])[w ↦ c]=(s[w ↦ c])[q ↦ b] := by
        funext k
        simp only [upd]
        split_ifs <;> simp_all
      rw [phaseWordState,he,ih cs _ hh.2]
      rfl

private theorem word_commute (ws vs : List Wire) (bs cs : List Bool) (s : BasisState)
    (hd : List.Disjoint ws vs) :
    phaseWordState vs cs (phaseWordState ws bs s)=
      phaseWordState ws bs (phaseWordState vs cs s) := by
  induction ws generalizing bs s with
  | nil => rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      have hh := List.disjoint_cons_left.mp hd
      rw [phaseWordState,ih bs _ hh.2,word_update vs cs s w b hh.1]
      rfl
private theorem outcomes_add (n m : Nat) : fourierOutcomes (n+m)=
    (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a++b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add,fourierOutcomes,ih,List.flatMap_append,List.flatMap_map,
      List.map_flatMap,List.map_map,Function.comp_def,List.cons_append]

private theorem product_filter_swap {α β : Type} (xs : List α) (ys : List β)
    (p : α → β → Bool) :
    (xs.map (fun x => (ys.filter (p x)).length)).sum =
      (ys.map (fun y => (xs.filter (fun x => p x y)).length)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    clear ih
    induction ys with
    | nil => simp
    | cons y ys ihy =>
      cases hp : p x y <;> simp_all [List.filter_cons, Nat.add_assoc, Nat.add_comm] <;> omega

private theorem bounded_sum {α : Type} (xs : List α) (f : α → Nat) (b : Nat)
    (h : ∀ x∈xs, f x≤b) : (xs.map f).sum≤xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    have h1 := h x (by simp)
    have h2 := ih (by intro y hy; exact h y (by simp [hy]))
    omega

/-- The full emitted assignment family inherits the conditional first-window bound. -/
theorem reducedRawExclusions_word_count (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    ((fourierOutcomes 464).filter (fun bs =>
      ¬reducedRawExclusions P Q hP hQ hrP hrQ
        (phaseWordState reducedPhaseWires bs s))).length ≤ 2^448*112 := by
  let ws := List.range' 855 16
  let vs := List.range' 871 240 ++ List.range' 1127 208
  let bad (bs : List Bool) : Bool := decide
    (¬reducedRawExclusions P Q hP hQ hrP hrQ (phaseWordState reducedPhaseWires bs s))
  have hw : reducedPhaseWires=ws++vs := by decide +kernel
  have hd : List.Disjoint ws vs := by
    apply List.disjoint_left.mpr
    intro w hw hv
    simp only [ws,vs,List.mem_append,List.mem_range'_1] at *
    omega
  have hc (cs : List Bool) :
      ((fourierOutcomes 16).filter (fun bs => bad (bs++cs))).length≤112 := by
    have he : (fourierOutcomes 16).filter (fun bs => bad (bs++cs)) =
        (fourierOutcomes 16).filter (fun bs => decide
          (¬reducedRawExclusions P Q hP hQ hrP hrQ
            (phaseWordState ws bs (phaseWordState vs cs s)))) := by
      apply List.filter_congr
      intro bs hbs
      have hl := (fourierOutcomes_mem _ _).mp hbs
      dsimp only [bad]
      rw [hw,phaseWordState_append ws vs bs cs (by simpa [ws] using hl),word_commute ws vs bs cs s hd]
    rw [he]
    exact first_count P Q hP hQ hrP hrQ _
  change ((fourierOutcomes 464).filter bad).length≤_
  rw [show 464=16+448 from rfl,outcomes_add,List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,Function.comp_def,List.length_map]
  rw [product_filter_swap]
  have h := bounded_sum (fourierOutcomes 448)
    (fun cs => ((fourierOutcomes 16).filter (fun bs => bad (bs++cs))).length) 112
    (by intro cs _; exact hc cs)
  simpa only [fourierOutcomes_length] using h

/-- The excluded subspace of the actual root-enabled entry has mass at most 7/4096.
This is an input bound, not yet an output sampling-error bound. -/
theorem reducedRawEntry_excluded_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    normSq (reducedRawEntryState.filter
      (fun s => ¬reducedRawExclusions P Q hP hQ hrP hrQ s)) ≤ (7:ℝ)/4096 := by
  rw [reducedRawEntryState_filtered_mass]
  have hc := reducedRawExclusions_word_count P Q hP hQ hrP hrQ (scalarRootFlip zeroBasisState)
  have hr : (((fourierOutcomes 464).filter (fun bs =>
      ¬reducedRawExclusions P Q hP hQ hrP hrQ
        (phaseWordState reducedPhaseWires bs (scalarRootFlip zeroBasisState)))).length : ℝ) ≤
      (2:ℝ)^448*112 := by exact_mod_cast hc
  calc
    _ ≤ ((2:ℝ)^448*112)/2^464 := div_le_div_of_nonneg_right hr (by positivity)
    _ = 7/4096 := by
      rw [show 464=448+16 from rfl, pow_add, mul_div_mul_left _ _ (by positivity : (2:ℝ)^448≠0)]
      norm_num

end
end ShorECDLP.Paper2607_13816
