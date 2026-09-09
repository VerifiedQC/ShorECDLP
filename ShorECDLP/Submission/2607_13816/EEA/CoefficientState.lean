import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPhase
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem low_truthMinusOne (small large value : Nat) (hp : 0 < small) (hl : small ≤ large) :
    truthMinusOneValue large value % 2^small = truthMinusOneValue small value := by
  have hm : 1 < 2^small := Nat.one_lt_two_pow (by omega)
  have hM : 1 < 2^large := Nat.one_lt_two_pow (by omega)
  have hd : 2^small ∣ 2^large := pow_dvd_pow 2 hl
  change ((value+2^large-1%2^large)%2^large)%2^small = (value+2^small-1%2^small)%2^small
  rw [Nat.mod_eq_of_lt hM,Nat.mod_eq_of_lt hm,Nat.mod_mod_of_dvd _ hd]
  rw [Nat.add_sub_assoc (by omega : 1 ≤ 2^large), Nat.add_sub_assoc (by omega : 1 ≤ 2^small)]
  have he : Nat.ModEq (2^small) (2^large) (2^small) := by
    change 2^large % 2^small = 2^small % 2^small
    rw [Nat.mod_eq_zero_of_dvd hd,Nat.mod_self]
  exact (Nat.ModEq.refl value).add (Nat.ModEq.sub_right (by omega) (by omega) he)
private theorem packed_low_metadata (r : IndexedStepRegisters) (n index value : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index)
    (hs : boolWordToNat (wireValues r.lengthS s) = truthMinusOneValue r.lengthS.length value) :
    boolWordToNat (wireValues r.tBoundary.lengthSLow s) = truthMinusOneValue r.lengthT.length value := by
  have ht := boolWordToNat_slice (wireValues r.lengthS s) 0 r.lengthT.length
    (by simpa only [Nat.zero_add,wireValues,List.length_map] using h.tBoundary.lengthS_capacity)
  simp only [List.drop_zero,Nat.pow_zero,Nat.div_one] at ht
  change boolWordToNat (wireValues (r.lengthS.take r.lengthT.length) s) = _
  rw [wireValues, List.map_take]
  change boolWordToNat ((wireValues r.lengthS s).take r.lengthT.length) = _
  rw [ht,hs]
  exact low_truthMinusOne _ _ _ h.tBoundary.positive h.tBoundary.lengthS_capacity

private theorem packed_regroup_disjoint (a b c d e : List Wire)
    (h : (a++(b++(c++(d++e)))).Nodup) :
    List.Disjoint (a++c++e) (d++b) := by
  obtain ⟨_,hrest,ha⟩ := List.nodup_append.mp h
  obtain ⟨_,hrest,hb⟩ := List.nodup_append.mp hrest
  obtain ⟨_,hrest,hc⟩ := List.nodup_append.mp hrest
  obtain ⟨_,_,hd⟩ := List.nodup_append.mp hrest
  apply List.disjoint_left.mpr
  intro w hw hn
  simp only [List.mem_append] at hw hn
  rcases hw with (hw | hw) | hw <;> rcases hn with hn | hn
  · exact ha w hw w (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hn))) rfl
  · exact ha w hw w (List.mem_append_left _ hn) rfl
  · exact hc w hw w (List.mem_append_left _ hn) rfl
  · exact hb w hn w (List.mem_append_left _ hw) rfl
  · exact hd w hn w hw rfl
  · exact hb w hn w (List.mem_append_right _ (List.mem_append_right _ hw)) rfl

/-- Physical interpretation of a logical packed EEA state. Capacity and active-window
bounds are separate arithmetic invariants; every auxiliary wire is clean. -/
structure IndexedPackedState (r : IndexedStepRegisters) (n : Nat) (s : BasisState)
    (v : EEAState) : Prop where
  work1 : wireValues r.work1 s = constantBits v.lT v.t ++ [false] ++
    (constantBits v.lQ v.q).reverse ++ (constantBits (n+3-(v.lT+v.lQ+1)) v.r).reverse
  work2 : wireValues r.work2 s = (constantBits (n+3-v.lRPrime) v.tPrime ++
    (constantBits v.lRPrime v.rPrime).reverse).rotate v.shift
  lengthT : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthT.length v.lT
  lengthQ : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length v.lQ
  lengthRP : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthRPrime.length v.lRPrime
  lengthS : boolWordToNat (wireValues r.lengthS s) = truthMinusOneValue r.lengthS.length v.shift
  phase1 : s r.phase1 = v.phase.bits.1
  phase2 : s r.phase2 = v.phase.bits.2
  sign : s r.sign = v.sign
  iter : s r.iter = v.iter
  clean : Clean r.aux s

/-- One coefficient microstep on the unweighted quotient prefix carried by Work1. -/
def coefficientMicrostep (v : EEAState) : EEAState :=
  let switch := decide (v.lQ=1) && !decide (v.lRPrime=0)
  { v with
    q := v.q / 2
    lQ := v.lQ - 1
    shift := v.shift + 1
    tPrime := if v.q.testBit 0 then v.tPrime + 2^v.shift*v.t else v.tPrime
    phase := if switch then .swap else .coefficient
    sign := switch }

/-- The complete actual coefficient circuit preserves the packed-state interpretation
and the strict bound and weighted conservation law needed by phase iteration. -/
theorem indexedStepUnitary_coefficient_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase = .coefficient)
    (hsign : v.sign = false) (hQ : 0 < v.lQ)
    (hqfit : v.lT+v.lQ+1 < 2^r.lengthQ.length)
    (hqlo : (certifiedActiveWindows n index).quotientSwap.start ≤ v.lT+v.lQ+1)
    (hqhi : v.lT+v.lQ+1 ≤ (certifiedActiveWindows n index).quotientSwap.stop)
    (hthi : v.lT+1 < 2^r.lengthT.length)
    (hlo : v.lRPrime+v.shift ≤ n+3)
    (hhi : n+3-v.lRPrime-v.shift < 2^r.lengthT.length)
    (hv : v.lT+1 ∈ quotientSwapLabels 1 (certifiedActiveWindows n index).coefficient.stop)
    (ht : v.t < 2^v.lT) (htp : v.tPrime < 2^(n+3-v.lRPrime))
    (hspan : v.shift+(v.lT+1) ≤ n+3-v.lRPrime)
    (hbound : v.tPrime < 2^v.shift*v.t)
    (hquot : v.q < 2^v.lQ) (hrem : v.r < 2^(n+3-(v.lT+v.lQ+1)))
    (hswidth : 0 < r.lengthS.length) (hsinc : v.shift+1 < 2^r.lengthS.length)
    (hrpfit : v.lRPrime < 2^r.lengthRPrime.length) :
    let next := coefficientMicrostep v
    IndexedPackedState r n (run (indexedStepUnitary r n index) s) next ∧
    next.q < 2^next.lQ ∧ next.tPrime < 2^(n+3-next.lRPrime) ∧
    next.tPrime < 2^next.shift*next.t ∧
    next.tPrime+2^next.shift*next.t*next.q = v.tPrime+2^v.shift*v.t*v.q := by
  have hp1 : s r.phase1 = true := by simpa [hphase,EEAPhase.bits] using hp.phase1
  have hp2 : s r.phase2 = false := by simpa [hphase,EEAPhase.bits] using hp.phase2
  have hsg : s r.sign = false := hp.sign.trans hsign
  have hrmeta : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthT.length v.lRPrime := by
    have hw : r.lengthRPrime.length = r.lengthT.length := h.tBoundary.lengthRP_length
    simpa only [hw] using hp.lengthRP
  have hsmeta := packed_low_metadata r n index v.shift s h hp.lengthS
  have hg := indexedStepUnitary_coefficientPhase r n index s v h hp.clean hp1 hp2 hsg hQ
    hp.lengthT hp.lengthQ hrmeta hsmeta hqfit hqlo hqhi hthi hlo hhi hv ht htp hspan
    hbound hquot hrem hp.work1 hp.work2 hp.lengthS hswidth hsinc hrpfit
  obtain ⟨hd1,hd2,hdQ,hdS,_,hdq,hdFit,_,hdBound,hdSum,hdFrame⟩ :=
    blockDEFForward_completeCoefficient r n index s v h hp.clean hp1 hp2 hsg hQ
      hp.lengthT hp.lengthQ hrmeta hsmeta hqfit hqlo hqhi hthi hlo hhi hv ht htp hspan
      hbound hquot hrem hp.work1 hp.work2 hp.lengthS hswidth hsinc
  let mid := run (blockDForward r (certifiedActiveWindows n index).quotientSwap ++
    blockEForward r n (certifiedActiveWindows n index).coefficient ++ blockFForward r) s
  let out := run (indexedStepUnitary r n index) s
  let switch := decide (v.lQ=1) && !decide (v.lRPrime=0)
  change out = mid[r.phase2 ↦ switch][r.sign ↦ switch] ∧ _ at hg
  have hsep := packed_regroup_disjoint [r.phase1,r.phase2,r.iter] (r.sign :: r.work1 ++ r.work2)
    r.lengthT (r.lengthQ ++ r.lengthS) (r.lengthRPrime ++ r.aux)
    (by simpa only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] using h.physical)
  have hstable : ∀ wire ∈ [r.phase1,r.phase2,r.iter] ++ r.lengthT ++ (r.lengthRPrime ++ r.aux),
      mid wire = s wire := by
    intro wire hw
    apply hdFrame wire
    have hn := List.disjoint_left.mp hsep hw
    intro hm
    apply hn
    simp only [List.mem_append] at hm ⊢
    rcases hm with (hm | hm) | hm
    · exact Or.inl (Or.inl hm)
    · exact Or.inr hm
    · exact Or.inl (Or.inr hm)
  have phys := h.physical
  simp only [IndexedStepRegisters.allWires,List.cons_append,List.nil_append,List.nodup_cons] at phys
  have hread (ws : List Wire)
      (hws : ∀ wire ∈ ws, wire ∈ r.work1 ++ r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux) :
      wireValues ws out = wireValues ws mid := by
    apply List.map_congr_left
    intro wire hw
    have hm := hws wire hw
    have h2 : wire ≠ r.phase2 := by intro he; subst wire; exact phys.2.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
    have hsg : wire ≠ r.sign := by intro he; subst wire; exact phys.2.2.2.1 hm
    rw [hg.1]
    simp only [upd_other _ _ _ hsg,upd_other _ _ _ h2]
  have hmeta (ws : List Wire)
      (hws : ∀ wire ∈ ws, wire ∈ r.lengthT ++ r.lengthRPrime ++ r.aux) :
      wireValues ws out = wireValues ws s := by
    rw [hread ws (by
      intro wire hw
      have hm := hws wire hw
      simp only [List.mem_append] at hm
      rcases hm with (hm | hm) | hm <;> simp [hm])]
    apply List.map_congr_left
    intro wire hw
    apply hstable wire
    have hm := hws wire hw
    simpa only [List.append_assoc,List.mem_append] using Or.inr hm
  have hp1mid : mid r.phase1 = true := (hstable _ (by simp)).trans hp1
  have hiter : mid r.iter = v.iter := (hstable _ (by simp)).trans hp.iter
  have hp1ne2 : r.phase1 ≠ r.phase2 := by intro he; exact phys.1 (by simp [he])
  have hp1nesg : r.phase1 ≠ r.sign := by intro he; exact phys.1 (by simp [he])
  have hp2nesg : r.phase2 ≠ r.sign := by intro he; exact phys.2.1 (by simp [he])
  have hitne2 : r.iter ≠ r.phase2 := by intro he; exact phys.2.1 (by simp [← he])
  have hitnesg : r.iter ≠ r.sign := by intro he; exact phys.2.2.1 (by simp [he])
  refine ⟨?_,hdq,hdFit,hdBound,hdSum⟩
  constructor
  · change wireValues r.work1 out = _
    rw [hread r.work1 (by intro w hw; simp [hw])]
    exact hd1
  · change wireValues r.work2 out = _
    rw [hread r.work2 (by intro w hw; simp [hw])]
    exact hd2
  · change boolWordToNat (wireValues r.lengthT out) = _
    rw [hmeta r.lengthT (by intro w hw; simp [hw])]
    exact hp.lengthT
  · change boolWordToNat (wireValues r.lengthQ out) = _
    rw [hread r.lengthQ (by intro w hw; simp [hw]),hdQ,boolWordToNat_constantBits]
    exact Nat.mod_mod _ _
  · change boolWordToNat (wireValues r.lengthRPrime out) = _
    rw [hmeta r.lengthRPrime (by intro w hw; simp [hw])]
    exact hp.lengthRP
  · change boolWordToNat (wireValues r.lengthS out) = _
    rw [hread r.lengthS (by intro w hw; simp [hw])]
    exact hdS
  · change out r.phase1 = _
    rw [hg.1]
    simp only [upd_other _ _ _ hp1nesg,upd_other _ _ _ hp1ne2,hp1mid]
    change true = (if switch then EEAPhase.swap else .coefficient).bits.1
    cases switch <;> rfl
  · change out r.phase2 = _
    rw [hg.1]
    simp only [upd_other _ _ _ hp2nesg,upd_same]
    change switch = (if switch then EEAPhase.swap else .coefficient).bits.2
    cases switch <;> rfl
  · change out r.sign = _
    rw [hg.1,upd_same]
    rfl
  · change out r.iter = _
    rw [hg.1]
    simp only [upd_other _ _ _ hitnesg,upd_other _ _ _ hitne2,hiter]
    rfl
  · intro wire hw
    have he : out wire = s wire := by
      have hm : wire ∈ r.work1 ++ r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux := by simp [hw]
      have h2 : wire ≠ r.phase2 := by intro he; subst wire; exact phys.2.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
      have hsg : wire ≠ r.sign := by intro he; subst wire; exact phys.2.2.2.1 hm
      rw [hg.1]
      simp only [upd_other _ _ _ hsg,upd_other _ _ _ h2]
      exact hstable wire (by simp [hw])
    exact he.trans (hp.clean wire hw)
/-- Pure nonfinal swap microstep, before the bank-swap boundary. -/
def swapInteriorMicrostep (v : EEAState) : EEAState :=
  { v with
    shift := v.shift-1
    phase := if v.sign ^^ decide (v.t*2^v.shift ≤ v.tPrime) then .swap else .coefficient
    sign := false }

/-- The complete nonfinal swap circuit preserves the packed logical-state
interpretation, including all metadata and the entire clean auxiliary bank. -/
theorem indexedStepUnitary_swap_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase = .swap) (hQ : v.lQ = 0)
    (hthi : v.lT+1 < 2^r.lengthT.length) (hspan : v.lT+1+v.lRPrime ≤ n+3)
    (hshift : 1 < v.shift) (hlo : v.lRPrime+v.shift ≤ n+3)
    (hhi : n+3-v.lRPrime-v.shift < 2^r.lengthT.length)
    (hv : n+3-v.lRPrime-v.shift ∈ quotientSwapLabels 1 (certifiedActiveWindows n index).coefficient.stop)
    (ht : v.t < 2^v.lT) (htB : v.t < 2^(n+3-v.lRPrime-v.shift))
    (htp : v.tPrime < 2^(n+3-v.lRPrime)) (hrem : v.r < 2^v.lRPrime)
    (hswidth : 0 < r.lengthS.length) (hsfit : v.shift < 2^r.lengthS.length)
    (hR : 0 < v.lRPrime) (hrfit : v.lRPrime < 2^r.lengthRPrime.length) :
    IndexedPackedState r n (run (indexedStepUnitary r n index) s) (swapInteriorMicrostep v) := by
  let cw := (certifiedActiveWindows n index).coefficient
  let mid := run (blockEForward r n cw ++ blockFForward r) s
  let out := run (indexedStepUnitary r n index) s
  let comparison := v.sign ^^ decide (v.t*2^v.shift ≤ v.tPrime)
  have hp1 : s r.phase1 = true := by simpa [hphase,EEAPhase.bits] using hp.phase1
  have hp2 : s r.phase2 = true := by simpa [hphase,EEAPhase.bits] using hp.phase2
  have hrmeta : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthT.length v.lRPrime := by
    have hw : r.lengthRPrime.length = r.lengthT.length := h.tBoundary.lengthRP_length
    simpa only [hw] using hp.lengthRP
  have hsmeta := packed_low_metadata r n index v.shift s h hp.lengthS
  have hqmeta : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length 0 := by
    simpa only [hQ] using hp.lengthQ
  have hwork1 : wireValues r.work1 s = constantBits v.lT v.t ++ [false] ++
      (constantBits (n+3-(v.lT+1)) v.r).reverse := by
    simpa only [hQ,constantBits,List.replicate_zero,xorConstantBits,List.reverse_nil,List.append_nil,Nat.add_zero] using hp.work1
  have hr : IndexedStepReady r s := by
    intro wire hm
    apply hp.clean wire
    simp only [IndexedStepRegisters.sharedScratch,List.mem_cons,List.mem_append] at hm
    rcases hm with he | he | he
    · subst wire
      change r.aux.getD 0 0 ∈ r.aux
      rw [List.getD_eq_getElem _ _ (by rw [h.aux_length]; decide)]
      exact List.getElem_mem _
    · exact List.mem_of_mem_take (List.mem_of_mem_drop he)
    · exact List.mem_of_mem_drop he
  have hg := indexedStepUnitary_swapPhase r n index cw s v h rfl hp.clean hp1 hp2
    hp.lengthT hrmeta hsmeta hthi hspan hshift hlo hhi hv ht htB htp hrem
    hp.lengthS hswidth hsfit hqmeta hR hrfit hwork1 hp.work2
  rw [hp.sign] at hg
  change out = mid[r.phase1 ↦ true][r.phase2 ↦ comparison][r.sign ↦ false] ∧ _ at hg
  obtain ⟨hd1,hd2,hdS,_,_,hdFrame⟩ := blockEFForward_swap r n index cw s v h rfl hr hp1 hp2
    hp.lengthT hrmeta hsmeta hthi hspan (by omega) hlo hhi hv ht htB htp hrem
    hp.lengthS hswidth hsfit hwork1 hp.work2
  have hsep := packed_regroup_disjoint [r.phase1,r.phase2,r.iter] (r.sign :: r.work1 ++ r.work2)
    (r.lengthT ++ r.lengthQ) r.lengthS (r.lengthRPrime ++ r.aux)
    (by simpa only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] using h.physical)
  have hstable : ∀ wire ∈ [r.phase1,r.phase2,r.iter] ++ (r.lengthT ++ r.lengthQ) ++ (r.lengthRPrime ++ r.aux),
      mid wire = s wire := by
    intro wire hw
    apply hdFrame wire
    have hn := List.disjoint_left.mp hsep hw
    intro hm
    apply hn
    simp only [List.mem_append,List.mem_cons] at hm ⊢
    rcases hm with (hm | hm) | hm
    · exact Or.inr (Or.inl (Or.inl hm))
    · exact Or.inr (Or.inr hm)
    · exact Or.inl hm
  have phys := h.physical
  simp only [IndexedStepRegisters.allWires,List.cons_append,List.nil_append,List.nodup_cons] at phys
  have hread (ws : List Wire)
      (hws : ∀ wire ∈ ws, wire ∈ r.work1 ++ r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux) :
      wireValues ws out = wireValues ws mid := by
    apply List.map_congr_left
    intro wire hw
    have hm := hws wire hw
    have h1 : wire ≠ r.phase1 := by intro he; subst wire; exact phys.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))
    have h2 : wire ≠ r.phase2 := by intro he; subst wire; exact phys.2.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
    have hsg : wire ≠ r.sign := by intro he; subst wire; exact phys.2.2.2.1 hm
    rw [hg.1]
    simp only [upd_other _ _ _ hsg,upd_other _ _ _ h2,upd_other _ _ _ h1]
  have hmeta (ws : List Wire)
      (hws : ∀ wire ∈ ws, wire ∈ r.lengthT ++ r.lengthQ ++ r.lengthRPrime ++ r.aux) :
      wireValues ws out = wireValues ws s := by
    rw [hread ws (by
      intro wire hw
      have hm := hws wire hw
      simp only [List.mem_append] at hm
      rcases hm with ((hm | hm) | hm) | hm <;> simp [hm])]
    apply List.map_congr_left
    intro wire hw
    apply hstable wire
    have hm := hws wire hw
    simpa only [List.append_assoc,List.mem_append] using Or.inr hm
  have hiter : mid r.iter = v.iter := (hstable _ (by simp)).trans hp.iter
  have hp1ne2 : r.phase1 ≠ r.phase2 := by intro he; exact phys.1 (by simp [he])
  have hp1nesg : r.phase1 ≠ r.sign := by intro he; exact phys.1 (by simp [he])
  have hp2nesg : r.phase2 ≠ r.sign := by intro he; exact phys.2.1 (by simp [he])
  have hitne1 : r.iter ≠ r.phase1 := by intro he; exact phys.1 (by simp [← he])
  have hitne2 : r.iter ≠ r.phase2 := by intro he; exact phys.2.1 (by simp [← he])
  have hitnesg : r.iter ≠ r.sign := by intro he; exact phys.2.2.1 (by simp [he])
  constructor
  · change wireValues r.work1 out = _
    rw [hread r.work1 (by intro w hw; simp [hw]),hd1]
    exact hp.work1
  · change wireValues r.work2 out = _
    rw [hread r.work2 (by intro w hw; simp [hw])]
    exact hd2
  · change boolWordToNat (wireValues r.lengthT out) = _
    rw [hmeta r.lengthT (by intro w hw; simp [hw])]
    exact hp.lengthT
  · change boolWordToNat (wireValues r.lengthQ out) = _
    rw [hmeta r.lengthQ (by intro w hw; simp [hw])]
    exact hp.lengthQ
  · change boolWordToNat (wireValues r.lengthRPrime out) = _
    rw [hmeta r.lengthRPrime (by intro w hw; simp [hw])]
    exact hp.lengthRP
  · change boolWordToNat (wireValues r.lengthS out) = _
    rw [hread r.lengthS (by intro w hw; simp [hw])]
    exact hdS
  · change out r.phase1 = _
    rw [hg.1]
    simp only [upd_other _ _ _ hp1nesg,upd_other _ _ _ hp1ne2,upd_same]
    change true = (if comparison then EEAPhase.swap else .coefficient).bits.1
    cases comparison <;> rfl
  · change out r.phase2 = _
    rw [hg.1]
    simp only [upd_other _ _ _ hp2nesg,upd_same]
    change comparison = (if comparison then EEAPhase.swap else .coefficient).bits.2
    cases comparison <;> rfl
  · change out r.sign = _
    rw [hg.1,upd_same]
    rfl
  · change out r.iter = _
    rw [hg.1]
    simp only [upd_other _ _ _ hitnesg,upd_other _ _ _ hitne2,upd_other _ _ _ hitne1,hiter]
    rfl
  · intro wire hw
    have haux : wireValues r.aux out = wireValues r.aux s := hmeta _ (by intro w hm; simp [hm])
    exact ((List.map_eq_map_iff.mp haux) wire hw).trans (hp.clean wire hw)

private theorem packed_endpoint_word (ws : List Wire) (s : BasisState) (value : Nat)
    (hv : boolWordToNat (wireValues ws s) = truthMinusOneValue ws.length value) :
    wireValues ws s = constantBits ws.length (truthMinusOneValue ws.length value) := by
  apply boolWordToNat_injective_of_length (by simp only [wireValues,List.length_map,constantBits_length])
  rw [hv, boolWordToNat_constantBits]
  change (_ % _) = (_ % _) % _
  exact (Nat.mod_mod _ _).symm

private theorem packed_endpoint_zero (ws : List Wire) (s : BasisState)
    (hv : boolWordToNat (wireValues ws s) = truthMinusOneValue ws.length 0) :
    wireAnd ws s = true := by
  rw [wireAnd_eq_numeric_allOnes, hv]
  have hz : truthMinusOneValue ws.length 0 = 2^ws.length-1 := by
    change (0+2^ws.length-1%2^ws.length)%2^ws.length = 2^ws.length-1
    have hp : 0 < 2^ws.length := Nat.two_pow_pos _
    by_cases h : 2^ws.length = 1
    · simp [h]
    · have hh : 1 < 2^ws.length := by omega
      rw [Nat.mod_eq_of_lt hh]
      simp only [zero_add]
      rw [Nat.mod_eq_of_lt (by omega)]
  simp only [hz, decide_true]

/-- At a scheduled zero-Q/zero-shift endpoint, the logical packed state determines
both output length words. Physical scan views and decoder routes are derived. -/
theorem blockHForward_packed_lengths (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hstep : index % 4 = 0)
    (hQ : v.lQ = 0) (hS : v.shift = 0)
    (hT : v.lT = v.t.size) (hRP : v.lRPrime = v.rPrime.size)
    (hrem : v.r < v.rPrime) (hmono : v.lT ≤ v.tPrime.size)
    (hspan : v.tPrime.size+1+v.lRPrime ≤ n+3)
    (hcapacity : n+3 < 2^r.lengthT.length)
    (hboundary4 : (endIterationWindowsAt n index).k4 ≤ n+3-v.lRPrime ∧
      n+3-v.lRPrime ≤ (endIterationWindowsAt n index).K4)
    (hboundary5 : (endIterationWindowsAt n index).k5 ≤ v.tPrime.size+2 ∧
      v.tPrime.size+2 ≤ (endIterationWindowsAt n index).K5Decode n)
    (htWindow : (endIterationWindowsAt n index).k4 ≤ v.t.size ∧
      v.t.size ≤ (endIterationWindowsAt n index).K4)
    (htpWindow : (endIterationWindowsAt n index).k4 ≤ v.tPrime.size ∧
      v.tPrime.size ≤ (endIterationWindowsAt n index).K4)
    (hrWindow : v.r ≠ 0 → (endIterationWindowsAt n index).k5 ≤ n+4-v.r.size ∧
      n+4-v.r.size ≤ (endIterationWindowsAt n index).K5Decode n)
    (hrpWindow : (endIterationWindowsAt n index).k5 ≤ n+4-v.rPrime.size ∧
      n+4-v.rPrime.size ≤ (endIterationWindowsAt n index).K5Decode n) :
    (wireValues r.lengthT (run (blockHForward r n index) s),
      wireValues r.lengthRPrime (run (blockHForward r n index) s)) =
      (constantBits r.lengthT.length (truthMinusOneValue r.lengthT.length v.tPrime.size),
       constantBits r.lengthRPrime.length (truthMinusOneValue r.lengthRPrime.length v.r.size)) := by
  have hrpfit : v.rPrime < 2^v.lRPrime := by rw [hRP]; exact Nat.lt_size_self _
  have hremfit := hrem.trans hrpfit
  have htfit : v.t < 2^v.lT := by rw [hT]; exact Nat.lt_size_self _
  have htpfit := Nat.lt_size_self v.tPrime
  have hv := endpoint_canonical_bank_views (n+3) v.lT v.tPrime.size v.lRPrime
    v.t v.tPrime v.r v.rPrime hmono hspan htfit htpfit hremfit hrpfit
  have hw1 : wireValues r.work1 s = constantBits v.lT v.t ++ [false] ++
      (constantBits (n+3-(v.lT+1)) v.r).reverse := by
    simpa only [hQ, constantBits, List.replicate_zero, xorConstantBits,
      List.reverse_nil, List.append_nil, Nat.add_zero] using hp.work1
  have hw2 : wireValues r.work2 s = constantBits (n+3-v.lRPrime) v.tPrime ++
      (constantBits v.lRPrime v.rPrime).reverse := by
    simpa only [hS, List.rotate_zero] using hp.work2
  have ready : IndexedStepReady r s := by
    intro wire hw
    apply hp.clean wire
    simp only [IndexedStepRegisters.sharedScratch, List.mem_cons, List.mem_append] at hw
    rcases hw with he | hw | hw
    · subst wire
      change r.aux.getD 0 0 ∈ r.aux
      rw [List.getD_eq_getElem _ _ (by rw [h.aux_length]; decide)]
      exact List.getElem_mem _
    · exact List.mem_of_mem_take (List.mem_of_mem_drop hw)
    · exact List.mem_of_mem_drop hw
  have hepoch : s r.shiftEpoch = false := by
    apply hp.clean
    change r.aux.getD 1 0 ∈ r.aux
    rw [List.getD_eq_getElem _ _ (by rw [h.aux_length]; decide)]
    exact List.getElem_mem _
  have hq := packed_endpoint_zero r.lengthQ s (by simpa only [hQ] using hp.lengthQ)
  have hs := packed_endpoint_zero r.lengthS s (by simpa only [hS] using hp.lengthS)
  have hmT := packed_endpoint_word r.lengthT s v.lT hp.lengthT
  have hmRP := packed_endpoint_word r.lengthRPrime s v.lRPrime hp.lengthRP
  have hwide : v.lRPrime ≤ n+3-(v.tPrime.size+1) := by omega
  have hremWide := hremfit.trans_le (Nat.pow_le_pow_right (by decide) hwide)
  have hrpWide := hrpfit.trans_le (Nat.pow_le_pow_right (by decide) hwide)
  have htWide := htfit.trans_le (Nat.pow_le_pow_right (by decide)
    (by omega : v.lT ≤ n+3-v.lRPrime))
  have htpWide := htpfit.trans_le (Nat.pow_le_pow_right (by decide)
    (by omega : v.tPrime.size ≤ n+3-v.lRPrime))
  apply blockHForward_canonical_endpoint r n index v.t v.tPrime v.r v.rPrime
    (n+3-(v.tPrime.size+1)) (n+3-(v.tPrime.size+1))
    (constantBits v.lRPrime v.r).reverse (constantBits v.lRPrime v.rPrime).reverse
    (constantBits v.tPrime.size v.t ++ [false]) (constantBits v.tPrime.size v.tPrime ++ [false])
    (by omega) hcapacity (by simpa only [hRP] using hboundary4) hboundary5
    s h ready hstep hq hs hepoch
  · simpa only [← hRP] using hw1.trans hv.1
  · simpa only [← hRP] using hw2
  · exact hw1.trans hv.2.1
  · exact hw2.trans hv.2.2
  · simpa only [← hRP] using htWide
  · simpa only [← hRP] using htpWide
  · exact hremWide
  · exact hrpWide
  · exact htWindow
  · exact htpWindow
  · simp only [List.length_append, constantBits_length, List.length_singleton]; omega
  · simp only [List.length_append, constantBits_length, List.length_singleton]; omega
  · intro hz
    have hb := hrWindow hz
    have hsize := Nat.size_le.mpr hremfit
    exact ⟨hb.1, hb.2, by omega⟩
  · intro _
    exact ⟨hrpWindow.1, hrpWindow.2, by omega⟩
  · simpa only [hT] using hmT
  · simpa only [hRP] using hmRP

end ShorECDLP.Paper2607_13816
