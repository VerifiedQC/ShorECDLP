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
end ShorECDLP.Paper2607_13816
