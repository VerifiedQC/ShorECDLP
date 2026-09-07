import ShorECDLP.Submission.«2607_13816».Arithmetic.CarryAdd

/-!
# Borrowed carry XOR for Gidney constant arithmetic

The pinned quadratic backend clears its borrowed carry word with `_xor_carries_all`.
The descending sweep reads the original dirty bits before the ascending sweep changes them.
The XOR of these two sweeps cancels the arbitrary dirty input and leaves just the carries.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

/-- Source `_ccx_cond_const` with the constant inversions gated by `q`. -/
def carryConstCCX (q a b out : Wire) (ka kb : Bool) : Circuit :=
  (if ka then [.CX q a] else []) ++ (if kb then [.CX q b] else []) ++
    [.CCX a b out] ++ (if kb then [.CX q b] else []) ++ (if ka then [.CX q a] else [])

private def carryXorBackward (q previous : Wire) : List Wire → List Wire → List Bool → Circuit
  | a :: as, d :: ds, k :: ks =>
      carryXorBackward q d as ds ks ++ carryConstCCX q a previous d k false
  | _, _, _ => []

private def carryXorForward (q previous : Wire) : List Wire → List Wire → List Bool → Circuit
  | a :: as, d :: ds, k :: ks =>
      carryConstCCX q a previous d k k ++ carryXorForward q d as ds ks
  | _, _, _ => []

private def carryXorConstants (q : Wire) : List Wire → List Bool → Circuit
  | d :: ds, k :: ks => (if k then [.CX q d] else []) ++ carryXorConstants q ds ks
  | _, _ => []

/-- Literal controlled `_xor_carries_all` stream for a little-endian constant word.
The incoming carry wire is clean; the output word may contain arbitrary borrowed data. -/
def controlledConstCarryXor (input dirty : List Wire) (constant : List Bool)
    (control carry : Wire) : Circuit :=
  match input, dirty, constant with
  | a :: as, d :: ds, k :: ks =>
      carryXorBackward control d as ds ks ++ carryXorConstants control (d :: ds) (k :: ks) ++
        carryConstCCX control carry a d k k ++ carryXorForward control d as ds ks
  | _, _, _ => []

/-- Ordinary carry-out bits of adding two little-endian words. -/
def constantCarryBits (incoming : Bool) : List Bool → List Bool → List Bool
  | a :: as, k :: ks =>
      let next := cuccaroCarry a k incoming
      next :: constantCarryBits next as ks
  | _, _ => []

private def backwardBits (previous : Bool) : List Bool → List Bool → List Bool → List Bool
  | a :: as, k :: ks, d :: ds =>
      Bool.xor d ((Bool.xor a k) && previous) :: backwardBits d as ks ds
  | _, _, _ => []

private def forwardBits (previous : Bool) : List Bool → List Bool → List Bool → List Bool
  | a :: as, k :: ks, d :: ds =>
      let next := Bool.xor d ((Bool.xor a k) && (Bool.xor previous k))
      next :: forwardBits next as ks ds
  | _, _, _ => []

private theorem carryXor_boolean (a k dirty previous carry : Bool) :
    Bool.xor (Bool.xor (Bool.xor dirty ((Bool.xor a k) && previous)) k)
      ((Bool.xor a k) && (Bool.xor (Bool.xor previous carry) k)) =
        Bool.xor dirty (cuccaroCarry a k carry) := by
  cases a <;> cases k <;> cases dirty <;> cases previous <;> cases carry <;> decide

private theorem carryXor_bits (as ks ds : List Bool)
    (previous carry : Bool) (hk : as.length = ks.length) (hd : as.length = ds.length) :
    forwardBits (Bool.xor previous carry) as ks
      (List.zipWith Bool.xor (backwardBits previous as ks ds) ks) =
        List.zipWith Bool.xor ds (constantCarryBits carry as ks) := by
  induction as generalizing ks ds previous carry with
  | nil => cases ks <;> cases ds <;> simp_all [backwardBits,forwardBits,constantCarryBits]
  | cons a as ih =>
    cases ks with
    | nil => simp at hk
    | cons k ks =>
      cases ds with
      | nil => simp at hd
      | cons d ds =>
        have hk' : as.length = ks.length := by simpa using hk
        have hd' : as.length = ds.length := by simpa using hd
        simp only [backwardBits,List.zipWith_cons_cons,forwardBits,constantCarryBits]
        rw [carryXor_boolean,ih ks ds d (cuccaroCarry a k carry) hk' hd']

private theorem carryConstCCX_state (q a b out : Wire) (ka kb : Bool) (s : BasisState)
    (hnd : [q,a,b,out].Nodup) :
    run (carryConstCCX q a b out ka kb) s =
      upd s out (Bool.xor (s out)
        ((Bool.xor (s a) (s q && ka)) && (Bool.xor (s b) (s q && kb)))) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
  rcases hnd with ⟨⟨hqa,hqb,hqo⟩,⟨⟨hab,hao⟩,hbo,_⟩⟩
  funext w
  cases ka <;> cases kb <;>
    simp [carryConstCCX,run_append,run_cons,run_nil,applyGate,upd,
      hqa,hqb,hqo,hab,hao,hbo,Ne.symm hqa,Ne.symm hqb,Ne.symm hqo,
      Ne.symm hab,Ne.symm hao,Ne.symm hbo]
  all_goals
    by_cases hwa : w = a <;> by_cases hwb : w = b <;> by_cases hwo : w = out <;>
      simp_all

private theorem carrySweep_layout (q p a d : Wire) (as ds : List Wire)
    (hnd : (q :: p :: (a :: as) ++ d :: ds).Nodup) :
    [q,a,p,d].Nodup ∧ (q :: d :: as ++ ds).Nodup ∧
      q ∉ d :: ds ∧ p ∉ d :: ds ∧ a ∉ d :: ds ∧ d ∉ ds := by
  have hq := (List.nodup_cons.mp hnd).1
  have ht := (List.nodup_cons.mp hnd).2
  have hp := (List.nodup_cons.mp ht).1
  have hd := List.nodup_append.mp (List.nodup_cons.mp ht).2
  have ha := (List.nodup_cons.mp hd.1).1
  have hds := (List.nodup_cons.mp hd.2.1).1
  have hdis := hd.2.2
  have hqa : q ≠ a := by intro h; apply hq; change q ∈ p :: (a :: as) ++ d :: ds; simp [h]
  have hqp : q ≠ p := by intro h; apply hq; change q ∈ p :: (a :: as) ++ d :: ds; simp [h]
  have hqd : q ≠ d := by intro h; apply hq; change q ∈ p :: (a :: as) ++ d :: ds; simp [h]
  have hap : a ≠ p := by intro h; apply hp; change p ∈ (a :: as) ++ d :: ds; simp [← h]
  have had : a ≠ d := hdis a (by simp) d (by simp)
  have hpd : p ≠ d := by intro h; apply hp; change p ∈ (a :: as) ++ d :: ds; simp [h]
  refine ⟨by simp [hqa,hqp,hqd,hap,had,hpd],?_,?_,?_,?_,hds⟩
  · have hdas : d ∉ as := by intro h; exact hdis d (by simp [h]) d (by simp) rfl
    have hqas : q ∉ as := by
      intro h; apply hq; change q ∈ p :: (a :: as) ++ d :: ds; simp [h]
    have hqds : q ∉ ds := by
      intro h; apply hq; change q ∈ p :: (a :: as) ++ d :: ds; simp [h]
    have hasds : (as ++ ds).Nodup := by
      apply List.nodup_append.mpr
      exact ⟨(List.nodup_cons.mp hd.1).2,(List.nodup_cons.mp hd.2.1).2,
        fun x hx y hy => hdis x (by simp [hx]) y (by simp [hy])⟩
    simpa only [List.cons_append,List.nodup_cons,List.mem_append,not_or,List.mem_cons] using
      And.intro (And.intro hqd (And.intro hqas hqds))
        (And.intro (And.intro hdas hds) hasds)
  · intro h; apply hq; change q ∈ p :: (a :: as) ++ d :: ds
    exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
  · intro h; apply hp; change p ∈ (a :: as) ++ d :: ds
    exact List.mem_append_right _ h
  · intro h; exact hdis a (by simp) a h rfl

private theorem wireValues_upd_outside (ws : List Wire) (s : BasisState) (w : Wire)
    (value : Bool) (hw : w ∉ ws) : wireValues ws (upd s w value) = wireValues ws s := by
  apply List.map_congr_left
  intro v hv
  have hvw : v ≠ w := fun h => hw (h ▸ hv)
  simp [upd,hvw]

private theorem carryXorBackward_correct (input dirty : List Wire) (constant : List Bool)
    (q p : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length) (hnd : (q :: p :: input ++ dirty).Nodup) :
    wireValues dirty (run (carryXorBackward q p input dirty constant) s) =
      backwardBits (s p) (wireValues input s) (constant.map (fun k => s q && k))
        (wireValues dirty s) ∧
      (∀ w, w ∉ dirty → run (carryXorBackward q p input dirty constant) s w = s w) := by
  induction input generalizing dirty constant p s with
  | nil =>
    cases dirty <;> cases constant <;> simp_all [carryXorBackward,wireValues,backwardBits]
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        have hl := carrySweep_layout q p a d as ds hnd
        have hr := ih ds ks d s (by simpa using hk) (by simpa using hd) hl.2.1
        let mid := run (carryXorBackward q d as ds ks) s
        have hmid (w : Wire) (hw : w ∉ ds) : mid w = s w := hr.2 w hw
        have hmq : mid q = s q := hmid q (by intro h; exact hl.2.2.1 (by simp [h]))
        have hma : mid a = s a := hmid a (by intro h; exact hl.2.2.2.2.1 (by simp [h]))
        have hmp : mid p = s p := hmid p (by intro h; exact hl.2.2.2.1 (by simp [h]))
        have hmd : mid d = s d := hmid d hl.2.2.2.2.2
        rw [carryXorBackward,run_append,carryConstCCX_state q a p d k false mid hl.1]
        constructor
        · simp only [wireValues,List.map_cons,backwardBits,Bool.and_false,Bool.xor_false]
          change _ :: wireValues ds (upd mid d _) = _
          rw [wireValues_upd_outside ds mid d _ hl.2.2.2.2.2]
          simp only [upd,ite_true,hmq,hma,hmp,hmd]
          exact congrArg (List.cons _) hr.1
        · intro w hw
          have hwd : w ≠ d := by intro h; apply hw; simp [h]
          have hwds : w ∉ ds := by intro h; apply hw; simp [h]
          simp [upd,hwd,hmid w hwds]

private theorem carryXorForward_correct (input dirty : List Wire) (constant : List Bool)
    (q p : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length) (hnd : (q :: p :: input ++ dirty).Nodup) :
    wireValues dirty (run (carryXorForward q p input dirty constant) s) =
      forwardBits (s p) (wireValues input s) (constant.map (fun k => s q && k))
        (wireValues dirty s) ∧
      (∀ w, w ∉ dirty → run (carryXorForward q p input dirty constant) s w = s w) := by
  induction input generalizing dirty constant p s with
  | nil =>
    cases dirty <;> cases constant <;> simp_all [carryXorForward,wireValues,forwardBits]
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        have hl := carrySweep_layout q p a d as ds hnd
        let value := Bool.xor (s d) ((Bool.xor (s a) (s q && k)) &&
          (Bool.xor (s p) (s q && k)))
        let mid := upd s d value
        have hr := ih ds ks d mid (by simpa using hk) (by simpa using hd) hl.2.1
        have hparts := List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
        have hdas : d ∉ as := by intro h; exact hparts.2.2 d (by simp [h]) d (by simp) rfl
        have hqd : q ≠ d := by intro h; exact hl.2.2.1 (by simp [h])
        have hmq : mid q = s q := by simp [mid,upd,hqd]
        have hmd : mid d = value := by simp [mid,upd]
        have hma : wireValues as mid = wireValues as s := wireValues_upd_outside as s d value hdas
        have hms : wireValues ds mid = wireValues ds s :=
          wireValues_upd_outside ds s d value hl.2.2.2.2.2
        rw [carryXorForward,run_append,carryConstCCX_state q a p d k k s hl.1]
        constructor
        · change run (carryXorForward q d as ds ks) mid d ::
            wireValues ds (run (carryXorForward q d as ds ks) mid) = _
          rw [hr.2 d hl.2.2.2.2.2,hr.1,hmq,hmd,hma,hms]
          rfl
        · intro w hw
          have hwd : w ≠ d := by intro h; apply hw; simp [h]
          have hwds : w ∉ ds := by intro h; apply hw; simp [h]
          change run (carryXorForward q d as ds ks) mid w = _
          rw [hr.2 w hwds]
          simp [mid,upd,hwd]

private theorem carryXorConstants_correct (dirty : List Wire) (constant : List Bool)
    (q : Wire) (s : BasisState) (hk : dirty.length = constant.length)
    (hnd : (q :: dirty).Nodup) :
    wireValues dirty (run (carryXorConstants q dirty constant) s) =
      List.zipWith Bool.xor (wireValues dirty s) (constant.map (fun k => s q && k)) ∧
      (∀ w, w ∉ dirty → run (carryXorConstants q dirty constant) s w = s w) := by
  induction dirty generalizing constant s with
  | nil => cases constant <;> simp_all [carryXorConstants,wireValues]
  | cons d ds ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      have hqd : q ≠ d := by simpa using fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons.mpr (Or.inl h))
      have hqds : q ∉ ds := by intro h; exact (List.nodup_cons.mp hnd).1 (by simp [h])
      have hdnd := (List.nodup_cons.mp hnd).2
      have hdds := (List.nodup_cons.mp hdnd).1
      have htail : (q :: ds).Nodup := List.nodup_cons.mpr ⟨hqds,(List.nodup_cons.mp hdnd).2⟩
      let mid := upd s d (Bool.xor (s d) (s q && k))
      have hpulse : run (if k then [.CX q d] else []) s = mid := by
        funext w
        cases k <;> by_cases hw : w = d <;> simp [run,applyGate,mid,upd,hw]
      have hr := ih ks mid (by simpa using hk) htail
      have hmq : mid q = s q := by simp [mid,upd,hqd]
      have hmd : mid d = Bool.xor (s d) (s q && k) := by simp [mid,upd]
      have hms : wireValues ds mid = wireValues ds s := wireValues_upd_outside ds s d _ hdds
      rw [carryXorConstants,run_append,hpulse]
      constructor
      · change run (carryXorConstants q ds ks) mid d ::
          wireValues ds (run (carryXorConstants q ds ks) mid) = _
        rw [hr.2 d hdds,hr.1,hmq,hmd,hms]
        rfl
      · intro w hw
        have hwd : w ≠ d := by intro h; apply hw; simp [h]
        have hwds : w ∉ ds := by intro h; apply hw; simp [h]
        rw [hr.2 w hwds]
        simp [mid,upd,hwd]

private theorem carryXor_first (a q k d : Bool) :
    Bool.xor (Bool.xor d (q && k)) ((q && k) && (Bool.xor a (q && k))) =
      Bool.xor d (cuccaroCarry a (q && k) false) := by
  cases a <;> cases q <;> cases k <;> cases d <;> decide

/-- The borrowed output is XORed with the ordinary addition carry word. All other wires,
including the input, control and clean carry, retain their original values. -/
theorem controlledConstCarryXor_correct (input dirty : List Wire) (constant : List Bool)
    (q c : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length) (hnd : (q :: c :: input ++ dirty).Nodup)
    (hc : s c = false) :
    wireValues dirty (run (controlledConstCarryXor input dirty constant q c) s) =
      List.zipWith Bool.xor (wireValues dirty s)
        (constantCarryBits false (wireValues input s) (constant.map (fun k => s q && k))) ∧
      (∀ w, w ∉ dirty → run (controlledConstCarryXor input dirty constant q c) s w = s w) := by
  cases input with
  | nil => cases dirty <;> cases constant <;> simp_all [controlledConstCarryXor,wireValues,constantCarryBits]
  | cons a as =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        have hk' : as.length = ks.length := by simpa using hk
        have hd' : as.length = ds.length := by simpa using hd
        have hl := carrySweep_layout q c a d as ds hnd
        have hparts := List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
        have hdds := hl.2.2.2.2.2
        have hin (w : Wire) (hw : w ∈ as) : w ∉ d :: ds := by
          intro hdw; exact hparts.2.2 w (by simp [hw]) w hdw rfl
        have hflipLayout : (q :: d :: ds).Nodup := List.nodup_cons.mpr ⟨hl.2.2.1,hparts.2.1⟩
        let s1 := run (carryXorBackward q d as ds ks) s
        have hb := carryXorBackward_correct as ds ks q d s hk' hd' hl.2.1
        have h1 (w : Wire) (hw : w ∉ ds) : s1 w = s w := hb.2 w hw
        have h1q : s1 q = s q := h1 q (by intro h; exact hl.2.2.1 (by simp [h]))
        have h1d : s1 d = s d := h1 d hdds
        let s2 := run (carryXorConstants q (d :: ds) (k :: ks)) s1
        have hf := carryXorConstants_correct (d :: ds) (k :: ks) q s1
          (by simp [← hd',hk']) hflipLayout
        have h2 (w : Wire) (hw : w ∉ d :: ds) : s2 w = s w :=
          (hf.2 w hw).trans (h1 w (by intro h; exact hw (by simp [h])))
        have h2q : s2 q = s q := h2 q hl.2.2.1
        have h2a : s2 a = s a := h2 a hl.2.2.2.2.1
        have h2c : s2 c = false := (h2 c hl.2.2.2.1).trans hc
        have h2d : s2 d = Bool.xor (s d) (s q && k) := by
          have hh := congrArg List.head? hf.1
          simpa [wireValues,h1d,h1q] using hh
        have h2ds : wireValues ds s2 = List.zipWith Bool.xor
            (backwardBits (s d) (wireValues as s) (ks.map (fun k => s q && k)) (wireValues ds s))
            (ks.map (fun k => s q && k)) := by
          have ht := congrArg List.tail hf.1
          simp only [wireValues,List.map_cons,List.zipWith_cons_cons,List.tail_cons] at ht
          change wireValues ds s2 = List.zipWith Bool.xor (wireValues ds s1) _ at ht
          rw [ht,hb.1,h1q]
        let next := cuccaroCarry (s a) (s q && k) false
        let s3 := upd s2 d (Bool.xor (s d) next)
        have hpulse : run (carryConstCCX q c a d k k) s2 = s3 := by
          have hcell : [q,c,a,d].Nodup := by
            have hh := hl.1
            simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢
            tauto
          rw [carryConstCCX_state q c a d k k s2 hcell,h2q,h2c,h2a,h2d]
          simp only [Bool.false_xor]
          rw [carryXor_first]
        have h3 (w : Wire) (hw : w ∉ d :: ds) : s3 w = s w := by
          have hwd : w ≠ d := by intro h; exact hw (by simp [h])
          simp [s3,upd,hwd,h2 w hw]
        have h3q : s3 q = s q := h3 q hl.2.2.1
        have h3d : s3 d = Bool.xor (s d) next := by simp [s3,upd]
        have h3as : wireValues as s3 = wireValues as s := by
          apply List.map_congr_left; intro w hw; exact h3 w (hin w hw)
        have h3ds : wireValues ds s3 = wireValues ds s2 :=
          wireValues_upd_outside ds s2 d _ hdds
        have hforward := carryXorForward_correct as ds ks q d s3 hk' hd' hl.2.1
        rw [controlledConstCarryXor,run_append,run_append,run_append]
        change wireValues (d :: ds) (run (carryXorForward q d as ds ks)
          (run (carryConstCCX q c a d k k) s2)) = _ ∧ _
        rw [hpulse]
        constructor
        · change run (carryXorForward q d as ds ks) s3 d ::
            wireValues ds (run (carryXorForward q d as ds ks) s3) = _
          rw [hforward.2 d hdds,hforward.1,h3q,h3d,h3as,h3ds,h2ds,
            carryXor_bits _ _ _ (s d) next (by simp [wireValues,hk']) (by simp [wireValues,hd'])]
          rfl
        · intro w hw
          have hwds : w ∉ ds := by intro h; exact hw (by simp [h])
          rw [hforward.2 w hwds,h3 w hw]

/-- Number of set bits in a little-endian Boolean constant. -/
def constantBitWeight (ks : List Bool) : Nat := (ks.map Bool.toNat).sum

private theorem carryConstCCX_resources (q a b d : Wire) (ka kb : Bool) :
    HPFree (carryConstCCX q a b d ka kb) ∧
      eeaToffoliCount (carryConstCCX q a b d ka kb) = 1 ∧
      eeaCnotCount (carryConstCCX q a b d ka kb) = 2 * (ka.toNat + kb.toNat) ∧
      tCount (carryConstCCX q a b d ka kb) = 7 := by
  cases ka <;> cases kb <;>
    simp [carryConstCCX,eeaToffoliCount,eeaCnotCount,tCount,tCost]

private theorem carryConstCCX_wellFormed (q a b d : Wire) (ka kb : Bool)
    (hnd : [q,a,b,d].Nodup) : CircuitWellFormed (carryConstCCX q a b d ka kb) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
  rcases hnd with ⟨⟨hqa,hqb,hqd⟩,⟨⟨hab,had⟩,hbd,_⟩⟩
  cases ka <;> cases kb <;>
    simp [carryConstCCX,CircuitWellFormed,Gate.WellFormed,hqa,hqb,hqd,hab,had,hbd]

private theorem carryXorBackward_resources (input dirty : List Wire) (constant : List Bool)
    (q p : Wire) (hk : input.length = constant.length) (hd : input.length = dirty.length) :
    HPFree (carryXorBackward q p input dirty constant) ∧
      eeaToffoliCount (carryXorBackward q p input dirty constant) = input.length ∧
      eeaCnotCount (carryXorBackward q p input dirty constant) = 2 * constantBitWeight constant ∧
      tCount (carryXorBackward q p input dirty constant) = 7 * input.length := by
  induction input generalizing dirty constant p with
  | nil => cases dirty <;> cases constant <;> simp_all [carryXorBackward,constantBitWeight,eeaToffoliCount,eeaCnotCount,tCount]
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        have ht := ih ds ks d (by simpa using hk) (by simpa using hd)
        have hp := carryConstCCX_resources q a p d k false
        simp only [carryXorBackward,hpFree_append,eeaToffoliCount_append,eeaCnotCount_append,
          tCount_append,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
        simp [constantBitWeight,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

private theorem carryXorForward_resources (input dirty : List Wire) (constant : List Bool)
    (q p : Wire) (hk : input.length = constant.length) (hd : input.length = dirty.length) :
    HPFree (carryXorForward q p input dirty constant) ∧
      eeaToffoliCount (carryXorForward q p input dirty constant) = input.length ∧
      eeaCnotCount (carryXorForward q p input dirty constant) = 4 * constantBitWeight constant ∧
      tCount (carryXorForward q p input dirty constant) = 7 * input.length := by
  induction input generalizing dirty constant p with
  | nil => cases dirty <;> cases constant <;> simp_all [carryXorForward,constantBitWeight,eeaToffoliCount,eeaCnotCount,tCount]
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        have ht := ih ds ks d (by simpa using hk) (by simpa using hd)
        have hp := carryConstCCX_resources q a p d k k
        simp only [carryXorForward,hpFree_append,eeaToffoliCount_append,eeaCnotCount_append,
          tCount_append,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
        simp [constantBitWeight,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
        omega

private theorem carryXorConstants_resources (dirty : List Wire) (constant : List Bool)
    (q : Wire) (hk : dirty.length = constant.length) :
    HPFree (carryXorConstants q dirty constant) ∧
      eeaToffoliCount (carryXorConstants q dirty constant) = 0 ∧
      eeaCnotCount (carryXorConstants q dirty constant) = constantBitWeight constant ∧
      tCount (carryXorConstants q dirty constant) = 0 := by
  induction dirty generalizing constant with
  | nil => cases constant <;> simp_all [carryXorConstants,constantBitWeight,eeaToffoliCount,eeaCnotCount,tCount]
  | cons d ds ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      have ht := ih ks (by simpa using hk)
      simp only [carryXorConstants,hpFree_append,eeaToffoliCount_append,eeaCnotCount_append,
        tCount_append,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
      cases k <;> simp [constantBitWeight,eeaToffoliCount,eeaCnotCount,tCount,tCost]

/-- Constructor-derived counts. The CNOT count reflects the sparse constant bits. -/
theorem controlledConstCarryXor_counts (a : Wire) (input dirty : List Wire) (k : Bool)
    (constant : List Bool) (q c : Wire) (hk : input.length = constant.length)
    (hd : (a :: input).length = dirty.length) :
    HPFree (controlledConstCarryXor (a :: input) dirty (k :: constant) q c) ∧
      eeaToffoliCount (controlledConstCarryXor (a :: input) dirty (k :: constant) q c) =
        2 * input.length + 1 ∧
      eeaCnotCount (controlledConstCarryXor (a :: input) dirty (k :: constant) q c) =
        7 * constantBitWeight constant + 5 * k.toNat ∧
      tCount (controlledConstCarryXor (a :: input) dirty (k :: constant) q c) =
        7 * (2 * input.length + 1) := by
  cases dirty with
  | nil => simp at hd
  | cons d ds =>
    have hd' : input.length = ds.length := by simpa using hd
    have hb := carryXorBackward_resources input ds constant q d hk hd'
    have hf := carryXorForward_resources input ds constant q d hk hd'
    have hx := carryXorConstants_resources (d :: ds) (k :: constant) q (by simp [← hd',hk])
    have hp := carryConstCCX_resources q c a d k k
    simp only [controlledConstCarryXor,hpFree_append,eeaToffoliCount_append,
      eeaCnotCount_append,tCount_append,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,
      hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2,
      hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
    simp only [constantBitWeight,List.map_cons,List.sum_cons] at *
    simp only [true_and]
    omega

private theorem carrySweeps_wellFormed (input dirty : List Wire) (constant : List Bool)
    (q p : Wire) (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (hnd : (q :: p :: input ++ dirty).Nodup) :
    CircuitWellFormed (carryXorBackward q p input dirty constant) ∧
      CircuitWellFormed (carryXorForward q p input dirty constant) := by
  induction input generalizing dirty constant p with
  | nil => cases dirty <;> cases constant <;> simp_all [carryXorBackward,carryXorForward,CircuitWellFormed]
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        have hl := carrySweep_layout q p a d as ds hnd
        have ht := ih ds ks d (by simpa using hk) (by simpa using hd) hl.2.1
        rw [carryXorBackward,carryXorForward,circuitWellFormed_append,circuitWellFormed_append]
        exact ⟨⟨ht.1,carryConstCCX_wellFormed q a p d k false hl.1⟩,
          ⟨carryConstCCX_wellFormed q a p d k k hl.1,ht.2⟩⟩

private theorem carryXorConstants_wellFormed (dirty : List Wire) (constant : List Bool)
    (q : Wire) (hq : q ∉ dirty) : CircuitWellFormed (carryXorConstants q dirty constant) := by
  induction dirty generalizing constant with
  | nil => simp [carryXorConstants,CircuitWellFormed]
  | cons d ds ih =>
    cases constant with
    | nil => simp [carryXorConstants,CircuitWellFormed]
    | cons k ks =>
      have hqd : q ≠ d := by intro h; exact hq (by simp [h])
      have hqds : q ∉ ds := by intro h; exact hq (by simp [h])
      rw [carryXorConstants,circuitWellFormed_append]
      exact ⟨by cases k <;> simp [CircuitWellFormed,Gate.WellFormed,hqd],ih ks hqds⟩

theorem controlledConstCarryXor_wellFormed (input dirty : List Wire) (constant : List Bool)
    (q c : Wire) (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (hnd : (q :: c :: input ++ dirty).Nodup) :
    CircuitWellFormed (controlledConstCarryXor input dirty constant q c) := by
  cases input with
  | nil => simp [controlledConstCarryXor,CircuitWellFormed]
  | cons a as =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        have hl := carrySweep_layout q c a d as ds hnd
        have ht := carrySweeps_wellFormed as ds ks q d (by simpa using hk) (by simpa using hd) hl.2.1
        have hcell : [q,c,a,d].Nodup := by
          have hh := hl.1
          simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢
          tauto
        simp only [controlledConstCarryXor,circuitWellFormed_append]
        exact ⟨⟨⟨ht.1,carryXorConstants_wellFormed (d :: ds) (k :: ks) q hl.2.2.1⟩,
          carryConstCCX_wellFormed q c a d k k hcell⟩,ht.2⟩

private theorem carryConstCCX_usesOnly (q a b d : Wire) (ka kb : Bool) :
    PaperCircuitUsesOnly [q,a,b,d] (carryConstCCX q a b d ka kb) := by
  cases ka <;> cases kb <;> simp [carryConstCCX,PaperCircuitUsesOnly,PaperGateUsesOnly,gateWires]

private theorem carrySweeps_usesOnly (input dirty : List Wire) (constant : List Bool) (q p : Wire) :
    PaperCircuitUsesOnly (q :: p :: input ++ dirty) (carryXorBackward q p input dirty constant) ∧
      PaperCircuitUsesOnly (q :: p :: input ++ dirty) (carryXorForward q p input dirty constant) := by
  induction input generalizing dirty constant p with
  | nil => simp [carryXorBackward,carryXorForward,PaperCircuitUsesOnly]
  | cons a as ih =>
    cases dirty with
    | nil => simp [carryXorBackward,carryXorForward,PaperCircuitUsesOnly]
    | cons d ds =>
      cases constant with
      | nil => simp [carryXorBackward,carryXorForward,PaperCircuitUsesOnly]
      | cons k ks =>
        have ht := ih ds ks d
        have hsub : ∀ w ∈ q :: d :: as ++ ds, w ∈ q :: p :: (a :: as) ++ d :: ds := by
          intro w hw; simp only [List.mem_append,List.mem_cons] at hw ⊢; tauto
        have hcell : ∀ w ∈ [q,a,p,d], w ∈ q :: p :: (a :: as) ++ d :: ds := by
          intro w hw; simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢; tauto
        exact ⟨(ht.1.mono hsub).append ((carryConstCCX_usesOnly q a p d k false).mono hcell),
          ((carryConstCCX_usesOnly q a p d k k).mono hcell).append (ht.2.mono hsub)⟩

private theorem carryXorConstants_usesOnly (dirty : List Wire) (constant : List Bool) (q : Wire) :
    PaperCircuitUsesOnly (q :: dirty) (carryXorConstants q dirty constant) := by
  induction dirty generalizing constant with
  | nil => simp [carryXorConstants,PaperCircuitUsesOnly]
  | cons d ds ih =>
    cases constant with
    | nil => simp [carryXorConstants,PaperCircuitUsesOnly]
    | cons k ks =>
      apply PaperCircuitUsesOnly.append
      · cases k <;> simp [PaperCircuitUsesOnly,PaperGateUsesOnly,gateWires]
      · exact (ih ks).mono (by intro w hw; simp only [List.mem_cons] at hw ⊢; tauto)

theorem controlledConstCarryXor_usesOnly (input dirty : List Wire) (constant : List Bool) (q c : Wire) :
    PaperCircuitUsesOnly (q :: c :: input ++ dirty) (controlledConstCarryXor input dirty constant q c) := by
  cases input with
  | nil => simp [controlledConstCarryXor,PaperCircuitUsesOnly]
  | cons a as =>
    cases dirty with
    | nil => simp [controlledConstCarryXor,PaperCircuitUsesOnly]
    | cons d ds =>
      cases constant with
      | nil => simp [controlledConstCarryXor,PaperCircuitUsesOnly]
      | cons k ks =>
        have ht := carrySweeps_usesOnly as ds ks q d
        have hsub : ∀ w ∈ q :: d :: as ++ ds, w ∈ q :: c :: (a :: as) ++ d :: ds := by
          intro w hw; simp only [List.mem_append,List.mem_cons] at hw ⊢; tauto
        have hf := (carryXorConstants_usesOnly (d :: ds) (k :: ks) q).mono
          (show ∀ w ∈ q :: d :: ds, w ∈ q :: c :: (a :: as) ++ d :: ds by
            intro w hw; simp only [List.mem_append,List.mem_cons] at hw ⊢; tauto)
        have hp := (carryConstCCX_usesOnly q c a d k k).mono
          (show ∀ w ∈ [q,c,a,d], w ∈ q :: c :: (a :: as) ++ d :: ds by
            intro w hw; simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢; tauto)
        exact (((ht.1.mono hsub).append hf).append hp).append (ht.2.mono hsub)

private theorem carryConstCCX_covers (q a b d w : Wire) (ka kb : Bool) (hw : w ∈ [a,b,d]) :
    w ∈ circuitWires (carryConstCCX q a b d ka kb) := by
  cases ka <;> cases kb <;> simp_all [carryConstCCX,circuitWires,gateWires] <;> tauto

private theorem carryXorForward_covers (input dirty : List Wire) (constant : List Bool) (q p w : Wire)
    (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (hw : w ∈ input ++ dirty) : w ∈ circuitWires (carryXorForward q p input dirty constant) := by
  induction input generalizing dirty constant p with
  | nil =>
    have he : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    subst dirty; simp at hw
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        simp only [carryXorForward,circuitWires,List.flatMap_append,List.mem_append]
        change w ∈ circuitWires (carryConstCCX q a p d k k) ∨
          w ∈ circuitWires (carryXorForward q d as ds ks)
        simp only [List.mem_append,List.mem_cons] at hw
        rcases hw with (h | h) | (h | h)
        · exact Or.inl (carryConstCCX_covers q a p d w k k (by simp [h]))
        · exact Or.inr (ih ds ks d (by simpa using hk) (by simpa using hd) (by simp [h]))
        · exact Or.inl (carryConstCCX_covers q a p d w k k (by simp [h]))
        · exact Or.inr (ih ds ks d (by simpa using hk) (by simpa using hd) (by simp [h]))

/-- When the low constant bit is set, every declared role occurs in the literal stream. -/
theorem controlledConstCarryXor_qubitCount (a : Wire) (input dirty : List Wire)
    (constant : List Bool) (q c : Wire) (hk : input.length = constant.length)
    (hd : (a :: input).length = dirty.length) (hnd : (q :: c :: (a :: input) ++ dirty).Nodup) :
    qubitCount (controlledConstCarryXor (a :: input) dirty (true :: constant) q c) =
      2 * (input.length + 1) + 2 := by
  have hmem (w : Wire) :
      w ∈ circuitWires (controlledConstCarryXor (a :: input) dirty (true :: constant) q c) ↔
        w ∈ q :: c :: (a :: input) ++ dirty := by
    constructor
    · intro hw
      obtain ⟨g,hg,hwg⟩ := List.mem_flatMap.mp hw
      exact controlledConstCarryXor_usesOnly _ _ _ _ _ g hg w hwg
    · intro hw
      cases dirty with
      | nil => simp at hd
      | cons d ds =>
        have hcell : w ∈ [q,c,a,d] → w ∈ circuitWires (carryConstCCX q c a d true true) := by
          intro h; simpa [carryConstCCX,circuitWires,gateWires,or_assoc,or_left_comm,or_comm] using h
        simp only [controlledConstCarryXor,circuitWires,List.flatMap_append,List.mem_append]
        change ((w ∈ circuitWires (carryXorBackward q d input ds constant) ∨
          w ∈ circuitWires (carryXorConstants q (d :: ds) (true :: constant))) ∨
          w ∈ circuitWires (carryConstCCX q c a d true true)) ∨
          w ∈ circuitWires (carryXorForward q d input ds constant)
        by_cases h : w ∈ [q,c,a,d]
        · exact Or.inl (Or.inr (hcell h))
        · apply Or.inr
          apply carryXorForward_covers input ds constant q d w hk (by simpa using hd)
          simp only [List.mem_cons,List.mem_append,List.not_mem_nil] at hw h ⊢
          tauto
  have heq : (circuitWires (controlledConstCarryXor (a :: input) dirty (true :: constant) q c)).dedup.toFinset =
      (q :: c :: (a :: input) ++ dirty).toFinset := by
    ext w; simpa using hmem w
  have hc := congrArg Finset.card heq
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_card_of_nodup hnd] at hc
  simpa [qubitCount,← hd,Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc

/-- The sparse correction `2^256 - p = 2^32 + 977` as 256 little-endian bits. -/
def secp256k1ReductionConstantBits : List Bool :=
  (List.range' 0 256).map (Nat.testBit (2 ^ 32 + 977))

/-- Control 0, clean carry 1, input 2–257, arbitrary borrowed output 258–513. -/
def secp256k1ReductionCarryXor : Circuit :=
  controlledConstCarryXor (List.range' 2 256) (List.range' 258 256)
    secp256k1ReductionConstantBits 0 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem secp256k1ReductionCarry_layout :
    (0 :: 1 :: List.range' 2 256 ++ List.range' 258 256).Nodup := by decide

set_option maxRecDepth 100000 in
private theorem secp256k1ReductionConstant_tailWeight :
    constantBitWeight ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) = 6 := by decide

set_option maxRecDepth 100000 in
/-- The constant word denotes the secp256k1 power-of-two correction exactly. -/
theorem secp256k1ReductionConstant_value :
    boolWordToNat secp256k1ReductionConstantBits = 2 ^ 32 + 977 := by decide

/-- Human-readable certificate for the actual 256-bit carry-XOR circuit. The borrowed word
is XORed with the carry bits of input + control*(2^32+977); all other wires are preserved.
The exact circuit uses 511 Toffolis, 47 CNOTs, 3,577 coherent T gates and 514 distinct wires.
This carry eraser is a component of constant arithmetic, not the complete modular adder. -/
theorem secp256k1ReductionCarryXor_correct_resources (s : BasisState) (hc : s 1 = false) :
    let after := run secp256k1ReductionCarryXor s
    wireValues (List.range' 258 256) after =
      List.zipWith Bool.xor (wireValues (List.range' 258 256) s)
        (constantCarryBits false (wireValues (List.range' 2 256) s)
          (secp256k1ReductionConstantBits.map (fun k => s 0 && k))) ∧
      (∀ w, w ∉ List.range' 258 256 → after w = s w) ∧
      boolWordToNat secp256k1ReductionConstantBits = 2 ^ 32 + 977 ∧
      CircuitWellFormed secp256k1ReductionCarryXor ∧ HPFree secp256k1ReductionCarryXor ∧
      eeaToffoliCount secp256k1ReductionCarryXor = 511 ∧
      eeaCnotCount secp256k1ReductionCarryXor = 47 ∧
      tCount secp256k1ReductionCarryXor = 3577 ∧ qubitCount secp256k1ReductionCarryXor = 514 := by
  have hk : (List.range' 2 256).length = secp256k1ReductionConstantBits.length := by
    simp [secp256k1ReductionConstantBits]
  have hd : (List.range' 2 256).length = (List.range' 258 256).length := by simp
  have hs := controlledConstCarryXor_correct _ _ _ 0 1 s hk hd secp256k1ReductionCarry_layout hc
  have hw := controlledConstCarryXor_wellFormed _ _ _ 0 1 hk hd secp256k1ReductionCarry_layout
  have he : secp256k1ReductionCarryXor = controlledConstCarryXor (2 :: List.range' 3 255)
      (List.range' 258 256) (true :: (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) 0 1 := rfl
  have hn := controlledConstCarryXor_counts 2 (List.range' 3 255) (List.range' 258 256) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) 0 1 (by simp) (by simp)
  have hq := controlledConstCarryXor_qubitCount 2 (List.range' 3 255) (List.range' 258 256)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) 0 1 (by simp) (by simp)
      secp256k1ReductionCarry_layout
  dsimp only
  refine ⟨hs.1,hs.2,secp256k1ReductionConstant_value,hw,?_,?_,?_,?_,?_⟩
  · rw [he]; exact hn.1
  · rw [he]; simpa only [List.length_range'] using hn.2.1
  · rw [he]; simpa only [secp256k1ReductionConstant_tailWeight,Bool.toNat_true] using hn.2.2.1
  · rw [he]; simpa only [List.length_range'] using hn.2.2.2
  · rw [he]; simpa only [List.length_range'] using hq

end ShorECDLP.Paper2607_13816
