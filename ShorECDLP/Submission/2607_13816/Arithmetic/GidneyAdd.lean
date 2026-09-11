import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceCorrections
import ShorECDLP.Submission.«2607_13816».Arithmetic.PrimitiveTransforms

/-!
# Measurement-assisted constant addition

The pinned `append_gidney_add_const_mod2n` reuses two carry wires and one constant-bit
ancilla. A carry is copied into a borrowed wire before its X-basis measurement/reset;
paired Z corrections on that borrowed word remove the measurement phases after cleanup.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

/-- One literal forward carry cell of the controlled constant adder. -/
def gidneyAddCarryCell (q current spare ancilla input dirty : Wire) (constant : Bool) : Circuit :=
  (if constant then [.CX q ancilla] else []) ++
    [.CX current ancilla, .CX current input, .CCX input ancilla spare,
      .CX current spare, .CX spare dirty, .CX current ancilla] ++
    (if constant then [.CX q ancilla, .CX q input] else [])

private def gidneyFlipWord (input : List Wire) : Circuit := input.map Gate.X

private def gidneyAddCleanup (input dirty : List Wire) (constant : List Bool) (q carry : Wire) : Circuit :=
  gidneyFlipWord input ++
    controlledConstCarryXor (input.take dirty.length) dirty (constant.take dirty.length) q carry ++
    gidneyFlipWord input

private def gidneyAddTail (q current spare ancilla : Wire)
    (onComplete : List Bool → Circuit) (outcomes : List Bool) :
    List Wire → List Wire → List Bool → Quantum.AdaptiveCircuit
  | [a], [], [k] =>
      .unitary ((if k then [.CX q a] else []) ++ [.CX current a])
        (.xMeasureReset current (.unitary (onComplete (outcomes ++ [false])) .done)
          (.unitary (onComplete (outcomes ++ [true])) .done))
  | a :: as, d :: ds, k :: ks =>
      .unitary (gidneyAddCarryCell q current spare ancilla a d k)
        (.xMeasureReset current
          (gidneyAddTail q spare current ancilla onComplete (outcomes ++ [false]) as ds ks)
          (gidneyAddTail q spare current ancilla onComplete (outcomes ++ [true]) as ds ks))
  | _, _, _ => .done

/-- Literal pinned controlled Gidney constant adder, including deferred phase corrections.
For nonzero width, `dirty` has one fewer wire than `input`, and all three clean wires start
at zero. The empty word is identity; width one is a single controlled constant-bit XOR. -/
def controlledGidneyAddConst (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) : Quantum.AdaptiveCircuit :=
  if constant.all (fun k => !k) then .done else
  match input, dirty, constant with
  | [a], [], [k] => .unitary (if k then [.CX q a] else []) .done
  | a :: as, d :: ds, k :: ks =>
      let onComplete := fun outcomes =>
        (Quantum.registerZCorrection (d :: ds) outcomes ++
          gidneyAddCleanup (a :: as) (d :: ds) (k :: ks) q carry ++
          Quantum.registerZCorrection (d :: ds) outcomes)
      .unitary (gidneyAddCarryCell q carry spare ancilla a d k)
        (gidneyAddTail q spare carry ancilla onComplete (List.nil : List Bool) as ds ks)
  | _, _, _ => .done

private theorem gidneyAddCarryCell_state (q c r t a d : Wire) (k : Bool) (s : BasisState)
    (hnd : [q,c,r,t,a,d].Nodup) (hr : s r = false) (ht : s t = false) :
    run (gidneyAddCarryCell q c r t a d k) s =
      upd (upd (upd s a (cuccaroSum (s a) (s q && k) (s c)))
        r (cuccaroCarry (s a) (s q && k) (s c)))
        d (Bool.xor (s d) (cuccaroCarry (s a) (s q && k) (s c))) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
  rcases hnd with ⟨⟨hqc,hqr,hqt,hqa,hqd⟩,⟨⟨hcr,hct,hca,hcd⟩,
    ⟨⟨hrt,hra,hrd⟩,⟨⟨hta,htd⟩,had,_⟩⟩⟩⟩
  funext w
  cases k <;>
    simp only [gidneyAddCarryCell,Bool.false_eq_true,↓reduceIte,
      List.nil_append,List.append_nil,run_append,run_cons,run_nil,applyGate]
  all_goals
    by_cases hwq : w = q <;> by_cases hwc : w = c <;> by_cases hwr : w = r <;>
      by_cases hwt : w = t <;> by_cases hwa : w = a <;> by_cases hwd : w = d <;>
      simp_all [upd,cuccaroSum,cuccaroCarry,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm,
        Ne.symm hqc,Ne.symm hqr,Ne.symm hqt,Ne.symm hqa,Ne.symm hqd,
        Ne.symm hcr,Ne.symm hct,Ne.symm hca,Ne.symm hcd,
        Ne.symm hrt,Ne.symm hra,Ne.symm hrd,Ne.symm hta,Ne.symm htd,Ne.symm had]
  all_goals cases hsa : s a <;> cases hsc : s c <;> cases hsq : s q <;> cases hsd : s d <;> simp_all

private theorem gidneyComplementedSumCarry (a k c : Bool) :
    cuccaroCarry (!(cuccaroSum a k c)) k c = cuccaroCarry a k c := by
  cases a <;> cases k <;> cases c <;> decide

private theorem gidneyComplementedSumCarries (input constant : List Bool) (carry : Bool)
    (hk : input.length = constant.length) :
    constantCarryBits carry ((cuccaroAddBits carry input constant).map Bool.not) constant =
      constantCarryBits carry input constant := by
  induction input generalizing constant carry with
  | nil => cases constant <;> simp_all [constantCarryBits,cuccaroAddBits]
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      simp only [cuccaroAddBits,List.map_cons,constantCarryBits]
      rw [gidneyComplementedSumCarry,ih ks (cuccaroCarry a k carry) (by simpa using hk)]

private theorem gidneyAddCarryCell_resources (q c r t a d : Wire) (k : Bool) :
    HPFree (gidneyAddCarryCell q c r t a d k) ∧
      eeaToffoliCount (gidneyAddCarryCell q c r t a d k) = 1 ∧
      eeaCnotCount (gidneyAddCarryCell q c r t a d k) = 5 + 3 * k.toNat ∧
      tCount (gidneyAddCarryCell q c r t a d k) = 7 := by
  cases k <;> simp [gidneyAddCarryCell,eeaToffoliCount,eeaCnotCount,tCount,tCost]

private def gidneyCarryCellState (q c r a d : Wire) (k : Bool) (s : BasisState) : BasisState :=
  upd (upd (upd s a (cuccaroSum (s a) (s q && k) (s c)))
    r (cuccaroCarry (s a) (s q && k) (s c)))
    d (Bool.xor (s d) (cuccaroCarry (s a) (s q && k) (s c)))

/-- Circuit-free forward trace: the final basis state and the carries being measured,
listed chronologically. The two physical carry roles alternate after each reset. -/
private def gidneyTailTrace (q current spare : Wire) :
    List Wire → List Wire → List Bool → BasisState → BasisState × List Bool
  | [a], [], [k], s =>
      (upd (upd s a (cuccaroSum (s a) (s q && k) (s current))) current false, [s current])
  | a :: as, d :: ds, k :: ks, s =>
      let mid := gidneyCarryCellState q current spare a d k s
      let next := gidneyTailTrace q spare current as ds ks (upd mid current false)
      (next.1, s current :: next.2)
  | _, _, _, s => (s, [])

private def gidneyTailReady (q current spare ancilla : Wire) :
    List Wire → List Wire → List Bool → BasisState → Prop
  | [a], [], [_], _ => q ≠ a ∧ current ≠ a
  | a :: as, d :: ds, k :: ks, s =>
      [q,current,spare,ancilla,a,d].Nodup ∧ s spare = false ∧ s ancilla = false ∧
        gidneyTailReady q spare current ancilla as ds ks
          (upd (gidneyCarryCellState q current spare a d k s) current false)
  | _, _, _, _ => False

private theorem gidneyTop_state (q c a : Wire) (k : Bool) (s : BasisState)
    (_hqa : q ≠ a) (hca : c ≠ a) :
    run ((if k then [.CX q a] else []) ++ [.CX c a]) s =
      upd s a (cuccaroSum (s a) (s q && k) (s c)) := by
  funext w
  cases k <;> by_cases hwa : w = a <;>
    simp [run_append,run,applyGate,upd,_hqa,hca,hwa,cuccaroSum,Bool.xor_comm,
      Bool.xor_left_comm,Bool.xor_assoc]

private theorem gidneyCell_current (q c r t a d : Wire) (k : Bool) (s : BasisState)
    (hnd : [q,c,r,t,a,d].Nodup) : gidneyCarryCellState q c r a d k s c = s c := by
  have hc := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hcr : c ≠ r := by intro h; apply hc; simp [h]
  have hca : c ≠ a := by intro h; apply hc; simp [h]
  have hcd : c ≠ d := by intro h; apply hc; simp [h]
  simp [gidneyCarryCellState,upd,hcr,hca,hcd]

private theorem gidneyTail_branch (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (s : BasisState) (onComplete : List Bool → Circuit) (historyPrefix : List Bool)
    (hready : gidneyTailReady q c r t input dirty constant s)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (gidneyAddTail q c r t onComplete historyPrefix input dirty constant).run) :
    ∃ outcomes, branch.history = outcomes ∧ outcomes.length = input.length ∧
      branch.kraus (Quantum.ket s) =
        gidneyRawCoefficient outcomes (gidneyTailTrace q c r input dirty constant s).2 •
          Quantum.run (onComplete (historyPrefix ++ outcomes))
            (Quantum.ket (gidneyTailTrace q c r input dirty constant s).1) := by
  induction input generalizing dirty constant c r s historyPrefix branch with
  | nil => simp [gidneyTailReady] at hready
  | cons a as ih =>
    cases dirty with
    | nil =>
      cases as with
      | cons a' as => simp [gidneyTailReady] at hready
      | nil =>
        cases constant with
        | nil => simp [gidneyTailReady] at hready
        | cons k ks =>
          cases ks with
          | cons k' ks => simp [gidneyTailReady] at hready
          | nil =>
            have hp := gidneyTop_state q c a k s hready.1 hready.2
            let mid := upd s a (cuccaroSum (s a) (s q && k) (s c))
            have hmc : mid c = s c := by simp [mid,upd,hready.2]
            obtain ⟨measured,hm,hhist,hsem⟩ := gidneyUnitaryBranch _ _ branch hb
            obtain ⟨outcome,rest,hr,hrest,hmeasure⟩ := gidneyMeasureBranch c _ _ measured hm
            have hr' : rest ∈ (Quantum.AdaptiveCircuit.unitary (onComplete (historyPrefix ++ [outcome])) .done).run := by
              cases outcome <;> exact hr
            obtain ⟨last,hl,hlhist,hlsem⟩ := gidneyUnitaryBranch _ _ rest hr'
            have hlast := gidneyDoneBranch last hl
            refine ⟨[outcome],?_,rfl,?_⟩
            · rw [hhist,hrest,hlhist,hlast.1]
            · rw [hsem,Quantum.run_ket_agrees_classical _ s (by cases k <;> simp),hp]
              change measured.kraus (Quantum.ket mid) = _
              rw [hmeasure,Quantum.xResetKraus_ket,hmc,map_smul,hlsem,hlast.2]
              simp only [gidneyTailTrace,gidneyRawCoefficient,mul_one]
              rfl
    | cons d ds =>
      cases constant with
      | nil => simp [gidneyTailReady] at hready
      | cons k ks =>
        simp only [gidneyTailReady] at hready
        rcases hready with ⟨hnd,hr,ht,hnext⟩
        let mid := gidneyCarryCellState q c r a d k s
        let cleared := upd mid c false
        have hmc : mid c = s c := gidneyCell_current q c r t a d k s hnd
        simp only [gidneyAddTail] at hb
        obtain ⟨measured,hm,hist,hsem⟩ := gidneyUnitaryBranch _ _ branch hb
        obtain ⟨outcome,rest,hrest,hrestHist,hmeasure⟩ := gidneyMeasureBranch c _ _ measured hm
        have hrest' : rest ∈ (gidneyAddTail q r c t onComplete (historyPrefix ++ [outcome]) as ds ks).run := by
          cases outcome <;> exact hrest
        obtain ⟨outcomes,hout,hcount,hresult⟩ := ih ds ks r c cleared (historyPrefix ++ [outcome]) hnext rest hrest'
        refine ⟨outcome :: outcomes,?_,by simp [hcount],?_⟩
        · rw [hist,hrestHist,hout]
        · rw [hsem,Quantum.run_ket_agrees_classical _ s (gidneyAddCarryCell_resources q c r t a d k).1,
            gidneyAddCarryCell_state q c r t a d k s hnd hr ht]
          change measured.kraus (Quantum.ket mid) = _
          rw [hmeasure,Quantum.xResetKraus_ket,hmc,map_smul]
          change Quantum.xResetCoeff outcome (s c) • rest.kraus (Quantum.ket cleared) = _
          rw [hresult]
          simp only [gidneyTailTrace,gidneyRawCoefficient,smul_smul,List.append_assoc,List.singleton_append]
          rfl

private theorem gidneyLayoutStep (q c r t a d : Wire) (input dirty : List Wire)
    (hnd : ([q,c,r,t] ++ (a :: input) ++ d :: dirty).Nodup) :
    [q,c,r,t,a,d].Nodup ∧ ([q,r,c,t] ++ input ++ dirty).Nodup := by
  have hsA : [a].Sublist (a :: input) := List.Sublist.cons₂ a (List.nil_sublist _)
  have hsD : [d].Sublist (d :: dirty) := List.Sublist.cons₂ d (List.nil_sublist _)
  have hcell := List.Nodup.sublist (((List.Sublist.refl [q,c,r,t]).append hsA).append hsD) hnd
  have htail := List.Nodup.sublist
    (((List.Sublist.refl [q,c,r,t]).append (List.sublist_cons_self a input)).append
      (List.sublist_cons_self d dirty)) hnd
  have hperm : ([q,r,c,t] ++ input ++ dirty).Perm ([q,c,r,t] ++ input ++ dirty) := by
    exact List.Perm.cons q (List.Perm.swap c r (t :: input ++ dirty))
  exact ⟨hcell,hperm.nodup_iff.mpr htail⟩

private theorem gidneyCell_reset_clean (q c r t a d : Wire) (k : Bool) (s : BasisState)
    (hnd : [q,c,r,t,a,d].Nodup) (ht : s t = false) :
    (upd (gidneyCarryCellState q c r a d k s) c false) c = false ∧
      (upd (gidneyCarryCellState q c r a d k s) c false) t = false := by
  have hne : t ≠ c ∧ t ≠ r ∧ t ≠ a ∧ t ≠ d := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
    aesop
  simp [gidneyCarryCellState,upd,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2,ht]

private theorem gidneyTailReady_of_layout (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length + 1)
    (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup) (hr : s r = false) (ht : s t = false) :
    gidneyTailReady q c r t input dirty constant s := by
  induction input generalizing dirty constant c r s with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        simp only [gidneyTailReady]
        simp only [List.append_nil,List.nil_append,List.cons_append,List.nodup_cons,List.mem_cons,
          List.not_mem_nil,or_false,not_or] at hnd
        tauto
      | cons d ds =>
        have hl := gidneyLayoutStep q c r t a d as ds hnd
        have hclean := gidneyCell_reset_clean q c r t a d k s hl.1 ht
        simp only [gidneyTailReady]
        refine ⟨hl.1,hr,ht,?_⟩
        exact ih ds ks r c _ (by simpa using hk) (by simpa using hd)
          hl.2 hclean.1 hclean.2

private theorem gidneyTailTrace_frame (input dirty : List Wire) (constant : List Bool)
    (q c r w : Wire) (s : BasisState) (hw : w ∉ c :: r :: input ++ dirty) :
    (gidneyTailTrace q c r input dirty constant s).1 w = s w := by
  induction input generalizing dirty constant c r s with
  | nil => simp [gidneyTailTrace]
  | cons a as ih =>
    have hwa : w ≠ a := by intro h; apply hw; simp [h]
    have hwc : w ≠ c := by intro h; apply hw; simp [h]
    have hwr : w ≠ r := by intro h; apply hw; simp [h]
    cases dirty with
    | nil =>
      cases as <;> cases constant with
      | nil => simp [gidneyTailTrace]
      | cons k ks =>
        cases ks <;> simp [gidneyTailTrace,upd,hwa,hwc]
    | cons d ds =>
      cases constant with
      | nil => simp [gidneyTailTrace]
      | cons k ks =>
        have hwd : w ≠ d := by intro h; apply hw; simp [h]
        have htail : w ∉ r :: c :: as ++ ds := by
          simp only [List.mem_append,List.mem_cons] at hw ⊢
          tauto
        simp only [gidneyTailTrace]
        rw [ih ds ks r c _ htail]
        simp [gidneyCarryCellState,upd,hwa,hwc,hwr,hwd]

private theorem gidneyTailTrace_arithmetic (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup) :
    let result := gidneyTailTrace q c r input dirty constant s
    let carries := constantCarryBits (s c) (wireValues input s) (constant.map (fun k => s q && k))
    wireValues input result.1 = cuccaroAddBits (s c) (wireValues input s) (constant.map (fun k => s q && k)) ∧
      wireValues dirty result.1 = List.zipWith Bool.xor (wireValues dirty s) (carries.take dirty.length) ∧
      result.2 = s c :: carries.take dirty.length := by
  induction input generalizing dirty constant c r s with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        have hca : a ≠ c := by
          simp only [List.append_nil,List.nil_append,List.cons_append,List.nodup_cons,
            List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
          aesop
        simp [gidneyTailTrace,wireValues,upd,hca,cuccaroAddBits]
      | cons d ds =>
        have hl := gidneyLayoutStep q c r t a d as ds hnd
        have hperm : ([q,c,r,t] ++ (a :: as) ++ d :: ds).Perm ([q,c,r,t,a,d] ++ as ++ ds) := by
          simpa only [List.cons_append,List.nil_append,List.append_assoc] using
            (List.perm_middle (a := d) (l₁ := as) (l₂ := ds)).append_left [q,c,r,t,a]
        have hsplit := List.nodup_append.mp (show ([q,c,r,t,a,d] ++ (as ++ ds)).Nodup by
          simpa only [List.append_assoc] using hperm.nodup_iff.mp hnd)
        have hnotTail (w : Wire) (hw : w ∈ [q,c,r,t,a,d]) : w ∉ as ++ ds :=
          fun hw' => hsplit.2.2 w hw w hw' rfl
        have hnotHead (w : Wire) (hw : w ∈ as ++ ds) : w ∉ [q,c,r,t,a,d] :=
          fun hw' => hsplit.2.2 w hw' w hw rfl
        have hcell := hl.1
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hcell
        rcases hcell with ⟨⟨hqc,hqr,hqt,hqa,hqd⟩,⟨⟨hcr,hct,hca,hcd⟩,
          ⟨⟨hrt,hra,hrd⟩,⟨⟨hta,htd⟩,had,_⟩⟩⟩⟩
        let next := cuccaroCarry (s a) (s q && k) (s c)
        let cleared := upd (gidneyCarryCellState q c r a d k s) c false
        have hframe (w : Wire) (hw : w ∉ [a,d,c,r]) : cleared w = s w := by
          have hp : w ≠ a ∧ w ≠ d ∧ w ≠ c ∧ w ≠ r := by simpa using hw
          simp [cleared,gidneyCarryCellState,upd,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
        have hq : cleared q = s q := hframe q (by simp [hqa,hqd,hqc,hqr])
        have ha : cleared a = cuccaroSum (s a) (s q && k) (s c) := by
          simp [cleared,gidneyCarryCellState,upd,had,Ne.symm hca,Ne.symm hra]
        have hdv : cleared d = Bool.xor (s d) next := by
          simp [cleared,gidneyCarryCellState,upd,Ne.symm hcd,next]
        have hrv : cleared r = next := by
          simp [cleared,gidneyCarryCellState,upd,hrd,Ne.symm hcr,next]
        have hread (ws : List Wire) (hs : ∀ w ∈ ws, w ∈ as ++ ds) : wireValues ws cleared = wireValues ws s := by
          apply List.map_congr_left
          intro w hw
          apply hframe
          have hn := hnotHead w (hs w hw)
          simp only [List.mem_cons,List.not_mem_nil] at hn ⊢
          tauto
        have hinput := hread as (by intro w hw; simp [hw])
        have hdirty := hread ds (by intro w hw; simp [hw])
        have hheadA : a ∉ r :: c :: as ++ ds := by
          simpa only [List.cons_append,List.mem_cons,not_or] using
            And.intro (Ne.symm hra) (And.intro (Ne.symm hca) (hnotTail a (by simp)))
        have hheadD : d ∉ r :: c :: as ++ ds := by
          simpa only [List.cons_append,List.mem_cons,not_or] using
            And.intro (Ne.symm hrd) (And.intro (Ne.symm hcd) (hnotTail d (by simp)))
        have ht := ih ds ks r c cleared (by simpa using hk) (by simpa using hd) hl.2
        dsimp only at ht ⊢
        simp only [gidneyTailTrace]
        constructor
        · change (gidneyTailTrace q r c as ds ks cleared).1 a ::
            wireValues as (gidneyTailTrace q r c as ds ks cleared).1 = _
          rw [gidneyTailTrace_frame as ds ks q r c a cleared hheadA,ht.1,ha,hrv,hinput,hq]
          rfl
        · constructor
          · change (gidneyTailTrace q r c as ds ks cleared).1 d ::
              wireValues ds (gidneyTailTrace q r c as ds ks cleared).1 = _
            rw [gidneyTailTrace_frame as ds ks q r c d cleared hheadD,ht.2.1,hdv,hrv,hinput,hq,hdirty]
            rfl
          · rw [ht.2.2,hrv,hinput,hq]
            rfl

private theorem gidneyTailTrace_clean (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup)
    (hr : s r = false) :
    (gidneyTailTrace q c r input dirty constant s).1 c = false ∧
      (gidneyTailTrace q c r input dirty constant s).1 r = false := by
  induction input generalizing dirty constant c r s with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        have hrc : r ≠ c ∧ r ≠ a := by
          simp only [List.append_nil,List.nil_append,List.cons_append,List.nodup_cons,
            List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
          aesop
        simp [gidneyTailTrace,upd,hrc.1,hrc.2,hr]
      | cons d ds =>
        have hl := gidneyLayoutStep q c r t a d as ds hnd
        have ht := ih ds ks r c (upd (gidneyCarryCellState q c r a d k s) c false)
          (by simpa using hk) (by simpa using hd) hl.2 (by simp [upd])
        simpa only [gidneyTailTrace] using And.intro ht.2 ht.1

private def gidneyWriteBits : List Wire → List Bool → BasisState → BasisState
  | w :: ws, b :: bs, s => gidneyWriteBits ws bs (upd s w b)
  | _, _, s => s

/-- Direct arithmetic ideal: change only the input word to its controlled fixed-width sum. -/
def gidneyAddIdealState (input : List Wire) (constant : List Bool) (q : Wire) (s : BasisState) : BasisState :=
  gidneyWriteBits input (cuccaroAddBits false (wireValues input s) (constant.map (fun k => s q && k))) s

private theorem gidneyWriteBits_frame (ws : List Wire) (bits : List Bool) (s : BasisState)
    (w : Wire) (hw : w ∉ ws) : gidneyWriteBits ws bits s w = s w := by
  induction ws generalizing bits s with
  | nil => rfl
  | cons a as ih =>
    cases bits with
    | nil => rfl
    | cons b bs =>
      have hwa : w ≠ a := by intro h; exact hw (by simp [h])
      have hwas : w ∉ as := by intro h; exact hw (by simp [h])
      rw [gidneyWriteBits,ih bs _ hwas]
      simp [upd,hwa]

private theorem gidneyWriteBits_values (ws : List Wire) (bits : List Bool) (s : BasisState)
    (hnd : ws.Nodup) (hlen : ws.length = bits.length) :
    wireValues ws (gidneyWriteBits ws bits s) = bits := by
  induction ws generalizing bits s with
  | nil => cases bits <;> simp_all [wireValues]
  | cons a as ih =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have ht := List.nodup_cons.mp hnd
      change gidneyWriteBits as bs (upd s a b) a :: wireValues as (gidneyWriteBits as bs (upd s a b)) = _
      rw [gidneyWriteBits_frame as bs (upd s a b) a ht.1,ih bs _ ht.2 (by simpa using hlen)]
      simp [upd]

private theorem gidneyState_ext (ws : List Wire) (left right : BasisState)
    (hwords : wireValues ws left = wireValues ws right)
    (hframe : ∀ w, w ∉ ws → left w = right w) : left = right := by
  funext w
  by_cases hw : w ∈ ws
  · exact List.map_inj_left.mp hwords w hw
  · exact hframe w hw

private theorem gidneyFlipWord_state (ws : List Wire) (s : BasisState) (hnd : ws.Nodup) :
    run (gidneyFlipWord ws) s = fun w => if w ∈ ws then !s w else s w := by
  induction ws generalizing s with
  | nil => simp [gidneyFlipWord]
  | cons a as ih =>
    have ht := List.nodup_cons.mp hnd
    change run (gidneyFlipWord as) (applyGate (.X a) s) = _
    rw [ih _ ht.2]
    funext w
    by_cases hwa : w = a
    · subst w; simp [ht.1,applyGate,upd]
    · simp [hwa,applyGate,upd]

private theorem gidneyCarryBits_take (input constant : List Bool) (carry : Bool) (n : Nat) :
    constantCarryBits carry (input.take n) (constant.take n) =
      (constantCarryBits carry input constant).take n := by
  induction n generalizing input constant carry with
  | zero => simp [constantCarryBits]
  | succ n ih =>
    cases input <;> cases constant <;> simp [constantCarryBits,ih]

private theorem gidneyAddCleanup_correct (input dirty : List Wire) (constant : List Bool)
    (q c : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : dirty.length ≤ input.length) (hnd : (q :: c :: input ++ dirty).Nodup)
    (hc : s c = false) :
    wireValues dirty (run (gidneyAddCleanup input dirty constant q c) s) =
      List.zipWith Bool.xor (wireValues dirty s)
        ((constantCarryBits false ((wireValues input s).map Bool.not)
          (constant.map (fun k => s q && k))).take dirty.length) ∧
      (∀ w, w ∉ dirty → run (gidneyAddCleanup input dirty constant q c) s w = s w) := by
  have hq := (List.nodup_cons.mp hnd).1
  have ht := (List.nodup_cons.mp hnd).2
  have hcOut := (List.nodup_cons.mp ht).1
  have hp := List.nodup_append.mp (List.nodup_cons.mp ht).2
  have hqi : q ∉ input := by intro h; apply hq; change q ∈ c :: input ++ dirty; simp [h]
  have hci : c ∉ input := by intro h; apply hcOut; change c ∈ input ++ dirty; simp [h]
  have hdi (w : Wire) (hw : w ∈ dirty) : w ∉ input := fun h => hp.2.2 w h w hw rfl
  have hshort : (q :: c :: input.take dirty.length ++ dirty).Nodup := by
    apply List.Nodup.sublist (l₂ := q :: c :: input ++ dirty) ?_ hnd
    exact ((List.Sublist.refl [q,c]).append (List.take_sublist _ _)).append (List.Sublist.refl dirty)
  let mid := run (gidneyFlipWord input) s
  have hmid : mid = fun w => if w ∈ input then !s w else s w := gidneyFlipWord_state input s hp.1
  have hmq : mid q = s q := by simp [hmid,hqi]
  have hmc : mid c = false := by simp [hmid,hci,hc]
  have hmInput : wireValues (input.take dirty.length) mid =
      (((wireValues input s).map Bool.not).take dirty.length) := by
    rw [← List.map_take]
    change (input.take dirty.length).map mid = _
    simp only [wireValues,List.map_map,← List.map_take]
    apply List.map_congr_left
    intro w hw
    have hwi : w ∈ input := List.mem_of_mem_take hw
    simp [hmid,hwi]
  have hmDirty : wireValues dirty mid = wireValues dirty s := by
    apply List.map_congr_left; intro w hw; simp [hmid,hdi w hw]
  let middle := run (controlledConstCarryXor (input.take dirty.length) dirty
    (constant.take dirty.length) q c) mid
  have hx := controlledConstCarryXor_correct (input.take dirty.length) dirty
    (constant.take dirty.length) q c mid (by simp [hk])
    (by simp [List.length_take,Nat.min_eq_left hd]) hshort hmc
  rw [gidneyAddCleanup,run_append,run_append]
  change wireValues dirty (run (gidneyFlipWord input) middle) = _ ∧ _
  rw [gidneyFlipWord_state input middle hp.1]
  constructor
  · have hlast : wireValues dirty (fun w => if w ∈ input then !middle w else middle w) =
        wireValues dirty middle := by
      apply List.map_congr_left; intro w hw; simp [hdi w hw]
    rw [hlast,hx.1,hmDirty,hmInput,hmq,List.map_take,gidneyCarryBits_take]
  · intro w hw
    have he : middle w = mid w := hx.2 w hw
    simp only [he,hmid]
    by_cases hwi : w ∈ input <;> simp [hwi]

private theorem gidneyNontrivial_branch (a d q c r t : Wire) (input dirty : List Wire)
    (k : Bool) (constant : List Bool) (s : BasisState) (onComplete : List Bool → Circuit)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (hnd : ([q,c,r,t] ++ (a :: input) ++ d :: dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (Quantum.AdaptiveCircuit.unitary (gidneyAddCarryCell q c r t a d k)
      (gidneyAddTail q r c t onComplete (List.nil : List Bool) input dirty constant)).run) :
    ∃ outcomes, branch.history = outcomes ∧ outcomes.length = (d :: dirty).length ∧
      branch.kraus (Quantum.ket s) =
        gidneyRawCoefficient outcomes
          ((constantCarryBits false (wireValues (a :: input) s)
            ((k :: constant).map (fun k => s q && k))).take (d :: dirty).length) •
          Quantum.run (onComplete outcomes)
            (Quantum.ket (gidneyTailTrace q c r (a :: input) (d :: dirty) (k :: constant) s).1) := by
  have hl := gidneyLayoutStep q c r t a d input dirty hnd
  let mid := gidneyCarryCellState q c r a d k s
  have hmc : mid c = false := (gidneyCell_current q c r t a d k s hl.1).trans hc
  have hreset : upd mid c false = mid := by
    funext w
    by_cases hw : w = c <;> simp [upd,hw,hmc]
  have hclean := gidneyCell_reset_clean q c r t a d k s hl.1 ht
  change (upd mid c false) c = false ∧ (upd mid c false) t = false at hclean
  rw [hreset] at hclean
  have hready := gidneyTailReady_of_layout input dirty constant q r c t mid hk hd hl.2 hclean.1 hclean.2
  obtain ⟨rest,hrest,hhist,hsem⟩ := gidneyUnitaryBranch _ _ branch hb
  obtain ⟨outcomes,hout,hcount,hresult⟩ := gidneyTail_branch input dirty constant q r c t mid
    onComplete (List.nil : List Bool) hready rest hrest
  have harith := gidneyTailTrace_arithmetic (a :: input) (d :: dirty) (k :: constant) q c r t s
    (by simpa using hk) (by simpa using hd) hnd
  have hrecord := congrArg List.tail harith.2.2
  simp only [gidneyTailTrace,List.tail_cons] at hrecord
  change (gidneyTailTrace q r c input dirty constant (upd mid c false)).2 = _ at hrecord
  rw [hreset,hc] at hrecord
  refine ⟨outcomes,hhist.trans hout,by simpa [hd] using hcount,?_⟩
  rw [hsem,Quantum.run_ket_agrees_classical _ s (gidneyAddCarryCell_resources q c r t a d k).1,
    gidneyAddCarryCell_state q c r t a d k s hl.1 hr ht]
  change rest.kraus (Quantum.ket mid) = _
  rw [hresult,hrecord]
  simp only [gidneyTailTrace,List.nil_append]
  change _ = _ • Quantum.run (onComplete outcomes)
    (Quantum.ket (gidneyTailTrace q r c input dirty constant (upd mid c false)).1)
  rw [hreset]

private theorem gidneyCleanup_after_forward (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) :
    run (gidneyAddCleanup input dirty constant q c)
      (gidneyTailTrace q c r input dirty constant s).1 = gidneyAddIdealState input constant q s := by
  have hshort : (q :: c :: input ++ dirty).Nodup := by
    apply List.Nodup.sublist (l₂ := [q,c,r,t] ++ input ++ dirty) ?_ hnd
    exact List.Sublist.cons₂ q (List.Sublist.cons₂ c
      (List.Sublist.cons r (List.Sublist.cons t (List.Sublist.refl (input ++ dirty)))))
  have hp := List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp hshort).2).2
  have hqf : (gidneyTailTrace q c r input dirty constant s).1 q = s q := by
    apply gidneyTailTrace_frame input dirty constant q c r q s
    have hn := (List.nodup_cons.mp hnd).1
    intro hw; apply hn
    change q ∈ c :: r :: t :: input ++ dirty
    simp only [List.mem_append,List.mem_cons] at hw ⊢
    tauto
  let forward := (gidneyTailTrace q c r input dirty constant s).1
  let carries := (constantCarryBits false (wireValues input s) (constant.map (fun k => s q && k))).take dirty.length
  have hbits : (wireValues input s).length = (constant.map (fun k => s q && k)).length := by simp [wireValues,hk]
  have hlength : carries.length = dirty.length := by
    rw [show carries = (constantCarryBits false (wireValues input s) (constant.map (fun k => s q && k))).take dirty.length from rfl, List.length_take, gidneyCarryBits_length _ _ false hbits]
    simp only [wireValues,List.length_map]
    exact Nat.min_eq_left (by omega)
  have htrace := gidneyTailTrace_arithmetic input dirty constant q c r t s hk hd hnd
  have hfInput : wireValues input forward = cuccaroAddBits false (wireValues input s) (constant.map (fun k => s q && k)) := by
    simpa only [hc] using htrace.1
  have hfDirty : wireValues dirty forward = List.zipWith Bool.xor (wireValues dirty s) carries := by
    simpa only [hc] using htrace.2.1
  have hclean := gidneyTailTrace_clean input dirty constant q c r t s hk hd hnd hr
  have hx := gidneyAddCleanup_correct input dirty constant q c forward hk (by omega) hshort hclean.1
  change forward q = s q at hqf
  rw [hfInput,hqf,gidneyComplementedSumCarries _ _ false hbits] at hx
  have hafterDirty : wireValues dirty (run (gidneyAddCleanup input dirty constant q c) forward) = wireValues dirty s := by
    rw [hx.1,hfDirty]
    apply gidneyXorWord_cancel
    simp only [wireValues,List.length_map,hlength]
  have hafterInput : wireValues input (run (gidneyAddCleanup input dirty constant q c) forward) = wireValues input forward := by
    apply List.map_congr_left
    intro w hw
    apply hx.2 w
    intro hdw; exact hp.2.2 w hw w hdw rfl
  apply gidneyState_ext input
  · rw [hafterInput,hfInput]
    exact (gidneyWriteBits_values input _ s hp.1 (by
      rw [cuccaroAddBits_length false _ _ hbits]; simp [wireValues])).symm
  · intro w hwi
    change run (gidneyAddCleanup input dirty constant q c) forward w = gidneyWriteBits input _ s w
    rw [gidneyWriteBits_frame input _ s w hwi]
    by_cases hwd : w ∈ dirty
    · exact List.map_inj_left.mp hafterDirty w hwd
    · rw [hx.2 w hwd]
      by_cases hwc : w = c
      · subst w; exact hclean.1.trans hc.symm
      · by_cases hwr : w = r
        · subst w; exact hclean.2.trans hr.symm
        · apply gidneyTailTrace_frame input dirty constant q c r w s
          simpa only [List.cons_append,List.mem_cons,List.mem_append,not_or] using
            And.intro hwc (And.intro hwr (And.intro hwi hwd))

private theorem gidneyAddCleanup_HPFree (input dirty : List Wire) (constant : List Bool)
    (q c : Wire) (hk : input.length = constant.length) (hd : dirty.length ≤ input.length) :
    HPFree (gidneyAddCleanup input dirty constant q c) := by
  have hx := gidneyCarryXor_HPFree (input.take dirty.length) dirty (constant.take dirty.length) q c
    (by simp [hk]) (by simp [List.length_take,Nat.min_eq_left hd])
  have hf : HPFree (gidneyFlipWord input) := by simp [gidneyFlipWord,HPFree]
  simp [gidneyAddCleanup,hx,hf]

private theorem gidneyCorrected_branch (a d q c r t : Wire) (input dirty : List Wire)
    (k : Bool) (constant : List Bool) (s : BasisState)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (hnd : ([q,c,r,t] ++ (a :: input) ++ d :: dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (Quantum.AdaptiveCircuit.unitary (gidneyAddCarryCell q c r t a d k)
      (gidneyAddTail q r c t (fun outcomes => Quantum.registerZCorrection (d :: dirty) outcomes ++
        gidneyAddCleanup (a :: input) (d :: dirty) (k :: constant) q c ++
        Quantum.registerZCorrection (d :: dirty) outcomes)
        (List.nil : List Bool) input dirty constant)).run) :
    branch.history.length = (d :: dirty).length ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude (d :: dirty).length •
        Quantum.ket (gidneyAddIdealState (a :: input) (k :: constant) q s) := by
  obtain ⟨outcomes,hist,hlen,hbranch⟩ := gidneyNontrivial_branch a d q c r t input dirty k constant s _
    hk hd hnd hc hr ht branch hb
  let forward := (gidneyTailTrace q c r (a :: input) (d :: dirty) (k :: constant) s).1
  let ideal := gidneyAddIdealState (a :: input) (k :: constant) q s
  let carries := (constantCarryBits false (wireValues (a :: input) s)
    ((k :: constant).map (fun k => s q && k))).take (d :: dirty).length
  have hbits : (wireValues (a :: input) s).length = ((k :: constant).map (fun k => s q && k)).length := by simp [wireValues,hk]
  have hcarrylen : carries.length = (d :: dirty).length := by
    rw [show carries = (constantCarryBits false (wireValues (a :: input) s)
      ((k :: constant).map (fun k => s q && k))).take (d :: dirty).length from rfl,
      List.length_take,gidneyCarryBits_length _ _ false hbits]
    simp only [wireValues,List.length_map,List.length_cons]
    exact Nat.min_eq_left (by omega)
  have hclean := gidneyCleanup_after_forward (a :: input) (d :: dirty) (k :: constant) q c r t s
    (by simpa using hk) (by simpa using hd) hnd hc hr
  change run (gidneyAddCleanup (a :: input) (d :: dirty) (k :: constant) q c) forward = ideal at hclean
  have hp := List.nodup_append.mp hnd
  have hdata := List.nodup_append.mp hp.1
  have hdirtyIdeal : wireValues (d :: dirty) ideal = wireValues (d :: dirty) s := by
    apply List.map_congr_left
    intro w hw
    apply gidneyWriteBits_frame
    intro hwi
    exact hp.2.2 w (List.mem_append_right _ hwi) w hw rfl
  have htrace := gidneyTailTrace_arithmetic (a :: input) (d :: dirty) (k :: constant) q c r t s
    (by simpa using hk) (by simpa using hd) hnd
  have hxor : wireValues (d :: dirty) forward = List.zipWith Bool.xor (wireValues (d :: dirty) ideal) carries := by
    rw [hdirtyIdeal]
    simpa only [hc] using htrace.2.1
  have hphase := gidneyBorrowedPhaseCancellation (d :: dirty) outcomes carries forward ideal hcarrylen.symm hxor
  refine ⟨by rw [hist,hlen],?_⟩
  rw [hbranch]
  change gidneyRawCoefficient outcomes carries • Quantum.run
    ((Quantum.registerZCorrection (d :: dirty) outcomes ++
      gidneyAddCleanup (a :: input) (d :: dirty) (k :: constant) q c) ++
      Quantum.registerZCorrection (d :: dirty) outcomes) (Quantum.ket forward) = _
  rw [Quantum.run_append,Quantum.run_append,Quantum.run_registerZCorrection_ket,map_smul,
    Quantum.run_ket_agrees_classical _ forward (gidneyAddCleanup_HPFree _ _ _ q c (by simpa using hk) (by simp; omega)),
    hclean,map_smul,Quantum.run_registerZCorrection_ket]
  rw [gidneyRawCoefficient_phase outcomes carries (hlen.trans hcarrylen.symm)]
  simp only [smul_smul]
  have hscalar : (Quantum.registerXResetMagnitude outcomes.length * gidneyRecordedPhase outcomes carries) *
      (Quantum.registerXPhase (d :: dirty) outcomes forward * Quantum.registerXPhase (d :: dirty) outcomes ideal) =
        Quantum.registerXResetMagnitude (d :: dirty).length := by
    rw [mul_assoc,← mul_assoc (gidneyRecordedPhase outcomes carries),hphase,mul_one,hlen]
  rw [hscalar]

private theorem gidneyZeroSum (input constant : List Bool) (control : Bool)
    (hk : input.length = constant.length) (hz : constant.all (fun k => !k) = true) :
    cuccaroAddBits false input (constant.map (fun k => control && k)) = input := by
  induction input generalizing constant with
  | nil => cases constant <;> simp_all [cuccaroAddBits]
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      have hkf : k = false := by cases k <;> simp_all
      subst k
      have ht : ks.all (fun k => !k) = true := by simpa using hz
      cases a <;> simp [cuccaroAddBits,cuccaroSum,cuccaroCarry,ih ks (by simpa using hk) ht]

private theorem gidneyWriteBits_same (input : List Wire) (s : BasisState) :
    gidneyWriteBits input (wireValues input s) s = s := by
  induction input generalizing s with
  | nil => rfl
  | cons a as ih =>
    have hu : upd s a (s a) = s := by funext w; by_cases hw : w = a <;> simp [upd,hw]
    change gidneyWriteBits as (wireValues as s) (upd s a (s a)) = s
    rw [hu,ih]

private theorem gidneyIdeal_zero (input : List Wire) (constant : List Bool) (q : Wire) (s : BasisState)
    (hk : input.length = constant.length) (hz : constant.all (fun k => !k) = true) :
    gidneyAddIdealState input constant q s = s := by
  rw [gidneyAddIdealState,gidneyZeroSum _ _ _ (by simp [wireValues,hk]) hz,gidneyWriteBits_same]

private theorem gidneySingle_state (a q : Wire) (k : Bool) (s : BasisState) :
    run (if k then [.CX q a] else []) s = gidneyAddIdealState ([a] : List Wire) ([k] : List Bool) q s := by
  funext w
  cases k <;> by_cases hw : w = a <;>
    simp [gidneyAddIdealState,gidneyWriteBits,wireValues,cuccaroAddBits,cuccaroSum,
      cuccaroCarry,run,applyGate,upd,hw,Bool.xor_comm]

/-- Every measurement branch implements the same controlled modular-power-of-two addition.
Its coefficient is independent of the input. The ordinary source zero-constant shortcut
has no measurements; otherwise there are exactly `dirty.length` carry resets. -/
theorem controlledGidneyAddConst_branch_correct (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch) (hb : branch ∈ (controlledGidneyAddConst input dirty constant q c r t).run) :
    let m := if constant.all (fun k => !k) then 0 else dirty.length
    branch.history.length = m ∧ branch.kraus (Quantum.ket s) =
      Quantum.registerXResetMagnitude m • Quantum.ket (gidneyAddIdealState input constant q s) := by
  dsimp only
  by_cases hz : constant.all (fun k => !k) = true
  · simp only [controlledGidneyAddConst,if_pos hz] at hb
    have hb' := gidneyDoneBranch branch hb
    rw [if_pos hz,hb'.1,hb'.2,gidneyIdeal_zero input constant q s hk hz]
    simp [Quantum.registerXResetMagnitude]
  · rw [if_neg hz]
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
          subst as
          have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
          subst ks
          simp only [controlledGidneyAddConst,if_neg hz] at hb
          obtain ⟨last,hl,hhist,hsem⟩ := gidneyUnitaryBranch _ _ branch hb
          have hlast := gidneyDoneBranch last hl
          rw [hhist,hlast.1,hsem,hlast.2,Quantum.run_ket_agrees_classical _ s (by cases k <;> simp),
            gidneySingle_state]
          simp [Quantum.registerXResetMagnitude]
        | cons d ds =>
          simp only [controlledGidneyAddConst,if_neg hz] at hb
          exact gidneyCorrected_branch a d q c r t as ds k ks s (by simpa using hk)
            (by simpa using hd) hnd hc hr ht branch hb

private theorem gidneyCell_wellFormed (q c r t a d : Wire) (k : Bool)
    (hnd : [q,c,r,t,a,d].Nodup) : CircuitWellFormed (gidneyAddCarryCell q c r t a d k) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
  rcases hnd with ⟨⟨hqc,hqr,hqt,hqa,hqd⟩,⟨⟨hcr,hct,hca,hcd⟩,
    ⟨⟨hrt,hra,hrd⟩,⟨⟨hta,htd⟩,had,_⟩⟩⟩⟩
  cases k <;> simp_all [gidneyAddCarryCell,CircuitWellFormed,Gate.WellFormed,Ne.symm]

private theorem gidneyCleanup_wellFormed (input dirty : List Wire) (constant : List Bool)
    (q c : Wire) (hk : input.length = constant.length) (hd : dirty.length ≤ input.length)
    (hnd : (q :: c :: input ++ dirty).Nodup) :
    CircuitWellFormed (gidneyAddCleanup input dirty constant q c) := by
  have hshort : (q :: c :: input.take dirty.length ++ dirty).Nodup := by
    apply List.Nodup.sublist (l₂ := q :: c :: input ++ dirty) ?_ hnd
    exact ((List.Sublist.refl [q,c]).append (List.take_sublist _ _)).append (List.Sublist.refl dirty)
  have hm := controlledConstCarryXor_wellFormed (input.take dirty.length) dirty
    (constant.take dirty.length) q c (by simp [hk])
    (by simp [List.length_take,Nat.min_eq_left hd]) hshort
  have hf : CircuitWellFormed (gidneyFlipWord input) := by
    simp [gidneyFlipWord,CircuitWellFormed,Gate.WellFormed]
  simpa only [gidneyAddCleanup,CircuitWellFormed, List.forall_mem_append] using And.intro (And.intro hf hm) hf

private theorem gidneyTail_wellFormed (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hcallback : ∀ outcomes, CircuitWellFormed (callback outcomes))
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup) :
    (gidneyAddTail q c r t callback history input dirty constant).WellFormed := by
  induction input generalizing dirty constant c r history with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        have hqa : q ≠ a := by simp_all
        have hca : c ≠ a := by simp_all
        cases k <;> simp [gidneyAddTail,Quantum.AdaptiveCircuit.WellFormed,
          CircuitWellFormed,Gate.WellFormed,hqa,hca,hcallback]
        all_goals exact ⟨hcallback _,hcallback _⟩
      | cons d ds =>
        have hl := gidneyLayoutStep q c r t a d as ds hnd
        simp only [gidneyAddTail,Quantum.AdaptiveCircuit.WellFormed]
        exact ⟨gidneyCell_wellFormed q c r t a d k hl.1,
          ih ds ks r c (history ++ [false]) (by simpa using hk) (by simpa using hd) hl.2,
          ih ds ks r c (history ++ [true]) (by simpa using hk) (by simpa using hd) hl.2⟩

/-- All unitary blocks of the concrete adaptive adder use distinct gate roles. -/
theorem controlledGidneyAddConst_wellFormed (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (hk : input.length = constant.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup) :
    (controlledGidneyAddConst input dirty constant q c r t).WellFormed := by
  by_cases hz : constant.all (fun k => !k) = true
  · simp [controlledGidneyAddConst,hz,Quantum.AdaptiveCircuit.WellFormed]
  cases input with
  | nil => simp at hd
  | cons a as =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        have hqa : q ≠ a := by simp_all
        cases k <;> simp [controlledGidneyAddConst,hz,Quantum.AdaptiveCircuit.WellFormed,
          CircuitWellFormed,Gate.WellFormed,hqa]
      | cons d ds =>
        have hl := gidneyLayoutStep q c r t a d as ds hnd
        have hshort : (q :: c :: (a :: as) ++ d :: ds).Nodup := by
          apply List.Nodup.sublist (l₂ := [q,c,r,t] ++ (a :: as) ++ d :: ds) ?_ hnd
          exact (((by simp : [q,c].Sublist [q,c,r,t]).append (List.Sublist.refl _)).append (List.Sublist.refl _))
        have hw := gidneyCleanup_wellFormed (a :: as) (d :: ds) (k :: ks) q c hk (by simp_all) hshort
        simp only [controlledGidneyAddConst,if_neg hz,Quantum.AdaptiveCircuit.WellFormed]
        refine ⟨gidneyCell_wellFormed q c r t a d k hl.1,?_⟩
        apply gidneyTail_wellFormed as ds ks q r c t _ _ ?_ (by simpa using hk) (by simpa using hd) hl.2
        intro outcomes
        have hz := Quantum.registerZCorrection_wellFormed (d :: ds) outcomes
        simpa only [CircuitWellFormed,List.forall_mem_append] using And.intro (And.intro hz hw) hz

/-- The implemented instrument preserves total probability, including every outcome. -/
theorem controlledGidneyAddConst_preservesBornMass (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (hk : input.length = constant.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup)
    (ψ : Quantum.State) :
    Quantum.Instrument.bornMass (controlledGidneyAddConst input dirty constant q c r t).run ψ =
      Quantum.normSq ψ :=
  Quantum.AdaptiveCircuit.run_preservesBornMass _
    (controlledGidneyAddConst_wellFormed input dirty constant q c r t hk hd hnd) ψ

private theorem gidneyTail_measurementCount (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    (gidneyAddTail q c r t callback history input dirty constant).measurementCount = input.length := by
  induction input generalizing dirty constant c r history with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        simp [gidneyAddTail,Quantum.AdaptiveCircuit.measurementCount]
      | cons d ds =>
        simp only [gidneyAddTail,Quantum.AdaptiveCircuit.measurementCount]
        rw [ih ds ks r c _ (by simpa using hk) (by simpa using hd),
          ih ds ks r c _ (by simpa using hk) (by simpa using hd)]
        simp [Nat.add_comm]

/-- Reset count of the same circuit; the zero-constant shortcut costs no measurements. -/
theorem controlledGidneyAddConst_measurementCount (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    (controlledGidneyAddConst input dirty constant q c r t).measurementCount =
      if constant.all (fun k => !k) then 0 else dirty.length := by
  by_cases hz : constant.all (fun k => !k) = true
  · simp [controlledGidneyAddConst,hz,Quantum.AdaptiveCircuit.measurementCount]
  rw [if_neg hz]
  cases input with
  | nil => simp at hd
  | cons a as =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        simp [controlledGidneyAddConst,hz,Quantum.AdaptiveCircuit.measurementCount]
      | cons d ds =>
        simp only [controlledGidneyAddConst,if_neg hz,Quantum.AdaptiveCircuit.measurementCount]
        rw [gidneyTail_measurementCount as ds ks q r c t _ _ (by simpa using hk) (by simpa using hd)]
        simpa using Nat.succ.inj hd

private def gidneyForwardCost (cell top : Bool → Nat) : List Bool → Nat
  | [] => 0
  | [k] => top k
  | k :: ks => cell k + gidneyForwardCost cell top ks

private theorem gidneyTail_gateCount (cost : Gate → Nat) (cell top : Bool → Nat)
    (hcell : ∀ q c r t a d k, ((gidneyAddCarryCell q c r t a d k).map cost).sum = cell k)
    (htop : ∀ q c a k, (((if k then [.CX q a] else []) ++ [.CX c a]).map cost).sum = top k)
    (input dirty : List Wire) (constant : List Bool) (q c r t : Wire)
    (callback : List Bool → Circuit) (history : List Bool) (budget : Nat)
    (hcallback : ∀ outcomes, ((callback outcomes).map cost).sum = budget)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    gidneyGateCount cost (gidneyAddTail q c r t callback history input dirty constant) =
      gidneyForwardCost cell top constant + budget := by
  induction input generalizing dirty constant c r history with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        simp only [gidneyAddTail,gidneyGateCount,htop,hcallback,Nat.add_zero,max_self,gidneyForwardCost]
      | cons d ds =>
        have hne : ks ≠ [] := by intro he; simp_all
        simp only [gidneyAddTail,gidneyGateCount,hcell]
        rw [ih ds ks r c _ (by simpa using hk) (by simpa using hd),
          ih ds ks r c _ (by simpa using hk) (by simpa using hd),max_self]
        cases ks with
        | nil => contradiction
        | cons l ls => simp [gidneyForwardCost,Nat.add_assoc]

private theorem gidneyRoot_gateCount (cost : Gate → Nat) (cell top : Bool → Nat)
    (hX : ∀ w, cost (.X w) = 0) (hH : ∀ w, cost (.H w) = 0)
    (hcell : ∀ q c r t a d k, ((gidneyAddCarryCell q c r t a d k).map cost).sum = cell k)
    (htop : ∀ q c a k, (((if k then [.CX q a] else []) ++ [.CX c a]).map cost).sum = top k)
    (a d q c r t : Wire) (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (hz : (k :: constant).all (fun k => !k) ≠ true) :
    gidneyGateCount cost (controlledGidneyAddConst (a :: input) (d :: dirty) (k :: constant) q c r t) =
      cell k + gidneyForwardCost cell top constant +
        ((controlledConstCarryXor ((a :: input).take (d :: dirty).length) (d :: dirty)
          ((k :: constant).take (d :: dirty).length) q c).map cost).sum := by
  simp only [controlledGidneyAddConst,if_neg hz,gidneyGateCount,hcell]
  rw [gidneyTail_gateCount cost cell top hcell htop input dirty constant q r c t _ _
    (((gidneyAddCleanup (a :: input) (d :: dirty) (k :: constant) q c).map cost).sum)
    (by intro outcomes; simp [List.map_append,List.sum_append,gidneyZ_cost cost hX hH]) hk hd]
  have hflip (wires : List Wire) : ((gidneyFlipWord wires).map cost).sum = 0 := by
    induction wires with
    | nil => rfl
    | cons w ws ih => simpa [gidneyFlipWord,hX] using ih
  simp [gidneyAddCleanup,List.map_append,List.sum_append,hflip,Nat.add_assoc]


private theorem gidneyForward_toffoli (constant : List Bool) :
    gidneyForwardCost (fun _ => 1) (fun _ => 0) constant = constant.length - 1 := by
  induction constant with
  | nil => rfl
  | cons k ks ih =>
    cases ks with
    | nil => rfl
    | cons l ls => simp [gidneyForwardCost] at ih ⊢; omega

private theorem gidneyForward_zero (constant : List Bool) :
    gidneyForwardCost (fun _ => 0) (fun _ => 0) constant = 0 := by
  induction constant with
  | nil => rfl
  | cons k ks ih => cases ks with
    | nil => rfl
    | cons l ls => simpa only [gidneyForwardCost,Nat.zero_add] using ih

/-- Every valid constant adder uses no dyadic phase rotations, including the zero case. -/
theorem controlledGidneyAddConst_phase_zero (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    (primitiveResources (controlledGidneyAddConst (a :: input) (d :: dirty)
      (k :: constant) q c r t)).phase = 0 := by
  change gidneyGateCount primitivePhaseCost _ = 0
  by_cases hz : (k :: constant).all (fun b => !b) = true
  · simp [controlledGidneyAddConst,hz,gidneyGateCount]
  have hroot := gidneyRoot_gateCount primitivePhaseCost (fun _ => 0) (fun _ => 0)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell,primitivePhaseCost])
    (by intro q c a k; cases k <;> simp [primitivePhaseCost])
    a d q c r t input dirty k constant hk hd hz
  rw [hroot,gidneyForward_zero]
  simp only [Nat.zero_add]
  apply primitivePhaseCost_of_HPFree
  apply gidneyCarryXor_HPFree
  · simp [hk]
  · simp only [List.length_take,List.length_cons]
    omega

private theorem gidneyTail_cost_le (cost : Gate → Nat)
    (hcell : ∀ q c r t a d k, ((gidneyAddCarryCell q c r t a d k).map cost).sum = 0)
    (htop : ∀ (q c a : Wire) (k : Bool), (((if k then [Gate.CX q a] else []) ++ [Gate.CX c a]).map cost).sum = 0)
    (input dirty : List Wire) (constant : List Bool) (q c r t : Wire)
    (callback : List Bool → Circuit) (history : List Bool) (budget : Nat)
    (hcallback : ∀ outcomes, ((callback outcomes).map cost).sum ≤ budget)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    gidneyGateCount cost (gidneyAddTail q c r t callback history input dirty constant) ≤ budget := by
  induction input generalizing dirty constant c r history with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        simp only [gidneyAddTail,gidneyGateCount,htop,Nat.zero_add,Nat.add_zero]
        exact max_le (hcallback _) (hcallback _)
      | cons d ds =>
        simp only [gidneyAddTail,gidneyGateCount,hcell,Nat.zero_add]
        exact max_le (ih ds ks r c _ (by simpa using hk) (by simpa using hd))
          (ih ds ks r c _ (by simpa using hk) (by simpa using hd))

private theorem gidneyRoot_plain_cost_le (cost : Gate → Nat) (x h : Nat)
    (hX : ∀ w, cost (.X w) = x) (hH : ∀ w, cost (.H w) = h)
    (hcx : ∀ a b, cost (.CX a b) = 0) (hccx : ∀ a b c, cost (.CCX a b c) = 0)
    (a d q c r t : Wire) (k : Bool) (input dirty : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    gidneyGateCount cost (controlledGidneyAddConst (a :: input) (d :: dirty)
      (k :: constant) q c r t) ≤
      2 * (input.length + 1) * x + 2 * (dirty.length + 1) * (2*h+x) := by
  have hc : ∀ q c r t a d k, ((gidneyAddCarryCell q c r t a d k).map cost).sum = 0 := by
    intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell,hcx,hccx]
  have hz (ws : List Wire) (bs : List Bool) :
      ((Quantum.registerZCorrection ws bs).map cost).sum ≤ ws.length*(2*h+x) := by
    induction ws generalizing bs with
    | nil => simp [Quantum.registerZCorrection]
    | cons w ws ih =>
      cases bs with
      | nil => simp [Quantum.registerZCorrection]
      | cons b bs =>
        have hi := ih bs
        cases b <;> simp [Quantum.registerZCorrection,Quantum.pauliZ,List.map_append,
          List.sum_append,hX,hH,Nat.add_mul] at * <;> omega
  have hf (ws : List Wire) : ((gidneyFlipWord ws).map cost).sum = ws.length*x := by
    induction ws with
    | nil => simp [gidneyFlipWord]
    | cons w ws ih => simp [gidneyFlipWord] at ih ⊢; rw [hX,ih]; simp [Nat.add_mul,Nat.add_comm]
  by_cases he : (k :: constant).all (fun b => !b) = true
  · simp [controlledGidneyAddConst,he,gidneyGateCount]
  simp only [controlledGidneyAddConst,if_neg he,gidneyGateCount,hc,Nat.zero_add]
  apply gidneyTail_cost_le cost hc
    (by intro q c a k; cases k <;> simp [hcx]) input dirty constant q r c t
  · intro outcomes
    have hz' := hz (d :: dirty) outcomes
    simp only [List.map_append,List.sum_append,gidneyAddCleanup,hf,
      controlledConstCarryXor_cost_zero cost hcx hccx,List.length_cons] at *
    simp only [Nat.mul_assoc]
    omega
  · exact hk
  · exact hd

/-- Primitive X/H bounds count both copies of every measurement-dependent Z correction. -/
theorem controlledGidneyAddConst_XH_le (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    (primitiveResources (controlledGidneyAddConst (a :: input) (d :: dirty)
      (k :: constant) q c r t)).x ≤ 4*(input.length+1)-2 ∧
    (primitiveResources (controlledGidneyAddConst (a :: input) (d :: dirty)
      (k :: constant) q c r t)).h ≤ 4*input.length := by
  have hx := gidneyRoot_plain_cost_le primitiveXCost 1 0 (by intro w; rfl)
    (by intro w; rfl) (by intro a b; rfl) (by intro a b c; rfl)
    a d q c r t k input dirty constant hk hd
  have hh := gidneyRoot_plain_cost_le primitiveHCost 0 1 (by intro w; rfl)
    (by intro w; rfl) (by intro a b; rfl) (by intro a b c; rfl)
    a d q c r t k input dirty constant hk hd
  simp only [primitiveResources]
  constructor <;> omega

private theorem gidneyForward_cnot_le (constant : List Bool) (hn : constant ≠ []) :
    gidneyForwardCost (fun k => 5+3*k.toNat) (fun k => 1+k.toNat) constant ≤
      8*(constant.length-1)+2 := by
  induction constant with
  | nil => contradiction
  | cons k ks ih =>
    cases ks with
    | nil => cases k <;> simp [gidneyForwardCost]
    | cons l ls =>
      have hh := ih (by simp)
      cases k <;> simp [gidneyForwardCost] at * <;> omega

/-- A pattern-independent CNOT bound for the actual controlled adder. -/
theorem controlledGidneyAddConst_cnot_le (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length+1) :
    gidneyCnotCount (controlledGidneyAddConst (a :: input) (d :: dirty)
      (k :: constant) q c r t) ≤ 15*input.length := by
  by_cases hz : (k :: constant).all (fun b => !b) = true
  · simp [controlledGidneyAddConst,hz,gidneyCnotCount,gidneyGateCount]
  have hroot := gidneyRoot_gateCount (fun g => match g with | .CX _ _ => 1 | _ => 0)
    (fun k => 5+3*k.toNat) (fun k => 1+k.toNat)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell])
    (by intro q c a k; cases k <;> simp)
    a d q c r t input dirty k constant hk hd hz
  have hcleanup := (controlledConstCarryXor_counts a (input.take dirty.length) (d :: dirty) k
    (constant.take dirty.length) q c (by simp [hk])
    (by simp [Nat.min_eq_left (by omega : dirty.length ≤ input.length)])).2.2.1
  have hw (ks : List Bool) : constantBitWeight ks ≤ ks.length := by
    induction ks with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [constantBitWeight] at * <;> omega
  have hw' := hw (constant.take dirty.length)
  have hf := gidneyForward_cnot_le constant (by intro h; simp_all)
  apply hroot.le.trans
  simp only [List.length_cons,List.take_succ_cons]
  change 5+3*k.toNat + gidneyForwardCost (fun k => 5+3*k.toNat) (fun k => 1+k.toNat) constant +
    eeaCnotCount (controlledConstCarryXor (a :: input.take dirty.length) (d :: dirty)
      (k :: constant.take dirty.length) q c) ≤ _
  rw [hcleanup]
  simp only [List.length_take] at hw'
  cases k <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

/-- An odd, nonzero constant uses exactly `3n - 4` Toffolis at every width
`n ≥ 2`, independent of its other bits and all wire labels. -/
theorem controlledGidneyAddConst_toffoli_exact (a d q c r t : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    gidneyToffoliCount (controlledGidneyAddConst (a :: input) (d :: dirty) (true :: constant) q c r t) =
      3 * (input.length + 1) - 4 := by
  have hroot := gidneyRoot_gateCount (fun g => match g with | .CCX _ _ _ => 1 | _ => 0)
    (fun _ => 1) (fun _ => 0) (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell])
    (by intro q c a k; cases k <;> simp) a d q c r t input dirty true constant hk hd (by simp)
  have hki : (input.take dirty.length).length = (constant.take dirty.length).length := by simp [hk]
  have hdi : (a :: input.take dirty.length).length = (d :: dirty).length := by
    simp [Nat.min_eq_left (by omega : dirty.length ≤ input.length)]
  have hcleanup := (controlledConstCarryXor_counts a (input.take dirty.length) (d :: dirty) true
    (constant.take dirty.length) q c hki hdi).2.1
  apply hroot.trans
  simp only [List.length_cons,List.take_succ_cons]
  change 1 + gidneyForwardCost (fun _ => 1) (fun _ => 0) constant +
    eeaToffoliCount (controlledConstCarryXor (a :: input.take dirty.length) (d :: dirty)
      (true :: constant.take dirty.length) q c) = _
  rw [gidneyForward_toffoli,hcleanup]
  simp only [List.length_take]
  rw [Nat.min_eq_left (by omega : dirty.length ≤ input.length)]
  omega

private theorem gidneyRoot_cnot (a d q c r t : Wire) (input dirty : List Wire)
    (constant : List Bool) (hk : input.length = constant.length)
    (hd : input.length = dirty.length + 1) :
    gidneyCnotCount (controlledGidneyAddConst (a :: input) (d :: dirty) (true :: constant) q c r t) =
      8 + gidneyForwardCost (fun k => 5 + 3 * k.toNat) (fun k => 1 + k.toNat) constant +
        (7 * constantBitWeight (constant.take dirty.length) + 5) := by
  have hroot := gidneyRoot_gateCount (fun g => match g with | .CX _ _ => 1 | _ => 0)
    (fun k => 5 + 3 * k.toNat) (fun k => 1 + k.toNat)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell])
    (by intro q c a k; cases k <;> simp) a d q c r t input dirty true constant hk hd (by simp)
  have hki : (input.take dirty.length).length = (constant.take dirty.length).length := by simp [hk]
  have hdi : (a :: input.take dirty.length).length = (d :: dirty).length := by
    simp [Nat.min_eq_left (by omega : dirty.length ≤ input.length)]
  have hcleanup := (controlledConstCarryXor_counts a (input.take dirty.length) (d :: dirty) true
    (constant.take dirty.length) q c hki hdi).2.2.1
  apply hroot.trans
  simp only [List.length_cons, List.take_succ_cons]
  change 8 + gidneyForwardCost _ _ constant +
    eeaCnotCount (controlledConstCarryXor (a :: input.take dirty.length) (d :: dirty)
      (true :: constant.take dirty.length) q c) = _
  rw [hcleanup]
  rfl

/-- Reusing the same odd constant and register widths preserves the exact CX
count, independently of physical labels and the ordering of the borrowed wires. -/
theorem controlledGidneyAddConst_cnot_congr (a d q c r t a' d' q' c' r' t' : Wire)
    (input dirty input' dirty' : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (hk' : input'.length = constant.length) (hd' : input'.length = dirty'.length + 1) :
    gidneyCnotCount (controlledGidneyAddConst (a :: input) (d :: dirty) (true :: constant) q c r t) =
      gidneyCnotCount (controlledGidneyAddConst (a' :: input') (d' :: dirty') (true :: constant) q' c' r' t') := by
  rw [gidneyRoot_cnot a d q c r t input dirty constant hk hd,
    gidneyRoot_cnot a' d' q' c' r' t' input' dirty' constant hk' hd',
    show dirty.length = dirty'.length by omega]

private theorem gidneyForward_tCost (constant : List Bool) :
    gidneyForwardCost (fun _ => 7) (fun _ => 0) constant = 7 * (constant.length - 1) := by
  induction constant with
  | nil => rfl
  | cons k ks ih =>
    cases ks with
    | nil => rfl
    | cons l ls => simp [gidneyForwardCost] at ih ⊢; omega

/-- Exact T count of every nonzero constant, independent of its bit pattern. -/
theorem controlledGidneyAddConst_tCount_nonzero (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (hz : (k::constant).all (fun b => !b) ≠ true) :
    (controlledGidneyAddConst (a :: input) (d :: dirty) (k :: constant) q c r t).tCount =
      7 * (3 * (input.length + 1) - 4) := by
  have hroot := gidneyRoot_gateCount tCost (fun _ => 7) (fun _ => 0)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell,tCost])
    (by intro q c a k; cases k <;> simp [tCost]) a d q c r t input dirty k constant hk hd hz
  have hki : (input.take dirty.length).length = (constant.take dirty.length).length := by simp [hk]
  have hdi : (a :: input.take dirty.length).length = (d :: dirty).length := by
    simp [Nat.min_eq_left (by omega : dirty.length ≤ input.length)]
  have hcleanup := (controlledConstCarryXor_counts a (input.take dirty.length) (d :: dirty) k
    (constant.take dirty.length) q c hki hdi).2.2.2
  rw [← gidneyGateCount_tCount]
  apply hroot.trans
  simp only [List.length_cons,List.take_succ_cons]
  change 7 + gidneyForwardCost (fun _ => 7) (fun _ => 0) constant +
    tCount (controlledConstCarryXor (a :: input.take dirty.length) (d :: dirty)
      (k :: constant.take dirty.length) q c) = _
  rw [gidneyForward_tCost,hcleanup]
  simp only [List.length_take]
  rw [Nat.min_eq_left (by omega : dirty.length ≤ input.length)]
  omega



/-- The exact Toffoli count also holds for every nonzero even constant. -/
theorem controlledGidneyAddConst_toffoli_nonzero (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (hz : (k :: constant).all (fun b => !b) ≠ true) :
    gidneyToffoliCount (controlledGidneyAddConst (a :: input) (d :: dirty)
      (k :: constant) q c r t) = 3*(input.length+1)-4 := by
  have hp := controlledGidneyAddConst_phase_zero a d q c r t k input dirty constant hk hd
  have hc := primitiveResources_T_of_no_phase _ hp
  have ht := controlledGidneyAddConst_tCount_nonzero a d q c r t k input dirty constant hk hd hz
  simp only [primitiveResources] at hc
  omega

/-- Exact T count of the odd-constant circuit at every width at least two. -/
theorem controlledGidneyAddConst_tCount_exact (a d q c r t : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    (controlledGidneyAddConst (a :: input) (d :: dirty) (true :: constant) q c r t).tCount =
      7 * (3 * (input.length + 1) - 4) :=
  controlledGidneyAddConst_tCount_nonzero a d q c r t true input dirty constant hk hd (by simp)

/-- Little-endian modulus word used by the source inverse correction. -/
def secp256k1ModulusBits : List Bool :=
  (List.range 256).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The modulus correction has the same Toffoli/T count as the reduction constant,
but its denser bit pattern gives a different, explicitly counted CNOT budget. -/
theorem secp256k1ModulusAdd_counts (q c r t : Wire) :
    let ac := controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      secp256k1ModulusBits q c r t
    gidneyToffoliCount ac = 764 ∧ gidneyCnotCount ac = 3765 ∧
      ac.tCount = 5348 ∧ ac.measurementCount = 255 := by
  have hb : secp256k1ModulusBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)) := by decide
  have htf := controlledGidneyAddConst_toffoli_exact 4 260 q c r t
    (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) (by simp) (by simp)
  have ht := controlledGidneyAddConst_tCount_exact 4 260 q c r t
    (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) (by simp) (by simp)
  have hm := controlledGidneyAddConst_measurementCount (List.range' 4 256) (List.range' 260 255)
    secp256k1ModulusBits q c r t (by simp [secp256k1ModulusBits]) (by simp)
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · rw [hb]; exact htf
  · have hroot := gidneyRoot_gateCount (fun g => match g with | .CX _ _ => 1 | _ => 0)
      (fun k => 5 + 3 * k.toNat) (fun k => 1 + k.toNat)
      (by intro w; rfl) (by intro w; rfl)
      (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell])
      (by intro q c a k; cases k <;> simp)
      4 260 q c r t (List.range' 5 255) (List.range' 261 254) true
      ((List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)))
      (by simp) (by simp) (by simp)
    have hforward : gidneyForwardCost (fun k => 5 + 3 * k.toNat) (fun k => 1 + k.toNat)
      ((List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) = 2016 := by decide
    have hcleanup := (controlledConstCarryXor_counts 4 (List.range' 5 254) (List.range' 260 255) true
      ((List.range' 1 254).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) q c (by simp) (by simp)).2.2.1
    have hweight : constantBitWeight
      ((List.range' 1 254).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) = 248 := by decide
    rw [hb]
    apply hroot.trans
    rw [hforward]
    change 8 + 2016 + eeaCnotCount (controlledConstCarryXor (4 :: List.range' 5 254)
      (List.range' 260 255) (true :: (List.range' 1 254).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) q c) = 3765
    rw [hcleanup,hweight]
    rfl
  · rw [hb]; exact ht
  · simpa [hb] using hm

set_option maxRecDepth 100000 in
/-- Exact costs of the wrapper’s controlled increment stage. -/
theorem secp256k1Increment_counts (q c r t : Wire) :
    let ac := controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      ((List.range 256).map (Nat.testBit 1)) q c r t
    gidneyToffoliCount ac = 764 ∧ gidneyCnotCount ac = 1284 ∧
      ac.tCount = 5348 ∧ ac.measurementCount = 255 := by
  have hb : ((List.range 256).map (Nat.testBit 1)) = true ::
      (List.range' 1 255).map (Nat.testBit 1) := by decide
  have htf := controlledGidneyAddConst_toffoli_exact 4 260 q c r t
    (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit 1)) (by simp) (by simp)
  have ht := controlledGidneyAddConst_tCount_exact 4 260 q c r t
    (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit 1)) (by simp) (by simp)
  have hm := controlledGidneyAddConst_measurementCount (List.range' 4 256) (List.range' 260 255)
    ((List.range 256).map (Nat.testBit 1)) q c r t (by simp) (by simp)
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · rw [hb]; exact htf
  · have hroot := gidneyRoot_gateCount (fun g => match g with | .CX _ _ => 1 | _ => 0)
      (fun k => 5 + 3 * k.toNat) (fun k => 1 + k.toNat)
      (by intro w; rfl) (by intro w; rfl)
      (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell])
      (by intro q c a k; cases k <;> simp)
      4 260 q c r t (List.range' 5 255) (List.range' 261 254) true
      ((List.range' 1 255).map (Nat.testBit 1))
      (by simp) (by simp) (by simp)
    have hforward : gidneyForwardCost (fun k => 5 + 3 * k.toNat) (fun k => 1 + k.toNat)
      ((List.range' 1 255).map (Nat.testBit 1)) = 1271 := by decide
    have hcleanup := (controlledConstCarryXor_counts 4 (List.range' 5 254) (List.range' 260 255) true
      ((List.range' 1 254).map (Nat.testBit 1)) q c (by simp) (by simp)).2.2.1
    have hweight : constantBitWeight
      ((List.range' 1 254).map (Nat.testBit 1)) = 0 := by decide
    rw [hb]
    apply hroot.trans
    rw [hforward]
    change 8 + 1271 + eeaCnotCount (controlledConstCarryXor (4 :: List.range' 5 254)
      (List.range' 260 255) (true :: (List.range' 1 254).map (Nat.testBit 1)) q c) = 1284
    rw [hcleanup,hweight]
    rfl
  · rw [hb]; exact ht
  · simpa [hb] using hm

/-- Production controlled constant adder, with 256 data bits, 255 arbitrary borrowed
bits, and three initially clean carry/ancilla bits. -/
def secp256k1GidneyAdd : Quantum.AdaptiveCircuit :=
  controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
    secp256k1ReductionConstantBits 0 1 2 3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyProduction_cleanup_counts (q c : Wire) :
    let gates := controlledConstCarryXor (List.range' 4 255) (List.range' 260 255)
      ((List.range 255).map (Nat.testBit (2 ^ 32 + 977))) q c
    eeaToffoliCount gates = 509 ∧ eeaCnotCount gates = 47 ∧ tCount gates = 3563 := by
  have h := controlledConstCarryXor_counts 4 (List.range' 5 254) (List.range' 260 255) true
    ((List.range' 1 254).map (Nat.testBit (2 ^ 32 + 977))) q c (by simp) (by simp)
  have hw : constantBitWeight ((List.range' 1 254).map (Nat.testBit (2 ^ 32 + 977))) = 6 := by decide
  dsimp only
  change eeaToffoliCount (controlledConstCarryXor (4 :: List.range' 5 254) _
    (true :: (List.range' 1 254).map (Nat.testBit (2 ^ 32 + 977))) q c) = 509 ∧ _
  simpa [hw] using And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2)


private theorem gidneyCell_wires (q c r t a d w : Wire) (k : Bool) :
    w ∈ circuitWires (gidneyAddCarryCell q c r t a d k) → w ∈ [q,c,r,t,a,d] := by
  cases k <;> simp [gidneyAddCarryCell,circuitWires,gateWires] <;> tauto

private theorem gidneyTail_usesOnly (allowed input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hroles : ∀ w ∈ [q,c,r,t] ++ input ++ dirty, w ∈ allowed)
    (hcallback : ∀ outcomes w, w ∈ circuitWires (callback outcomes) → w ∈ allowed) :
    ∀ w ∈ (gidneyAddTail q c r t callback history input dirty constant).wires, w ∈ allowed := by
  induction input generalizing dirty constant c r history with
  | nil => simp [gidneyAddTail,Quantum.AdaptiveCircuit.wires]
  | cons a as ih =>
    cases dirty with
    | nil =>
      cases as with
      | cons b bs => simp [gidneyAddTail,Quantum.AdaptiveCircuit.wires]
      | nil =>
        cases constant with
        | nil => simp [gidneyAddTail,Quantum.AdaptiveCircuit.wires]
        | cons k ks =>
          cases ks with
          | cons l ls => simp [gidneyAddTail,Quantum.AdaptiveCircuit.wires]
          | nil =>
            intro w hw
            have hq := hroles q (by simp)
            have hc := hroles c (by simp)
            have ha := hroles a (by simp)
            cases k <;> simp only [gidneyAddTail,Quantum.AdaptiveCircuit.wires,
              Bool.false_eq_true,↓reduceIte,circuitWires,List.flatMap_append,List.flatMap_cons,
              List.flatMap_nil,gateWires,List.mem_append,List.mem_cons,List.not_mem_nil] at hw
            all_goals
              have hf := hcallback (history ++ [false]) w
              have ht := hcallback (history ++ [true]) w
              simp only [circuitWires] at hf ht
              aesop
    | cons d ds =>
      cases constant with
      | nil => simp [gidneyAddTail,Quantum.AdaptiveCircuit.wires]
      | cons k ks =>
        have ht : ∀ w ∈ [q,r,c,t] ++ as ++ ds, w ∈ allowed := by
          intro w hw; apply hroles w
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢; tauto
        intro w hw
        simp only [gidneyAddTail,Quantum.AdaptiveCircuit.wires,List.mem_append,List.mem_cons] at hw
        rcases hw with h | h | h | h
        · apply hroles w
          have hm := gidneyCell_wires q c r t a d w k h
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hm ⊢; tauto
        · subst w; exact hroles c (by simp)
        · exact ih ds ks r c _ ht w h
        · exact ih ds ks r c _ ht w h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyProduction_toffoli (q c r t : Wire) : gidneyToffoliCount (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits q c r t) = 764 := by
  have h := gidneyRoot_gateCount (fun g => match g with | .CCX _ _ _ => 1 | _ => 0) (fun _ => 1) (fun _ => 0)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell,tCost])
    (by intro q c a k; cases k <;> simp [tCost])
    4 260 q c r t (List.range' 5 255) (List.range' 261 254) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)))
    (by simp) (by simp) (by simp)
  have hb : gidneyForwardCost (fun _ => 1) (fun _ => 0)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) = 254 := by decide
  have hc := (gidneyProduction_cleanup_counts q c).1
  unfold gidneyToffoliCount
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 255 = 260 :: List.range' 261 254 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  apply h.trans
  rw [hb]
  have ha : (4 :: List.range' 5 255).take (260 :: List.range' 261 254).length = List.range' 4 255 := by decide
  have hk : (true :: (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))).take
      (260 :: List.range' 261 254).length = (List.range 255).map (Nat.testBit (2 ^ 32 + 977)) := by decide
  rw [ha,hk]
  have hd : 260 :: List.range' 261 254 = List.range' 260 255 := rfl
  rw [hd]
  change 1 + 254 + eeaToffoliCount _ = 764
  rw [hc]


private theorem gidneyTail_covers (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length + 1) :
    ∀ w ∈ input ++ dirty, w ∈ (gidneyAddTail q c r t callback history input dirty constant).wires := by
  induction input generalizing dirty constant c r history with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        intro w hw
        have he : w = a := by simpa using hw
        subst w
        cases k <;> simp [gidneyAddTail,Quantum.AdaptiveCircuit.wires,circuitWires,gateWires]
      | cons d ds =>
        intro w hw
        have ht := ih ds ks r c (history ++ [false]) (by simpa using hk) (by simpa using hd)
        have hcell : w ∈ [a,d] → w ∈ circuitWires (gidneyAddCarryCell q c r t a d k) := by
          intro h; cases k <;> simp_all [gidneyAddCarryCell,circuitWires,gateWires] <;> tauto
        simp only [gidneyAddTail,Quantum.AdaptiveCircuit.wires,List.mem_append,List.mem_cons]
        by_cases h : w ∈ [a,d]
        · exact Or.inl (hcell h)
        · apply Or.inr; apply Or.inr; apply Or.inl
          apply ht w
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hw h ⊢; tauto

private theorem gidneyCleanup_usesOnly (input dirty : List Wire) (constant : List Bool) (q c : Wire) :
    ∀ w ∈ circuitWires (gidneyAddCleanup input dirty constant q c), w ∈ q :: c :: input ++ dirty := by
  have hm := controlledConstCarryXor_usesOnly (input.take dirty.length) dirty
    (constant.take dirty.length) q c
  intro w hw
  simp only [gidneyAddCleanup,circuitWires,List.flatMap_append,List.mem_append] at hw
  have hf : w ∈ (gidneyFlipWord input).flatMap gateWires → w ∈ input := by
    simp [gidneyFlipWord,gateWires]
  rcases hw with (h | h) | h
  · simp [hf h]
  · obtain ⟨g,hg,hwg⟩ := List.mem_flatMap.mp h
    have hh := hm g hg w hwg
    simp only [List.mem_cons,List.mem_append] at hh ⊢
    have htake : w ∈ input.take dirty.length → w ∈ input := List.mem_of_mem_take
    tauto
  · simp [hf h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyProduction_cnot (q c r t : Wire) : gidneyCnotCount (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits q c r t) = 1344 := by
  have h := gidneyRoot_gateCount (fun g => match g with | .CX _ _ => 1 | _ => 0) (fun k => 5 + 3 * k.toNat) (fun k => 1 + k.toNat)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell,tCost])
    (by intro q c a k; cases k <;> simp [tCost])
    4 260 q c r t (List.range' 5 255) (List.range' 261 254) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)))
    (by simp) (by simp) (by simp)
  have hb : gidneyForwardCost (fun k => 5 + 3 * k.toNat) (fun k => 1 + k.toNat)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) = 1289 := by decide
  have hc := (gidneyProduction_cleanup_counts q c).2.1
  unfold gidneyCnotCount
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 255 = 260 :: List.range' 261 254 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  apply h.trans
  rw [hb]
  have ha : (4 :: List.range' 5 255).take (260 :: List.range' 261 254).length = List.range' 4 255 := by decide
  have hk : (true :: (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))).take
      (260 :: List.range' 261 254).length = (List.range 255).map (Nat.testBit (2 ^ 32 + 977)) := by decide
  rw [ha,hk]
  have hd : 260 :: List.range' 261 254 = List.range' 260 255 := rfl
  rw [hd]
  change 8 + 1289 + eeaCnotCount _ = 1344
  rw [hc]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyProduction_t (q c r t : Wire) : (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits q c r t).tCount = 5348 := by
  have h := gidneyRoot_gateCount tCost (fun _ => 7) (fun _ => 0)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell,tCost])
    (by intro q c a k; cases k <;> simp [tCost])
    4 260 q c r t (List.range' 5 255) (List.range' 261 254) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)))
    (by simp) (by simp) (by simp)
  have hb : gidneyForwardCost (fun _ => 7) (fun _ => 0)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) = 1778 := by decide
  have hc := (gidneyProduction_cleanup_counts q c).2.2
  rw [← gidneyGateCount_tCount]
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 255 = 260 :: List.range' 261 254 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  apply h.trans
  rw [hb]
  have ha : (4 :: List.range' 5 255).take (260 :: List.range' 261 254).length = List.range' 4 255 := by decide
  have hk : (true :: (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))).take
      (260 :: List.range' 261 254).length = (List.range 255).map (Nat.testBit (2 ^ 32 + 977)) := by decide
  rw [ha,hk]
  have hd : 260 :: List.range' 261 254 = List.range' 260 255 := rfl
  rw [hd]
  change 7 + 1778 + tCount _ = 5348
  rw [hc]

/-- The production constant adder's costs are independent of its scalar wire labels. -/
theorem secp256k1GidneyAdd_counts (q c r t : Wire) :
    let g := controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      secp256k1ReductionConstantBits q c r t
    gidneyToffoliCount g = 764 ∧ gidneyCnotCount g = 1344 ∧ g.tCount = 5348 ∧ g.measurementCount = 255 := by
  refine ⟨gidneyProduction_toffoli q c r t,gidneyProduction_cnot q c r t,gidneyProduction_t q c r t,?_⟩
  have hz : secp256k1ReductionConstantBits.all (fun k => !k) = false := by decide
  simpa [hz] using controlledGidneyAddConst_measurementCount (List.range' 4 256) (List.range' 260 255)
    secp256k1ReductionConstantBits q c r t (by simp [secp256k1ReductionConstantBits]) (by simp)

theorem controlledGidneyAddConst_wires (a d q c r t : Wire) (input dirty : List Wire)
    (constant : List Bool) (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (w : Wire) :
    w ∈ (controlledGidneyAddConst (a :: input) (d :: dirty) (true :: constant) q c r t).wires ↔
      w ∈ [q,c,r,t] ++ (a :: input) ++ d :: dirty := by
  let allowed := [q,c,r,t] ++ (a :: input) ++ d :: dirty
  let callback := fun outcomes => Quantum.registerZCorrection (d :: dirty) outcomes ++
    gidneyAddCleanup (a :: input) (d :: dirty) (true :: constant) q c ++
    Quantum.registerZCorrection (d :: dirty) outcomes
  have hcallback : ∀ outcomes x, x ∈ circuitWires (callback outcomes) → x ∈ allowed := by
    intro outcomes x hx
    have hz := gidneyZ_usesOnly (d :: dirty) outcomes x
    have hc := gidneyCleanup_usesOnly (a :: input) (d :: dirty) (true :: constant) q c x
    simp only [callback,circuitWires,List.flatMap_append,List.mem_append] at hx
    change (x ∈ circuitWires (Quantum.registerZCorrection (d :: dirty) outcomes) ∨
      x ∈ circuitWires (gidneyAddCleanup (a :: input) (d :: dirty) (true :: constant) q c)) ∨
      x ∈ circuitWires (Quantum.registerZCorrection (d :: dirty) outcomes) at hx
    have : x ∈ (d :: dirty) ∨ x ∈ q :: c :: (a :: input) ++ d :: dirty := by tauto
    simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at this ⊢; tauto
  have hroles : ∀ x ∈ [q,r,c,t] ++ input ++ dirty, x ∈ allowed := by
    intro x hx; simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at hx ⊢; tauto
  have ht := gidneyTail_usesOnly allowed input dirty constant q r c t callback (List.nil : List Bool) hroles hcallback w
  have hl := gidneyTail_covers input dirty constant q r c t callback (List.nil : List Bool) hk hd w
  have hcell : w ∈ circuitWires (gidneyAddCarryCell q c r t a d true) ↔ w ∈ [q,c,r,t,a,d] := by
    simp [gidneyAddCarryCell,circuitWires,gateWires,or_assoc,or_left_comm,or_comm]
  simp only [controlledGidneyAddConst,List.all_cons,Bool.not_true,Bool.false_and,Bool.false_eq_true,
    ↓reduceIte,Quantum.AdaptiveCircuit.wires]
  rw [List.mem_append]
  change (w ∈ circuitWires (gidneyAddCarryCell q c r t a d true) ∨
    w ∈ (gidneyAddTail q r c t callback (List.nil : List Bool) input dirty constant).wires) ↔ w ∈ allowed
  rw [hcell]
  constructor
  · intro h
    rcases h with h | h
    · simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · exact ht h
  · intro h
    by_cases hcell : w ∈ [q,c,r,t,a,d]
    · exact Or.inl hcell
    · apply Or.inr; apply hl
      simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at h hcell ⊢; tauto

/-- Every constant pattern uses only the supplied registers and helper wires. -/
theorem controlledGidneyAddConst_wires_subset (a d q c r t : Wire) (input dirty : List Wire)
    (k : Bool) (constant : List Bool) :
    (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t).wires ⊆
      [q,c,r,t]++(a::input)++d::dirty := by
  intro w hw
  by_cases hz : (k::constant).all (fun b => !b)=true
  · simp [controlledGidneyAddConst,hz,Quantum.AdaptiveCircuit.wires] at hw
  · let allowed := [q,c,r,t] ++ (a :: input) ++ d :: dirty
    let callback := fun outcomes => Quantum.registerZCorrection (d :: dirty) outcomes ++
      gidneyAddCleanup (a :: input) (d :: dirty) (k :: constant) q c ++
      Quantum.registerZCorrection (d :: dirty) outcomes
    have hcallback : ∀ outcomes x, x ∈ circuitWires (callback outcomes) → x ∈ allowed := by
      intro outcomes x hx
      have hz := gidneyZ_usesOnly (d :: dirty) outcomes x
      have hc := gidneyCleanup_usesOnly (a :: input) (d :: dirty) (k :: constant) q c x
      simp only [callback,circuitWires,List.flatMap_append,List.mem_append] at hx
      change (x ∈ circuitWires (Quantum.registerZCorrection (d :: dirty) outcomes) ∨
        x ∈ circuitWires (gidneyAddCleanup (a :: input) (d :: dirty) (k :: constant) q c)) ∨
        x ∈ circuitWires (Quantum.registerZCorrection (d :: dirty) outcomes) at hx
      have : x ∈ (d :: dirty) ∨ x ∈ q :: c :: (a :: input) ++ d :: dirty := by tauto
      simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at this ⊢; tauto
    have hroles : ∀ x ∈ [q,r,c,t] ++ input ++ dirty, x ∈ allowed := by
      intro x hx; simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at hx ⊢; tauto
    have ht := gidneyTail_usesOnly allowed input dirty constant q r c t callback (List.nil : List Bool) hroles hcallback w
    simp only [controlledGidneyAddConst,if_neg hz,Quantum.AdaptiveCircuit.wires,List.mem_append] at hw
    change w ∈ circuitWires (gidneyAddCarryCell q c r t a d k) ∨
      w ∈ (gidneyAddTail q r c t callback (List.nil : List Bool) input dirty constant).wires at hw
    rcases hw with hw | hw
    · have hh := gidneyCell_wires q c r t a d w k hw
      simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at hh ⊢
      tauto
    · exact ht hw

/-- Exact physical support; measurements reuse labels without subtracting live wires. -/
theorem controlledGidneyAddConst_qubitCount (a d q c r t : Wire) (input dirty : List Wire)
    (constant : List Bool) (hk : input.length = constant.length) (hd : input.length = dirty.length + 1)
    (hnd : ([q,c,r,t] ++ (a :: input) ++ d :: dirty).Nodup) :
    (controlledGidneyAddConst (a :: input) (d :: dirty) (true :: constant) q c r t).qubitCount =
      2 * (input.length + 1) + 3 := by
  have heq : (controlledGidneyAddConst (a :: input) (d :: dirty) (true :: constant) q c r t).wires.dedup.toFinset =
      ([q,c,r,t] ++ (a :: input) ++ d :: dirty).toFinset := by
    ext w; simpa [or_assoc,or_left_comm,or_comm] using controlledGidneyAddConst_wires a d q c r t input dirty constant hk hd w
  have hc := congrArg Finset.card heq
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_card_of_nodup hnd] at hc
  simp only [List.length_append,List.length_cons,List.length_nil] at hc
  unfold Quantum.AdaptiveCircuit.qubitCount
  omega


/-- The ideal has the ordinary numeric modular-addition meaning and preserves every
wire outside the input word, including the control and all borrowed and clean work. -/
theorem gidneyAddIdealState_correct (input : List Wire) (constant : List Bool) (q : Wire)
    (s : BasisState) (hk : input.length = constant.length) (hnd : input.Nodup) :
    boolWordToNat (wireValues input (gidneyAddIdealState input constant q s)) =
      (boolWordToNat (wireValues input s) + if s q then boolWordToNat constant else 0) % 2 ^ input.length ∧
      (∀ w, w ∉ input → gidneyAddIdealState input constant q s w = s w) := by
  have hlen : (wireValues input s).length = (constant.map (fun k => s q && k)).length := by simp [wireValues,hk]
  have hvalues := gidneyWriteBits_values input
    (cuccaroAddBits false (wireValues input s) (constant.map (fun k => s q && k))) s hnd
    (by rw [cuccaroAddBits_length _ _ _ hlen]; simp [wireValues])
  have hv := carryAddBits_value false (wireValues input s) (constant.map (fun k => s q && k)) hlen
  have hlow := boolWordToNat_lt_pow_two (cuccaroAddBits false (wireValues input s) (constant.map (fun k => s q && k)))
  rw [cuccaroAddBits_length _ _ _ hlen] at hlow
  have hconst : boolWordToNat (constant.map (fun k => s q && k)) = if s q then boolWordToNat constant else 0 := by
    cases hq : s q with
    | true => simp
    | false =>
      simp only [Bool.false_and,↓reduceIte]
      clear hk hlen hvalues hv hlow
      induction constant with
      | nil => rfl
      | cons k ks ih => simpa only [List.map_cons,boolWordToNat,Bool.toNat_false,Nat.zero_add] using congrArg (2 * ·) ih
  constructor
  · change boolWordToNat (wireValues input (gidneyWriteBits input _ s)) = _
    rw [hvalues]
    have hm := congrArg (fun n => n % 2 ^ input.length) hv
    simpa [hconst,wireValues,Nat.add_mod,Nat.mod_eq_of_lt (by simpa [wireValues] using hlow)] using hm
  · exact fun w hw => gidneyWriteBits_frame input _ s w hw


/-- Complementary controlled constants cancel on the complete state. This is the
arithmetic inverse used by the measured modular subtraction circuit. -/
theorem gidneyAddIdealState_complement (input : List Wire) (forward inverse : List Bool)
    (q : Wire) (s : BasisState) (hf : input.length = forward.length)
    (hi : input.length = inverse.length) (hnd : input.Nodup) (hq : q ∉ input)
    (hsum : boolWordToNat forward + boolWordToNat inverse = 2 ^ input.length) :
    gidneyAddIdealState input inverse q (gidneyAddIdealState input forward q s) = s := by
  have hfirst := gidneyAddIdealState_correct input forward q s hf hnd
  have hsecond := gidneyAddIdealState_correct input inverse q
    (gidneyAddIdealState input forward q s) hi hnd
  have hvalue : boolWordToNat (wireValues input
      (gidneyAddIdealState input inverse q (gidneyAddIdealState input forward q s))) =
      boolWordToNat (wireValues input s) := by
    rw [hsecond.1,hfirst.1,hfirst.2 q hq]
    have hsmall : boolWordToNat (wireValues input s) < 2 ^ input.length := by
      simpa [wireValues] using boolWordToNat_lt_pow_two (wireValues input s)
    cases hs : s q <;> simp only [hs,Bool.false_eq_true,↓reduceIte]
    · simp [Nat.mod_eq_of_lt hsmall]
    · rw [Nat.mod_add_mod,Nat.add_assoc,hsum,Nat.add_mod_right,Nat.mod_eq_of_lt hsmall]
  have hwords := boolWordToNat_injective_of_length
    (by simp [wireValues]) hvalue
  funext w
  by_cases hw : w ∈ input
  · exact List.map_inj_left.mp hwords w hw
  · exact (hsecond.2 w hw).trans (hfirst.2 w hw)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyProduction_layout :
    ([0,1,2,3] ++ List.range' 4 256 ++ List.range' 260 255).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

set_option maxRecDepth 100000 in
private theorem gidneyProduction_qubits : secp256k1GidneyAdd.qubitCount = 515 := by
  unfold secp256k1GidneyAdd
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 255 = 260 :: List.range' 261 254 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  exact controlledGidneyAddConst_qubitCount 4 260 0 1 2 3 _ _ _
    (by simp) (by simp) gidneyProduction_layout

/-- Same-circuit 256-bit certificate. Every branch adds control*(2^32+977) modulo 2^256;
all other wires, including arbitrary borrowed data, are restored. Probability sums to one.
The concrete circuit uses 764 CCX, 1,344 CX, 5,348 T, 255 measurement/resets and 515 wires. -/
theorem secp256k1GidneyAdd_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) :
    let after := gidneyAddIdealState (List.range' 4 256) secp256k1ReductionConstantBits 0 s
    boolWordToNat (wireValues (List.range' 4 256) after) =
      (boolWordToNat (wireValues (List.range' 4 256) s) + if s 0 then 2 ^ 32 + 977 else 0) % 2 ^ 256 ∧
    (∀ w, w ∉ List.range' 4 256 → after w = s w) ∧
    (∀ branch ∈ secp256k1GidneyAdd.run, branch.history.length = 255 ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude 255 • Quantum.ket after) ∧
    Quantum.Instrument.bornMass secp256k1GidneyAdd.run (Quantum.ket s) = 1 ∧
    secp256k1GidneyAdd.WellFormed ∧
    gidneyToffoliCount secp256k1GidneyAdd = 764 ∧
    gidneyCnotCount secp256k1GidneyAdd = 1344 ∧
    secp256k1GidneyAdd.tCount = 5348 ∧
    secp256k1GidneyAdd.measurementCount = 255 ∧ secp256k1GidneyAdd.qubitCount = 515 := by
  have hk : (List.range' 4 256).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hd : (List.range' 4 256).length = (List.range' 260 255).length + 1 := by simp
  have hz : secp256k1ReductionConstantBits.all (fun k => !k) = false := by decide
  have hw := controlledGidneyAddConst_wellFormed _ _ _ 0 1 2 3 hk hd gidneyProduction_layout
  have ha := gidneyAddIdealState_correct (List.range' 4 256) secp256k1ReductionConstantBits 0 s hk (List.nodup_range')
  dsimp only
  refine ⟨?_,ha.2,?_,?_,hw,gidneyProduction_toffoli 0 1 2 3,gidneyProduction_cnot 0 1 2 3,gidneyProduction_t 0 1 2 3,?_,gidneyProduction_qubits⟩
  · simpa [secp256k1ReductionConstant_value] using ha.1
  · intro branch hb
    have h := controlledGidneyAddConst_branch_correct _ _ _ 0 1 2 3 s hk hd gidneyProduction_layout hc hr ht branch hb
    simpa [hz] using h
  · exact Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket s)
  · simpa [hz] using controlledGidneyAddConst_measurementCount _ _ _ 0 1 2 3 hk hd

private theorem gidneyAddCell_controlSafe (q c r t a d : Wire) (k : Bool)
    (h : q ∉ [c,r,t,a,d]) :
    ∀ g ∈ gidneyAddCarryCell q c r t a d k, constantControlSafe q g := by
  cases k <;> simp_all [gidneyAddCarryCell,constantControlSafe,eq_comm]
private theorem gidneyAddTail_controlSafe (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hroles : q ∉ [c,r,t]++input++dirty)
    (hcallback : ∀ outcomes g, g ∈ callback outcomes → constantControlSafe q g) :
    constantControlProgramSafe q (gidneyAddTail q c r t callback history input dirty constant) := by
  induction input generalizing dirty constant c r history with
  | nil => cases dirty <;> cases constant <;> simp [gidneyAddTail,constantControlProgramSafe]
  | cons a input ih =>
      cases dirty with
      | nil =>
        cases input <;> cases constant with
        | nil => simp [gidneyAddTail,constantControlProgramSafe]
        | cons k ks =>
          cases ks <;> cases k <;> simp_all [gidneyAddTail,constantControlProgramSafe,constantControlSafe,eq_comm]
          all_goals exact ⟨hcallback _,hcallback _⟩
      | cons d dirty =>
        cases constant with
        | nil => simp [gidneyAddTail,constantControlProgramSafe]
        | cons k constant =>
          have hc : c≠q := by simp_all [eq_comm]
          have hcell : q ∉ [c,r,t,a,d] := by simp_all
          have htail : q ∉ [r,c,t]++input++dirty := by simp_all
          cases input <;> simp only [gidneyAddTail,constantControlProgramSafe] <;>
            exact ⟨gidneyAddCell_controlSafe q c r t a d k hcell,
            hc,by have hh := ih dirty constant r c (history++[false]) htail; simp only [gidneyAddTail,constantControlProgramSafe] at hh; exact hh,
            by have hh := ih dirty constant r c (history++[true]) htail; simp only [gidneyAddTail,constantControlProgramSafe] at hh; exact hh⟩
private theorem addZ_controlSafe (q : Wire) (dirty : List Wire) (outcomes : List Bool)
    (h : q ∉ dirty) : ∀ g ∈ Quantum.registerZCorrection dirty outcomes, constantControlSafe q g := by
  intro g hg
  have hn : q ∉ gateWires g := by
    intro hq
    exact h (gidneyZ_usesOnly dirty outcomes q (List.mem_flatMap.mpr ⟨g,hg,hq⟩))
  cases g <;> simp_all [constantControlSafe,gateWires,eq_comm]
private theorem addCleanup_controlSafe (input dirty : List Wire) (constant : List Bool)
    (q c : Wire) (h : q ∉ c::input++dirty) :
    ∀ g ∈ gidneyAddCleanup input dirty constant q c, constantControlSafe q g := by
  have hx : ∀ g ∈ gidneyFlipWord input, constantControlSafe q g := by
    intro g hg
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
    change w≠q
    intro he
    subst w
    simp_all
  have hc : q ∉ c::input.take dirty.length++dirty := by
    simp only [List.mem_cons,List.mem_append,not_or] at h ⊢
    exact ⟨⟨h.1.1,fun hh => h.1.2 (List.mem_of_mem_take hh)⟩,h.2⟩
  simp only [gidneyAddCleanup,List.forall_mem_append]
  exact ⟨⟨hx,controlledConstCarryXor_controlSafe _ _ _ q c hc⟩,hx⟩
/-- The adder's external control is read only, including measured phase cleanup. -/
theorem controlledGidneyAddConst_controlSafe (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (h : q ∉ [c,r,t]++input++dirty) :
    constantControlProgramSafe q (controlledGidneyAddConst input dirty constant q c r t) := by
  unfold controlledGidneyAddConst
  split
  · trivial
  · cases input with
    | nil => simp [constantControlProgramSafe]
    | cons a input =>
      cases dirty with
      | nil =>
        cases input <;> cases constant with
        | nil => simp [constantControlProgramSafe]
        | cons k ks =>
          cases ks <;> cases k <;> simp only [constantControlProgramSafe,constantControlSafe,List.forall_mem_cons,List.forall_mem_nil, and_true, Bool.false_eq_true, if_false, if_true]
          all_goals simp_all only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or,ne_eq,eq_comm]
          all_goals simp
      | cons d dirty =>
        cases constant with
        | nil => trivial
        | cons k constant =>
          have hcell : q ∉ [c,r,t,a,d] := by simp_all
          have ht : q ∉ [r,c,t]++input++dirty := by simp_all
          have hd : q ∉ d::dirty := by simp_all
          have hx : q ∉ c::(a::input)++d::dirty := by simp_all
          cases input <;> simp only [constantControlProgramSafe] <;>
            refine ⟨gidneyAddCell_controlSafe q c r t a d k hcell,
            gidneyAddTail_controlSafe _ dirty constant q r c t _ _ ht ?_⟩
          all_goals intro outcomes
          all_goals simp only [List.forall_mem_append]
          all_goals exact ⟨⟨addZ_controlSafe q _ outcomes hd,addCleanup_controlSafe _ _ _ q c hx⟩,
            addZ_controlSafe q _ outcomes hd⟩

/-- Uncontrolled fixed-width constant sum, with no virtual control in the state map. -/
def gidneyUncontrolledAddIdealState (input : List Wire) (constant : List Bool) (s : BasisState) : BasisState :=
  gidneyWriteBits input (cuccaroAddBits false (wireValues input s) constant) s
private theorem gidneyWriteBits_control (input : List Wire) (bits : List Bool) (s : BasisState)
    (q : Wire) (b : Bool) (hq : q ∉ input) :
    gidneyWriteBits input bits (upd s q b)=upd (gidneyWriteBits input bits s) q b := by
  induction input generalizing bits s with
  | nil => rfl
  | cons a input ih =>
    cases bits with
    | nil => rfl
    | cons bit bits =>
      have hqa : q≠a := by intro he; exact hq (by simp [he])
      have hqt : q ∉ input := fun hh => hq (List.mem_cons_of_mem a hh)
      have hcomm : upd (upd s q b) a bit=upd (upd s a bit) q b := by
        funext w
        by_cases hwq : w=q <;> by_cases hwa : w=a <;> simp_all [upd]
      simp only [gidneyWriteBits,hcomm,ih bits (upd s a bit) hqt]
theorem gidneyAddIdealState_enabled (input : List Wire) (constant : List Bool) (s : BasisState)
    (q : Wire) (hq : q ∉ input) :
    gidneyAddIdealState input constant q (upd s q true)=upd (gidneyUncontrolledAddIdealState input constant s) q true := by
  have hi : wireValues input (upd s q true)=wireValues input s := by
    apply List.map_congr_left
    intro w hw
    have hn : w≠q := by intro he; exact hq (he ▸ hw)
    simp [upd,hn]
  have hmap : List.map (fun k : Bool => k) constant=constant := by induction constant <;> simp_all
  simp only [gidneyAddIdealState,upd_same,Bool.true_and,hmap,hi,
    gidneyWriteBits_control input _ s q true hq,gidneyUncontrolledAddIdealState]
theorem gidneyUncontrolledAddIdealState_correct (input : List Wire) (constant : List Bool) (s : BasisState)
    (hk : input.length=constant.length) (hnd : input.Nodup) :
    boolWordToNat (wireValues input (gidneyUncontrolledAddIdealState input constant s))=
      (boolWordToNat (wireValues input s)+boolWordToNat constant)%2^input.length ∧
    ∀ w, w ∉ input → gidneyUncontrolledAddIdealState input constant s w=s w := by
  have hlen : (wireValues input s).length=constant.length := by simp [wireValues,hk]
  have hw := gidneyWriteBits_values input (cuccaroAddBits false (wireValues input s) constant) s hnd
    (by rw [cuccaroAddBits_length _ _ _ hlen]; simp [wireValues])
  have hv := carryAddBits_value false (wireValues input s) constant hlen
  have hlo := boolWordToNat_lt_pow_two (cuccaroAddBits false (wireValues input s) constant)
  rw [cuccaroAddBits_length _ _ _ hlen] at hlo
  constructor
  · change boolWordToNat (wireValues input (gidneyWriteBits input _ s))=_
    rw [hw]
    have hh := congrArg (fun n => n%2^input.length) hv
    simpa [wireValues,Nat.add_mod,Nat.mod_eq_of_lt (by simpa [wireValues] using hlo)] using hh
  · exact fun w hw => gidneyWriteBits_frame input _ s w hw

end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
private theorem gidneyTail_allTrue_cost_le (cost : Gate → Nat)
    (hcell : ∀ q c r t a d k, ((gidneyAddCarryCell q c r t a d k).map cost).sum=0)
    (htop : ∀ (q c a : Wire) (k : Bool), (((if k then [Gate.CX q a] else []) ++ [Gate.CX c a]).map cost).sum=0)
    (input dirty : List Wire) (constant : List Bool) (q c r t : Wire)
    (callback : List Bool → Circuit) (history : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1) :
    ((callback (history ++ List.replicate input.length true)).map cost).sum ≤
      gidneyGateCount cost (gidneyAddTail q c r t callback history input dirty constant) := by
  induction input generalizing dirty constant c r history with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks=[] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        simp only [gidneyAddTail,gidneyGateCount,htop,Nat.zero_add,Nat.add_zero,List.length_singleton,List.replicate_one]
        exact Nat.le_max_right _ _
      | cons d ds =>
        simp only [gidneyAddTail,gidneyGateCount,hcell,Nat.zero_add]
        have h := ih ds ks r c (history++[true]) (by simpa using hk) (by simpa using hd)
        have he : history ++ List.replicate (a::as).length true =
            (history++[true]) ++ List.replicate as.length true := by
          simp [List.replicate_succ,List.append_assoc]
        rw [he]
        exact h.trans (Nat.le_max_right _ _)
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
private theorem gidneyRoot_plain_cost_ge (cost : Gate → Nat) (x h : Nat)
    (hX : ∀ w, cost (.X w)=x) (hH : ∀ w, cost (.H w)=h)
    (hcx : ∀ a b, cost (.CX a b)=0) (hccx : ∀ a b c, cost (.CCX a b c)=0)
    (a d q c r t : Wire) (k : Bool) (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) :
    2*(input.length+1)*x+2*(dirty.length+1)*(2*h+x) ≤
      gidneyGateCount cost (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t) := by
  have hc : ∀ q c r t a d k, ((gidneyAddCarryCell q c r t a d k).map cost).sum=0 := by
    intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell,hcx,hccx]
  have hz (ws : List Wire) :
      ((Quantum.registerZCorrection ws (List.replicate ws.length true)).map cost).sum=ws.length*(2*h+x) := by
    induction ws with
    | nil => simp [Quantum.registerZCorrection]
    | cons w ws ih =>
      simp [Quantum.registerZCorrection,Quantum.pauliZ,List.replicate_succ,hX,hH,ih,Nat.add_mul]
      omega
  have hf (ws : List Wire) : ((gidneyFlipWord ws).map cost).sum=ws.length*x := by
    induction ws with
    | nil => simp [gidneyFlipWord]
    | cons w ws ih => simp [gidneyFlipWord] at ih ⊢; rw [hX,ih]; simp [Nat.add_mul,Nat.add_comm]
  simp only [controlledGidneyAddConst,if_neg hn,gidneyGateCount,hc,Nat.zero_add]
  have ht := gidneyTail_allTrue_cost_le cost hc
    (by intro q c a k; cases k <;> simp [hcx]) input dirty constant q r c t
    (fun outcomes => Quantum.registerZCorrection (d::dirty) outcomes ++
      gidneyAddCleanup (a::input) (d::dirty) (k::constant) q c ++
      Quantum.registerZCorrection (d::dirty) outcomes) (List.nil : List Bool) hk hd
  simp only [List.nil_append] at ht
  have he : input.length=(d::dirty).length := by simp [hd]
  rw [he] at ht
  have hz' := hz (d::dirty)
  simp only [List.length_cons] at hz'
  simp only [List.map_append,List.sum_append,gidneyAddCleanup,hf,
    controlledConstCarryXor_cost_zero cost hcx hccx,List.length_cons,hz'] at ht
  simp only [gidneyAddCleanup,List.length_cons]
  simp only [Nat.mul_assoc] at *
  omega
/-- All-true reset outcomes attain both X and H budgets for a nonzero constant. -/
theorem controlledGidneyAddConst_XH_exact (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) :
    (primitiveResources (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)).x=4*(input.length+1)-2 ∧
    (primitiveResources (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)).h=4*input.length := by
  have hu := controlledGidneyAddConst_XH_le a d q c r t k input dirty constant hk hd
  have hx := gidneyRoot_plain_cost_ge primitiveXCost 1 0 (by intro w; rfl)
    (by intro w; rfl) (by intro a b; rfl) (by intro a b c; rfl)
    a d q c r t k input dirty constant hk hd hn
  have hh := gidneyRoot_plain_cost_ge primitiveHCost 0 1 (by intro w; rfl)
    (by intro w; rfl) (by intro a b; rfl) (by intro a b c; rfl)
    a d q c r t k input dirty constant hk hd hn
  simp only [primitiveResources] at hu ⊢
  constructor <;> omega
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
private theorem gidneyForward_cnot_exact (ks : List Bool) (hn : ks≠[]) :
    gidneyForwardCost (fun k => 5+3*k.toNat) (fun k => 1+k.toNat) ks=
      5*(ks.length-1)+3*constantBitWeight ks.dropLast+1+(ks.getLastD false).toNat := by
  induction ks with
  | nil => contradiction
  | cons k ks ih =>
    cases ks with
    | nil => cases k <;> simp [gidneyForwardCost,constantBitWeight]
    | cons l ls =>
      have hh := ih (by simp)
      cases k <;> simp [gidneyForwardCost,constantBitWeight] at * <;> omega
/-- The exact CNOT count depends on the first bit, interior weight and last bit. -/
theorem controlledGidneyAddConst_cnot_nonzero (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) :
    gidneyCnotCount (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)=
      5*(input.length-1)+6+8*k.toNat+10*constantBitWeight (constant.take dirty.length)+
        (constant.getLastD false).toNat := by
  have hroot := gidneyRoot_gateCount (fun g => match g with | .CX _ _ => 1 | _ => 0)
    (fun k => 5+3*k.toNat) (fun k => 1+k.toNat)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d k; cases k <;> simp [gidneyAddCarryCell])
    (by intro q c a k; cases k <;> simp) a d q c r t input dirty k constant hk hd hn
  have hki : (input.take dirty.length).length=(constant.take dirty.length).length := by simp [hk]
  have hdi : (a::input.take dirty.length).length=(d::dirty).length := by
    simp only [List.length_cons,List.length_take]; omega
  have hcleanup := (controlledConstCarryXor_counts a (input.take dirty.length) (d::dirty) k
    (constant.take dirty.length) q c hki hdi).2.2.1
  apply hroot.trans
  simp only [List.length_cons,List.take_succ_cons]
  change 5+3*k.toNat+gidneyForwardCost _ _ constant+
    eeaCnotCount (controlledConstCarryXor (a::input.take dirty.length) (d::dirty)
      (k::constant.take dirty.length) q c)=_
  rw [hcleanup,gidneyForward_cnot_exact constant (by
    intro he
    have hz : constant.length=0 := by simp only [he,List.length_nil]
    omega)]
  have he : constant.dropLast=constant.take dirty.length := by
    rw [List.dropLast_eq_take]
    congr 1
    omega
  rw [he]
  omega
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
/-- A complete exact primitive vector for every nonzero constant at width at least two. -/
theorem controlledGidneyAddConst_primitive_exact (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) :
    primitiveResources (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)=
      (⟨4*(input.length+1)-2,4*input.length,
        5*(input.length-1)+6+8*k.toNat+10*constantBitWeight (constant.take dirty.length)+
          (constant.getLastD false).toNat,
        3*(input.length+1)-4,0,input.length⟩ : PrimitiveResources) := by
  have hx := controlledGidneyAddConst_XH_exact a d q c r t k input dirty constant hk hd hn
  have hc := controlledGidneyAddConst_cnot_nonzero a d q c r t k input dirty constant hk hd hn
  have ht := controlledGidneyAddConst_toffoli_nonzero a d q c r t k input dirty constant hk hd hn
  have hp := controlledGidneyAddConst_phase_zero a d q c r t k input dirty constant hk hd
  have hm := controlledGidneyAddConst_measurementCount (a::input) (d::dirty) (k::constant) q c r t
    (by simp [hk]) (by simp [hd])
  simp only [hn,Bool.false_eq_true,if_false,List.length_cons] at hm
  simp only [primitiveResources] at hx hp ⊢
  rw [hx.1,hx.2,hc,ht,hp,hm,hd]
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
private theorem gidneyTail_lowered_cnot (input dirty : List Wire) (constant : List Bool)
    (q c r t : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hcallback : ∀ bs, eeaCnotCount ((callback bs).map (constantControlGate q))=0)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hc : c≠q) (hr : r≠q) :
    gidneyCnotCount (constantControlProgram q (gidneyAddTail q c r t callback history input dirty constant))=
      5*(input.length-1)+1 := by
  induction input generalizing dirty constant c r history with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks=[] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        have hb (bs : List Bool) : (List.map ((fun g => match g with | .CX _ _ => 1 | _ => 0) ∘ constantControlGate q) (callback bs)).sum=0 := by
          simpa only [eeaCnotCount,List.map_map] using hcallback bs
        cases k <;> simp [gidneyAddTail,constantControlProgram,gidneyCnotCount,gidneyGateCount,
          constantControlGate,hc] <;> exact ⟨hb _,hb _⟩
      | cons d ds =>
        have hcell : eeaCnotCount ((gidneyAddCarryCell q c r t a d k).map (constantControlGate q))=5 := by
          cases k <;> simp [gidneyAddCarryCell,constantControlGate,eeaCnotCount,hc,hr]
        simp only [gidneyAddTail,constantControlProgram,gidneyCnotCount,gidneyGateCount]
        change eeaCnotCount ((gidneyAddCarryCell q c r t a d k).map (constantControlGate q))+
          max (gidneyCnotCount (constantControlProgram q (gidneyAddTail q r c t callback (history++[false]) as ds ks)))
            (gidneyCnotCount (constantControlProgram q (gidneyAddTail q r c t callback (history++[true]) as ds ks)))=_
        rw [hcell,ih ds ks r c _ (by simpa using hk) (by simpa using hd) hr hc,
          ih ds ks r c _ (by simpa using hk) (by simpa using hd) hr hc,max_self]
        simp only [List.length_cons]
        have hn : 1≤as.length := by simp only [List.length_cons] at hd; omega
        omega
/-- Eliminating the fixed control leaves a pattern-independent CNOT chain. -/
private theorem controlledGidneyAddConst_lowered_cnot (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) (hc : c≠q) (hr : r≠q) :
    gidneyCnotCount (constantControlProgram q
      (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t))=
      5*(input.length-1)+6 := by
  have hz (ws : List Wire) (bs : List Bool) :
      eeaCnotCount ((Quantum.registerZCorrection ws bs).map (constantControlGate q))=0 := by
    induction ws generalizing bs with
    | nil => rfl
    | cons w ws ih => cases bs with
      | nil => rfl
      | cons b bs => cases b <;> simp [Quantum.registerZCorrection,Quantum.pauliZ,constantControlGate,eeaCnotCount] at * <;> exact ih bs
  have hf (ws : List Wire) : eeaCnotCount ((gidneyFlipWord ws).map (constantControlGate q))=0 := by
    simp [gidneyFlipWord,constantControlGate,eeaCnotCount,List.map_map,Function.comp_def]
  have hcallback : ∀ bs, eeaCnotCount (((Quantum.registerZCorrection (d::dirty) bs ++
      gidneyAddCleanup (a::input) (d::dirty) (k::constant) q c ++ Quantum.registerZCorrection (d::dirty) bs)).map (constantControlGate q))=0 := by
    intro bs
    simp only [List.map_append,eeaCnotCount_append,hz,gidneyAddCleanup,hf,
      controlledConstCarryXor_uncontrolled_cnot,Nat.add_zero]
  have hcell : eeaCnotCount ((gidneyAddCarryCell q c r t a d k).map (constantControlGate q))=5 := by
    cases k <;> simp [gidneyAddCarryCell,constantControlGate,eeaCnotCount,hc,hr]
  simp only [controlledGidneyAddConst,if_neg hn,constantControlProgram]
  change eeaCnotCount ((gidneyAddCarryCell q c r t a d k).map (constantControlGate q))+
    gidneyCnotCount (constantControlProgram q (gidneyAddTail q r c t _ _ input dirty constant))=_
  rw [hcell,gidneyTail_lowered_cnot _ _ _ _ _ _ _ _ _ hcallback hk hd hr hc]
  omega
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
private theorem gidneyTail_cost_history (cost : Gate → Nat)
    (input dirty : List Wire) (constant : List Bool) (q c r t : Wire)
    (callback : List Bool → Circuit) (history history' : List Bool) (budget : Nat)
    (hb : ∀ bs, ((callback bs).map cost).sum=budget)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1) :
    gidneyGateCount cost (gidneyAddTail q c r t callback history input dirty constant)=
      gidneyGateCount cost (gidneyAddTail q c r t callback history' input dirty constant) := by
  induction input generalizing dirty constant c r history history' with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks=[] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        simp only [gidneyAddTail,gidneyGateCount,hb]
      | cons d ds =>
        simp only [gidneyAddTail,gidneyGateCount]
        rw [ih ds ks r c (history++[false]) (history'++[false]) (by simpa using hk) (by simpa using hd),
          ih ds ks r c (history++[true]) (history'++[true]) (by simpa using hk) (by simpa using hd)]
private theorem gidneyTail_cost_add (cost plain : Gate → Nat)
    (input dirty : List Wire) (constant : List Bool) (q c r t : Wire)
    (callback : List Bool → Circuit) (history : List Bool) (budget : Nat)
    (hb : ∀ bs, ((callback bs).map plain).sum=budget)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1) :
    gidneyGateCount (fun g => cost g+plain g) (gidneyAddTail q c r t callback history input dirty constant)=
      gidneyGateCount cost (gidneyAddTail q c r t callback history input dirty constant)+
      gidneyGateCount plain (gidneyAddTail q c r t callback history input dirty constant) := by
  induction input generalizing dirty constant c r history with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil =>
        have he : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
        subst as
        have he : ks=[] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
        subst ks
        simp [gidneyAddTail,gidneyGateCount,List.sum_map_add,hb,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      | cons d ds =>
        have hp := gidneyTail_cost_history plain as ds ks q r c t callback
          (history++[false]) (history++[true]) budget hb (by simpa using hk) (by simpa using hd)
        simp only [gidneyAddTail,gidneyGateCount,List.sum_map_add]
        rw [ih ds ks r c _ (by simpa using hk) (by simpa using hd),
          ih ds ks r c _ (by simpa using hk) (by simpa using hd),hp,max_self,max_add_add_right]
        omega
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
private theorem gidneyRoot_cost_add (cost plain : Gate → Nat)
    (hX : ∀ w, plain (.X w)=0) (hH : ∀ w, plain (.H w)=0)
    (a d q c r t : Wire) (k : Bool) (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) :
    gidneyGateCount (fun g => cost g+plain g) (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)=
      gidneyGateCount cost (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)+
      gidneyGateCount plain (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t) := by
  simp only [controlledGidneyAddConst,if_neg hn,gidneyGateCount,List.sum_map_add]
  rw [gidneyTail_cost_add cost plain input dirty constant q r c t _ _
    ((gidneyAddCleanup (a::input) (d::dirty) (k::constant) q c).map plain).sum
    (by intro bs; simp [List.map_append,List.sum_append,gidneyZ_cost plain hX hH]) hk hd]
  omega
private theorem gidneyCount_control (cost : Gate → Nat) (q : Wire) (ac : Quantum.AdaptiveCircuit) :
    gidneyGateCount cost (constantControlProgram q ac)=gidneyGateCount (fun g => cost (constantControlGate q g)) ac := by
  induction ac with
  | done => rfl
  | unitary g ac ih => simp [constantControlProgram,gidneyGateCount,List.map_map,Function.comp_def,ih]
  | xMeasureReset w ac bc iha ihb => simp [constantControlProgram,gidneyGateCount,iha,ihb]
/-- Fixed-control compilation preserves the combined X/CNOT maximum for this adder. -/
private theorem controlledGidneyAddConst_lowered_XC (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) :
    let ac := controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t
    (primitiveResources (constantControlProgram q ac)).x+(primitiveResources (constantControlProgram q ac)).cnot=
      (primitiveResources ac).x+(primitiveResources ac).cnot := by
  simp only [primitiveResources,gidneyCnotCount,gidneyCount_control]
  have hfirst := gidneyRoot_cost_add (fun g => primitiveXCost (constantControlGate q g))
    (fun g => match constantControlGate q g with | .CX _ _ => 1 | _ => 0)
    (by intro w; rfl) (by intro w; rfl) a d q c r t k input dirty constant hk hd hn
  have he : (fun g => primitiveXCost (constantControlGate q g)+
      (match constantControlGate q g with | .CX _ _ => 1 | _ => 0))=
      (fun g => primitiveXCost g+(match g with | .CX _ _ => 1 | _ => 0)) := by
    funext g
    cases g with
    | CX c t => by_cases h : c=q <;> simp [constantControlGate,primitiveXCost,h]
    | _ => rfl
  have hlast := gidneyRoot_cost_add primitiveXCost (fun g => match g with | .CX _ _ => 1 | _ => 0)
    (by intro w; rfl) (by intro w; rfl) a d q c r t k input dirty constant hk hd hn
  exact hfirst.symm.trans ((congrArg (fun f => gidneyGateCount f
    (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)) he).trans hlast)
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- CNOTs removed by fixed-control compilation become X gates. -/
private theorem controlledGidneyAddConst_lowered_x (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) (hc : c≠q) (hr : r≠q) :
    (primitiveResources (constantControlProgram q
      (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t))).x=
      4*(input.length+1)-2+8*k.toNat+10*constantBitWeight (constant.take dirty.length)+
        (constant.getLastD false).toNat := by
  have hs := controlledGidneyAddConst_lowered_XC a d q c r t k input dirty constant hk hd hn
  have hx := controlledGidneyAddConst_XH_exact a d q c r t k input dirty constant hk hd hn
  have ho := controlledGidneyAddConst_cnot_nonzero a d q c r t k input dirty constant hk hd hn
  have hl := controlledGidneyAddConst_lowered_cnot a d q c r t k input dirty constant hk hd hn hc hr
  dsimp only at hs
  simp only [primitiveResources] at hs hx ⊢
  rw [hx.1,ho,hl] at hs
  omega
/-- Complete exact vector after eliminating the fixed external control. -/
theorem controlledGidneyAddConst_lowered_primitive_exact (a d q c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) (hc : c≠q) (hr : r≠q) :
    primitiveResources (constantControlProgram q
      (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t))=
      (⟨4*(input.length+1)-2+8*k.toNat+10*constantBitWeight (constant.take dirty.length)+
          (constant.getLastD false).toNat,4*input.length,5*(input.length-1)+6,
        3*(input.length+1)-4,0,input.length⟩ : PrimitiveResources) := by
  have hx := controlledGidneyAddConst_lowered_x a d q c r t k input dirty constant hk hd hn hc hr
  have hl := controlledGidneyAddConst_lowered_cnot a d q c r t k input dirty constant hk hd hn hc hr
  have hp := primitiveResources_constantControl_preserved q
    (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)
  rw [controlledGidneyAddConst_primitive_exact a d q c r t k input dirty constant hk hd hn] at hp
  cases he : primitiveResources (constantControlProgram q
    (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t)) with
  | mk x h cx ccx p m =>
    have hcx : (primitiveResources (constantControlProgram q
      (controlledGidneyAddConst (a::input) (d::dirty) (k::constant) q c r t))).cnot=5*(input.length-1)+6 := hl
    simp only [he] at hx hp hcx
    simp only [PrimitiveResources.mk.injEq]
    exact ⟨hx,hp.1,hcx,hp.2.1,hp.2.2.1,hp.2.2.2⟩
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
private def gidneyAddSourceTail (q current spare ancilla : Wire)
    (callback : List Bool → List CorrectionFragment) (outcomes : List Bool) :
    List Wire → List Wire → List Bool → CorrectionProgram
  | [a],[],[k] => .unitary [.ordinary ((if k then [.CX q a] else []) ++ [.CX current a])]
      (.reset current (.unitary (callback (outcomes++[false])) .done)
        (.unitary (callback (outcomes++[true])) .done))
  | a::input,d::dirty,k::constant =>
      .unitary [.ordinary (gidneyAddCarryCell q current spare ancilla a d k)]
        (.reset current
          (gidneyAddSourceTail q spare current ancilla callback (outcomes++[false]) input dirty constant)
          (gidneyAddSourceTail q spare current ancilla callback (outcomes++[true]) input dirty constant))
  | _,_,_ => .done
private theorem gidneyAddSourceTail_erase (q current spare ancilla : Wire)
    (callback : List Bool → List CorrectionFragment) (outcomes : List Bool) (input dirty : List Wire) (constant : List Bool) :
    (gidneyAddSourceTail q current spare ancilla callback outcomes input dirty constant).erase=
      gidneyAddTail q current spare ancilla (fun bs => correctionBlockErase (callback bs)) outcomes input dirty constant := by
  induction input generalizing current spare outcomes dirty constant with
  | nil => cases dirty <;> cases constant <;> rfl
  | cons a input ih =>
    cases dirty with
    | nil => cases input <;> cases constant with
      | nil => rfl
      | cons k ks => cases ks <;> simp [gidneyAddSourceTail,gidneyAddTail,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
    | cons d dirty =>
      cases constant with
      | nil => cases input <;> rfl
      | cons k ks =>
        simp [gidneyAddSourceTail,gidneyAddTail,CorrectionProgram.erase,
          correctionBlockErase,CorrectionFragment.erase,ih]
/-- The actual controlled Gidney adder with both deferred correction copies marked. -/
def controlledGidneyAddConstSource (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) : CorrectionProgram :=
  if constant.all (fun k => !k) then .done else
  match input,dirty,constant with
  | [a],[],[k] => .unitary [.ordinary (if k then [.CX q a] else [])] .done
  | a::input,d::dirty,k::constant =>
      let callback := fun bs => doubleZCorrectionFragments (d::dirty) bs
        (gidneyAddCleanup (a::input) (d::dirty) (k::constant) q carry)
      .unitary [.ordinary (gidneyAddCarryCell q carry spare ancilla a d k)]
        (gidneyAddSourceTail q spare carry ancilla callback (List.nil : List Bool) input dirty constant)
  | _,_,_ => .done
theorem controlledGidneyAddConstSource_erase (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) :
    (controlledGidneyAddConstSource input dirty constant q carry spare ancilla).erase=
      controlledGidneyAddConst input dirty constant q carry spare ancilla := by
  have hz (ws : List Wire) (bs : List Bool) (middle : Circuit) := doubleZCorrectionFragments_erase ws bs middle
  simp only [correctionBlockErase] at hz
  unfold controlledGidneyAddConstSource controlledGidneyAddConst
  split
  · rfl
  · cases input with
    | nil => cases dirty <;> cases constant <;> rfl
    | cons a input =>
      cases dirty with
      | nil => cases input <;> cases constant with
        | nil => rfl
        | cons k ks => cases ks <;> simp [CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
      | cons d dirty =>
        cases constant with
        | nil => cases input <;> rfl
        | cons k ks =>
          simp [CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,
            gidneyAddSourceTail_erase,hz,List.append_assoc]
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
private theorem gidneyAddSourceTail_events (q current spare ancilla : Wire)
    (callback : List Bool → List CorrectionFragment) (outcomes : List Bool)
    (input dirty : List Wire) (constant : List Bool) (N base perTrue : Nat)
    (hd : input.length=dirty.length+1) (hk : constant.length=input.length)
    (hp : outcomes.length+input.length=N)
    (hc : ∀ bs, bs.length=N → correctionBlockEvents (callback bs)=base+perTrue*bs.count true) :
    (gidneyAddSourceTail q current spare ancilla callback outcomes input dirty constant).events=
      base+perTrue*(outcomes.count true+input.length) := by
  induction input generalizing current spare outcomes dirty constant with
  | nil => simp at hd
  | cons a input ih =>
    cases input with
    | nil =>
      have hd0 : dirty=[] := by
        have hh : dirty.length=0 := by simpa using hd.symm
        simpa using hh
      have hk1 : constant.length=1 := by simpa using hk
      obtain ⟨k,rfl⟩ : ∃ k, constant=[k] := by
        cases constant with
        | nil => simp at hk1
        | cons k ks =>
          have ht : ks=[] := by simpa using hk1
          exact ⟨k, by rw [ht]⟩
      subst dirty
      have hf := hc (outcomes++[false]) (by simpa using hp)
      have ht := hc (outcomes++[true]) (by simpa using hp)
      simp only [gidneyAddSourceTail,CorrectionProgram.events,correctionBlockEvents,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,CorrectionFragment.events,Nat.zero_add]
      simp only [correctionBlockEvents] at hf ht
      rw [hf,ht]
      simp
    | cons a' input =>
      cases dirty with
      | nil => simp at hd
      | cons d dirty =>
        cases constant with
        | nil => simp at hk
        | cons k constant =>
          have hdt : (a'::input).length=dirty.length+1 := by simpa using hd
          have hkt : constant.length=(a'::input).length := by simpa using hk
          have hf := ih spare current (outcomes++[false]) dirty constant hdt hkt (by
            simp only [List.length_append,List.length_cons,List.length_nil] at *; omega)
          have ht := ih spare current (outcomes++[true]) dirty constant hdt hkt (by
            simp only [List.length_append,List.length_cons,List.length_nil] at *; omega)
          simp only [gidneyAddSourceTail,CorrectionProgram.events,correctionBlockEvents,
            List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,CorrectionFragment.events,Nat.zero_add,hf,ht]
          simp
          omega
/-- A nonzero n-bit addition has two selected correction copies over n-1 carries. -/
theorem controlledGidneyAddConstSource_events (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hi : 0 < input.length)
    (hd : dirty.length=input.length-1) (hk : constant.length=input.length) :
    (controlledGidneyAddConstSource input dirty constant q carry spare ancilla).events=
      if constant.all (fun k => !k) then 0 else 2*(input.length-1) := by
  unfold controlledGidneyAddConstSource
  split
  · rfl
  · cases input with
    | nil => simp at hi
    | cons a input =>
      cases input with
      | nil =>
        have hd0 : dirty=[] := by simpa using hd
        have hk1 : constant.length=1 := by simpa using hk
        obtain ⟨k,rfl⟩ : ∃ k, constant=[k] := by
          cases constant with
          | nil => simp at hk1
          | cons k ks =>
            have ht : ks=[] := by simpa using hk1
            exact ⟨k, by rw [ht]⟩
        subst dirty
        rfl
      | cons a' input =>
        cases dirty with
        | nil => simp at hd
        | cons d dirty =>
          cases constant with
          | nil => simp at hk
          | cons k constant =>
            simp only [CorrectionProgram.events,correctionBlockEvents,List.map_cons,List.map_nil,
              List.sum_cons,List.sum_nil,CorrectionFragment.events,Nat.zero_add]
            have hh := gidneyAddSourceTail_events q spare carry ancilla
              (fun bs => doubleZCorrectionFragments (d::dirty) bs
                (gidneyAddCleanup (a::a'::input) (d::dirty) (k::constant) q carry))
              (List.nil : List Bool) (a'::input) dirty constant (input.length+1) 0 2
              (by simp only [List.length_cons] at *; omega) (by simpa using hk) (by simp) (by
                intro bs hb
                simpa using doubleZCorrectionFragments_events (d::dirty) bs _ (by simpa [hd] using hb))
            simpa using hh
end ShorECDLP.Paper2607_13816
