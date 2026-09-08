import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyCarry

/-!
# Measurement-assisted constant comparison

Literal controlled `append_gidney_compare_ge_const`: the input is restored in each
forward carry cell, the final carry toggles an arbitrary result flag, and paired Z
corrections around borrowed-carry erasure cancel the measurement phases.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

/-- A source comparison carry cell; only the last cell toggles the result flag. -/
def gidneyCompareCarryCell (q current spare ancilla input dirty flag : Wire)
    (constant last : Bool) : Circuit :=
  (if constant then [.CX q ancilla] else []) ++
    [.CX current ancilla, .CX current input, .CCX input ancilla spare,
      .CX current spare, .CX spare dirty] ++
    (if last then [.CX spare flag] else []) ++
    [.CX current input, .CX current ancilla] ++
    (if constant then [.CX q ancilla] else [])

private def gidneyCompareTail (q current spare ancilla flag : Wire)
    (callback : List Bool → Circuit) (outcomes : List Bool) :
    List Wire → List Wire → List Bool → Quantum.AdaptiveCircuit
  | [], [], [] => .xMeasureReset current
      (.unitary (callback (outcomes ++ [false])) .done)
      (.unitary (callback (outcomes ++ [true])) .done)
  | a :: input, d :: dirty, k :: constant =>
      .unitary (gidneyCompareCarryCell q current spare ancilla a d flag k input.isEmpty)
        (.xMeasureReset current
          (gidneyCompareTail q spare current ancilla flag callback (outcomes ++ [false]) input dirty constant)
          (gidneyCompareTail q spare current ancilla flag callback (outcomes ++ [true]) input dirty constant))
  | _, _, _ => .done

/-- Controlled carry-out comparison core, using a fixed-width complement of the threshold. -/
def controlledGidneyCompareCarry (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) : Quantum.AdaptiveCircuit :=
  match input, dirty, constant with
  | a :: input, d :: dirty, k :: constant =>
      let callback := fun outcomes =>
        Quantum.registerZCorrection (d :: dirty) outcomes ++
          controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q carry ++
          Quantum.registerZCorrection (d :: dirty) outcomes
      .unitary (gidneyCompareCarryCell q carry spare ancilla a d flag k input.isEmpty)
        (gidneyCompareTail q spare carry ancilla flag callback (List.nil : List Bool) input dirty constant)
  | _, _, _ => .done

/-- Literal source threshold interface, including zero and out-of-range shortcuts. -/
def controlledGidneyCompareGE (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) : Quantum.AdaptiveCircuit :=
  if threshold = 0 then .unitary [.CX q flag] .done
  else if 2 ^ input.length ≤ threshold then .done
  else controlledGidneyCompareCarry input dirty
    ((List.range input.length).map (Nat.testBit (2 ^ input.length - threshold)))
    q carry spare ancilla flag

private theorem gidneyCompareCell_state (q c r t a d f : Wire) (k last : Bool) (s : BasisState)
    (hnd : [q,c,r,t,a,d,f].Nodup) (hr : s r = false) (ht : s t = false) :
    run (gidneyCompareCarryCell q c r t a d f k last) s =
      upd (upd (upd s r (cuccaroCarry (s a) (s q && k) (s c)))
        d (Bool.xor (s d) (cuccaroCarry (s a) (s q && k) (s c))))
        f (Bool.xor (s f) (last && cuccaroCarry (s a) (s q && k) (s c))) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
  rcases hnd with ⟨⟨hqc,hqr,hqt,hqa,hqd,hqf⟩,⟨⟨hcr,hct,hca,hcd,hcf⟩,
    ⟨⟨hrt,hra,hrd,hrf⟩,⟨⟨hta,htd,htf⟩,⟨⟨had,haf⟩,hdf,_⟩⟩⟩⟩⟩
  funext w
  cases k <;> cases last <;>
    simp only [gidneyCompareCarryCell,Bool.false_eq_true,↓reduceIte,
      List.nil_append,List.append_nil,run_append,run_cons,run_nil,applyGate]
  all_goals
    by_cases hwr : w = r <;> by_cases hwd : w = d <;> by_cases hwf : w = f <;> by_cases hwa : w = a <;> by_cases hwt : w = t <;>
      simp_all [upd,cuccaroCarry,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm,
        Ne.symm hqc,Ne.symm hqr,Ne.symm hqt,Ne.symm hqa,Ne.symm hqd,Ne.symm hqf,
        Ne.symm hcr,Ne.symm hct,Ne.symm hca,Ne.symm hcd,Ne.symm hcf,
        Ne.symm hrt,Ne.symm hra,Ne.symm hrd,Ne.symm hrf,
        Ne.symm hta,Ne.symm htd,Ne.symm htf,Ne.symm had,Ne.symm haf,Ne.symm hdf]
  all_goals cases hsa : s a <;> cases hsc : s c <;> cases hsq : s q <;> cases hsd : s d <;> simp_all


private theorem gidneyCompareCell_resources (q c r t a d f : Wire) (k last : Bool) :
    HPFree (gidneyCompareCarryCell q c r t a d f k last) ∧
    eeaToffoliCount (gidneyCompareCarryCell q c r t a d f k last) = 1 ∧
    eeaCnotCount (gidneyCompareCarryCell q c r t a d f k last) = 6 + 2 * k.toNat + last.toNat ∧
    tCount (gidneyCompareCarryCell q c r t a d f k last) = 7 := by
  cases k <;> cases last <;> simp [gidneyCompareCarryCell,eeaToffoliCount,eeaCnotCount,tCount,tCost]

private def gidneyCompareCellState (q c r a d f : Wire) (k last : Bool) (s : BasisState) : BasisState :=
  upd (upd (upd s r (cuccaroCarry (s a) (s q && k) (s c)))
    d (Bool.xor (s d) (cuccaroCarry (s a) (s q && k) (s c))))
    f (Bool.xor (s f) (last && cuccaroCarry (s a) (s q && k) (s c)))

private def gidneyCompareTrace (q c r f : Wire) : List Wire → List Wire → List Bool → BasisState → BasisState × List Bool
  | [], [], [], s => (upd s c false,[s c])
  | a :: input, d :: dirty, k :: constant, s =>
      let mid := gidneyCompareCellState q c r a d f k input.isEmpty s
      let tail := gidneyCompareTrace q r c f input dirty constant (upd mid c false)
      (tail.1,s c :: tail.2)
  | _, _, _, s => (s,[])

private def gidneyCompareReady (q c r t f : Wire) : List Wire → List Wire → List Bool → BasisState → Prop
  | [], [], [], _ => True
  | a :: input, d :: dirty, k :: constant, s =>
      [q,c,r,t,a,d,f].Nodup ∧ s r = false ∧ s t = false ∧
        gidneyCompareReady q r c t f input dirty constant
          (upd (gidneyCompareCellState q c r a d f k input.isEmpty s) c false)
  | _, _, _, _ => False

private theorem gidneyCompareCell_current (q c r t a d f : Wire) (k last : Bool) (s : BasisState)
    (hnd : [q,c,r,t,a,d,f].Nodup) : gidneyCompareCellState q c r a d f k last s c = s c := by
  have hcr : c ≠ r := by simp_all
  have hcd : c ≠ d := by simp_all
  have hcf : c ≠ f := by simp_all
  simp [gidneyCompareCellState,upd,hcr,hcd,hcf]

private theorem gidneyCompareTail_branch (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (s : BasisState) (callback : List Bool → Circuit) (historyPrefix : List Bool)
    (hready : gidneyCompareReady q c r t f input dirty constant s)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (gidneyCompareTail q c r t f callback historyPrefix input dirty constant).run) :
    ∃ outcomes, branch.history = outcomes ∧ outcomes.length = input.length + 1 ∧
      branch.kraus (Quantum.ket s) =
        gidneyRawCoefficient outcomes (gidneyCompareTrace q c r f input dirty constant s).2 •
          Quantum.run (callback (historyPrefix ++ outcomes))
            (Quantum.ket (gidneyCompareTrace q c r f input dirty constant s).1) := by
  induction input generalizing dirty constant c r s historyPrefix branch with
  | nil =>
    cases dirty with
    | cons d ds => simp [gidneyCompareReady] at hready
    | nil =>
      cases constant with
      | cons k ks => simp [gidneyCompareReady] at hready
      | nil =>
        obtain ⟨outcome,rest,hr,hrest,hmeasure⟩ := gidneyMeasureBranch c _ _ branch hb
        have hr' : rest ∈ (Quantum.AdaptiveCircuit.unitary (callback (historyPrefix ++ [outcome])) .done).run := by
          cases outcome <;> exact hr
        obtain ⟨last,hl,hlhist,hlsem⟩ := gidneyUnitaryBranch _ _ rest hr'
        have hlast := gidneyDoneBranch last hl
        refine ⟨[outcome],?_,rfl,?_⟩
        · rw [hrest,hlhist,hlast.1]
        · rw [hmeasure,Quantum.xResetKraus_ket,map_smul,hlsem,hlast.2]
          simp only [gidneyCompareTrace,gidneyRawCoefficient,mul_one]
  | cons a input ih =>
    cases dirty with
    | nil => simp [gidneyCompareReady] at hready
    | cons d dirty =>
      cases constant with
      | nil => simp [gidneyCompareReady] at hready
      | cons k constant =>
        simp only [gidneyCompareReady] at hready
        rcases hready with ⟨hnd,hr,ht,hnext⟩
        let mid := gidneyCompareCellState q c r a d f k input.isEmpty s
        let cleared := upd mid c false
        have hmc : mid c = s c := gidneyCompareCell_current q c r t a d f k input.isEmpty s hnd
        simp only [gidneyCompareTail] at hb
        obtain ⟨measured,hm,hist,hsem⟩ := gidneyUnitaryBranch _ _ branch hb
        obtain ⟨outcome,rest,hrest,hrestHist,hmeasure⟩ := gidneyMeasureBranch c _ _ measured hm
        have hrest' : rest ∈ (gidneyCompareTail q r c t f callback (historyPrefix ++ [outcome]) input dirty constant).run := by
          cases outcome <;> exact hrest
        obtain ⟨outcomes,hout,hcount,hresult⟩ := ih dirty constant r c cleared (historyPrefix ++ [outcome]) hnext rest hrest'
        refine ⟨outcome :: outcomes,?_,by simp [hcount],?_⟩
        · rw [hist,hrestHist,hout]
        · rw [hsem,Quantum.run_ket_agrees_classical _ s (gidneyCompareCell_resources q c r t a d f k input.isEmpty).1,
            gidneyCompareCell_state q c r t a d f k input.isEmpty s hnd hr ht]
          change measured.kraus (Quantum.ket mid) = _
          rw [hmeasure,Quantum.xResetKraus_ket,hmc,map_smul]
          change Quantum.xResetCoeff outcome (s c) • rest.kraus (Quantum.ket cleared) = _
          rw [hresult]
          simp only [gidneyCompareTrace,gidneyRawCoefficient,smul_smul,List.append_assoc,List.singleton_append]
          rfl


private theorem gidneyCompareLayoutStep (q c r t f a d : Wire) (input dirty : List Wire)
    (hnd : ([q,c,r,t,f] ++ (a :: input) ++ d :: dirty).Nodup) :
    [q,c,r,t,a,d,f].Nodup ∧ ([q,r,c,t,f] ++ input ++ dirty).Nodup := by
  have hsA : [a].Sublist (a :: input) := List.Sublist.cons₂ a (List.nil_sublist _)
  have hsD : [d].Sublist (d :: dirty) := List.Sublist.cons₂ d (List.nil_sublist _)
  have hcell := List.Nodup.sublist (((List.Sublist.refl [q,c,r,t,f]).append hsA).append hsD) hnd
  have htail := List.Nodup.sublist
    (((List.Sublist.refl [q,c,r,t,f]).append (List.sublist_cons_self a input)).append
      (List.sublist_cons_self d dirty)) hnd
  have hperm : ([q,r,c,t,f] ++ input ++ dirty).Perm ([q,c,r,t,f] ++ input ++ dirty) :=
    List.Perm.cons q (List.Perm.swap c r (t :: f :: input ++ dirty))
  refine ⟨?_,hperm.nodup_iff.mpr htail⟩
  simp only [List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hcell ⊢
  tauto

private theorem gidneyCompareReady_of_layout (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length) (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup)
    (hr : s r = false) (ht : s t = false) :
    gidneyCompareReady q c r t f input dirty constant s := by
  induction input generalizing dirty constant c r s with
  | nil =>
    have he : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have he' : constant = [] := List.eq_nil_of_length_eq_zero hk.symm
    subst dirty; subst constant; trivial
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        have hl := gidneyCompareLayoutStep q c r t f a d input dirty hnd
        refine ⟨hl.1,hr,ht,?_⟩
        apply ih dirty constant r c _ (by simpa using hk) (by simpa using hd) hl.2
        · simp [upd]
        · have htc : t ≠ c := by intro h; subst t; simp at hl
          have htr : t ≠ r := by intro h; subst t; simp at hl
          have htd : t ≠ d := by intro h; subst t; simp at hl
          have htf : t ≠ f := by intro h; subst t; simp at hl
          simp [upd,gidneyCompareCellState,htc,htr,htd,htf,ht]

private theorem gidneyCompareTrace_frame (input dirty : List Wire) (constant : List Bool)
    (q c r f : Wire) (s : BasisState) (w : Wire) (hw : w ∉ c :: r :: f :: dirty) :
    (gidneyCompareTrace q c r f input dirty constant s).1 w = s w := by
  induction input generalizing dirty constant c r s with
  | nil =>
    cases dirty <;> cases constant <;> simp_all [gidneyCompareTrace,upd]
  | cons a input ih =>
    cases dirty with
    | nil => simp [gidneyCompareTrace]
    | cons d dirty =>
      cases constant with
      | nil => simp [gidneyCompareTrace]
      | cons k constant =>
        simp only [List.mem_cons,not_or] at hw
        rw [gidneyCompareTrace,ih dirty constant r c _ (by simp_all)]
        simp [gidneyCompareCellState,upd,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1]


private theorem gidneyCompareTrace_arithmetic (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length) (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup) :
    let result := gidneyCompareTrace q c r f input dirty constant s
    let carries := constantCarryBits (s c) (wireValues input s) (constant.map (fun k => s q && k))
    wireValues dirty result.1 = List.zipWith Bool.xor (wireValues dirty s) carries ∧
      result.2 = s c :: carries ∧
      result.1 f = Bool.xor (s f) (if input.isEmpty then false else
        carryAddOverflow (s c) (wireValues input s) (constant.map (fun k => s q && k))) := by
  induction input generalizing dirty constant c r s with
  | nil =>
    have he : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have he' : constant = [] := List.eq_nil_of_length_eq_zero hk.symm
    subst dirty; subst constant
    have hfc : f ≠ c := by intro h; subst f; simp at hnd
    simp [gidneyCompareTrace,constantCarryBits,wireValues,upd,hfc]
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        have hl := gidneyCompareLayoutStep q c r t f a d input dirty hnd
        have hperm : ([q,c,r,t,f] ++ (a :: input) ++ d :: dirty).Perm
            ([q,c,r,t,f,a,d] ++ input ++ dirty) := by
          simpa only [List.cons_append,List.nil_append,List.append_assoc] using
            (List.perm_middle (a := d) (l₁ := input) (l₂ := dirty)).append_left [q,c,r,t,f,a]
        have hsplit := List.nodup_append.mp (show ([q,c,r,t,f,a,d] ++ (input ++ dirty)).Nodup by
          simpa only [List.append_assoc] using hperm.nodup_iff.mp hnd)
        have hnotTail (w : Wire) (hw : w ∈ [q,c,r,t,f,a,d]) : w ∉ input ++ dirty :=
          fun hw' => hsplit.2.2 w hw w hw' rfl
        have hnotHead (w : Wire) (hw : w ∈ input ++ dirty) : w ∉ [q,c,r,t,f,a,d] :=
          fun hw' => hsplit.2.2 w hw' w hw rfl
        have hcell := hl.1
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hcell
        rcases hcell with ⟨⟨hqc,hqr,hqt,hqa,hqd,hqf⟩,⟨⟨hcr,hct,hca,hcd,hcf⟩,
          ⟨⟨hrt,hra,hrd,hrf⟩,⟨⟨hta,htd,htf⟩,⟨⟨had,haf⟩,hdf,_⟩⟩⟩⟩⟩
        let next := cuccaroCarry (s a) (s q && k) (s c)
        let cleared := upd (gidneyCompareCellState q c r a d f k input.isEmpty s) c false
        have hframe (w : Wire) (hw : w ∉ [d,c,r,f]) : cleared w = s w := by
          have hp : w ≠ d ∧ w ≠ c ∧ w ≠ r ∧ w ≠ f := by simpa using hw
          simp [cleared,gidneyCompareCellState,upd,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
        have hq : cleared q = s q := hframe q (by simp [hqd,hqc,hqr,hqf])
        have hdv : cleared d = Bool.xor (s d) next := by
          simp [cleared,gidneyCompareCellState,upd,Ne.symm hcd,hdf,next]
        have hrv : cleared r = next := by
          simp [cleared,gidneyCompareCellState,upd,hrd,hrf,Ne.symm hcr,next]
        have hfv : cleared f = Bool.xor (s f) (input.isEmpty && next) := by
          simp [cleared,gidneyCompareCellState,upd,Ne.symm hcf,next]
        have hread (ws : List Wire) (hs : ∀ w ∈ ws, w ∈ input ++ dirty) : wireValues ws cleared = wireValues ws s := by
          apply List.map_congr_left
          intro w hw
          apply hframe
          have hn := hnotHead w (hs w hw)
          simp only [List.mem_cons,List.not_mem_nil] at hn ⊢; tauto
        have hinput := hread input (by intro w hw; simp [hw])
        have hdirty := hread dirty (by intro w hw; simp [hw])
        have hheadD : d ∉ r :: c :: f :: dirty := by
          have hn := hnotTail d (by simp)
          simp only [List.mem_append,not_or] at hn
          simp [Ne.symm hrd,Ne.symm hcd,hdf,hn.2]
        have ht := ih dirty constant r c cleared (by simpa using hk) (by simpa using hd) hl.2
        dsimp only at ht ⊢
        simp only [gidneyCompareTrace]
        refine ⟨?_,?_,?_⟩
        · change (gidneyCompareTrace q r c f input dirty constant cleared).1 d ::
            wireValues dirty (gidneyCompareTrace q r c f input dirty constant cleared).1 = _
          rw [gidneyCompareTrace_frame input dirty constant q r c f cleared d hheadD,
            ht.1,hdv,hrv,hinput,hq,hdirty]
          rfl
        · rw [ht.2.1,hrv,hinput,hq]
          rfl
        · rw [ht.2.2,hfv,hrv,hinput,hq]
          cases input with
          | nil =>
            have he : constant = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
            subst constant
            simp [carryAddOverflow,wireValues,next]
          | cons b bs => simp [carryAddOverflow,wireValues,next]


private theorem gidneyCompareTrace_clean (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length) (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup)
    (hr : s r = false) :
    (gidneyCompareTrace q c r f input dirty constant s).1 c = false ∧
      (gidneyCompareTrace q c r f input dirty constant s).1 r = false := by
  induction input generalizing dirty constant c r s with
  | nil =>
    have he : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have he' : constant = [] := List.eq_nil_of_length_eq_zero hk.symm
    subst dirty; subst constant
    have hrc : r ≠ c := by intro h; subst r; simp at hnd
    simp [gidneyCompareTrace,upd,hrc,hr]
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        have hl := gidneyCompareLayoutStep q c r t f a d input dirty hnd
        have hh := ih dirty constant r c (upd (gidneyCompareCellState q c r a d f k input.isEmpty s) c false) (by simpa using hk) (by simpa using hd) hl.2 (by simp [upd])
        exact ⟨hh.2,hh.1⟩

private theorem gidneyCompareRoot_branch (a d q c r t f : Wire) (input dirty : List Wire)
    (k : Bool) (constant : List Bool) (s : BasisState) (callback : List Bool → Circuit)
    (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (hnd : ([q,c,r,t,f] ++ (a :: input) ++ d :: dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (Quantum.AdaptiveCircuit.unitary (gidneyCompareCarryCell q c r t a d f k input.isEmpty)
      (gidneyCompareTail q r c t f callback (List.nil : List Bool) input dirty constant)).run) :
    ∃ outcomes, branch.history = outcomes ∧ outcomes.length = (d :: dirty).length ∧
      branch.kraus (Quantum.ket s) =
        gidneyRawCoefficient outcomes (constantCarryBits false (wireValues (a :: input) s)
          ((k :: constant).map (fun k => s q && k))) •
          Quantum.run (callback outcomes)
            (Quantum.ket (gidneyCompareTrace q c r f (a :: input) (d :: dirty) (k :: constant) s).1) := by
  have hl := gidneyCompareLayoutStep q c r t f a d input dirty hnd
  let mid := gidneyCompareCellState q c r a d f k input.isEmpty s
  have hmc : mid c = false := (gidneyCompareCell_current q c r t a d f k input.isEmpty s hl.1).trans hc
  have hreset : upd mid c false = mid := by
    funext w; by_cases hw : w = c <;> simp [upd,hw,hmc]
  have hready := gidneyCompareReady_of_layout (a :: input) (d :: dirty) (k :: constant)
    q c r t f s (by simpa using hk) (by simpa using hd) hnd hr ht
  simp only [gidneyCompareReady] at hready
  have hnext := hready.2.2.2
  change gidneyCompareReady q r c t f input dirty constant (upd mid c false) at hnext
  rw [hreset] at hnext
  obtain ⟨rest,hrest,hhist,hsem⟩ := gidneyUnitaryBranch _ _ branch hb
  obtain ⟨outcomes,hout,hcount,hresult⟩ := gidneyCompareTail_branch input dirty constant q r c t f mid
    callback (List.nil : List Bool) hnext rest hrest
  have harith := gidneyCompareTrace_arithmetic (a :: input) (d :: dirty) (k :: constant) q c r t f s
    (by simpa using hk) (by simpa using hd) hnd
  have hrecord := congrArg List.tail harith.2.1
  simp only [gidneyCompareTrace,List.tail_cons] at hrecord
  change (gidneyCompareTrace q r c f input dirty constant (upd mid c false)).2 = _ at hrecord
  rw [hreset,hc] at hrecord
  refine ⟨outcomes,hhist.trans hout,by simpa [hd] using hcount,?_⟩
  rw [hsem,Quantum.run_ket_agrees_classical _ s (gidneyCompareCell_resources q c r t a d f k input.isEmpty).1,
    gidneyCompareCell_state q c r t a d f k input.isEmpty s hl.1 hr ht]
  change rest.kraus (Quantum.ket mid) = _
  rw [hresult,hrecord]
  simp only [gidneyCompareTrace,List.nil_append]
  change _ = _ • Quantum.run (callback outcomes)
    (Quantum.ket (gidneyCompareTrace q r c f input dirty constant (upd mid c false)).1)
  rw [hreset]


/-- Direct ideal for the fixed-complement comparison core: toggle only the final carry. -/
def gidneyCompareIdealState (input : List Wire) (constant : List Bool) (q f : Wire) (s : BasisState) : BasisState :=
  upd s f (Bool.xor (s f) (carryAddOverflow false (wireValues input s) (constant.map (fun k => s q && k))))

private theorem gidneyCompareCleanup (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length) (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) :
    run (controlledConstCarryXor input dirty constant q c)
      (gidneyCompareTrace q c r f input dirty constant s).1 = gidneyCompareIdealState input constant q f s := by
  let forward := (gidneyCompareTrace q c r f input dirty constant s).1
  have hroles := List.nodup_append.mp (show ([q,c,r,t,f] ++ (input ++ dirty)).Nodup by
    simpa only [List.append_assoc] using hnd)
  have hnot (w : Wire) (hw : w ∈ [q,c,r,t,f]) : w ∉ input ++ dirty :=
    fun hw' => hroles.2.2 w hw w hw' rfl
  have hnotHead (w : Wire) (hw : w ∈ input ++ dirty) : w ∉ [q,c,r,t,f] :=
    fun hw' => hroles.2.2 w hw' w hw rfl
  have hpd := List.nodup_append.mp hroles.2.1
  have hshort : (q :: c :: input ++ dirty).Nodup := by
    apply List.Nodup.sublist (l₂ := [q,c,r,t,f] ++ input ++ dirty) ?_ hnd
    exact (((by simp : [q,c].Sublist [q,c,r,t,f]).append (List.Sublist.refl _)).append (List.Sublist.refl _))
  have hqnot : q ∉ c :: r :: f :: dirty := by
    have hn := hnot q (by simp)
    have hh := hroles.1
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh
    simp only [List.mem_cons,List.mem_append,not_or] at hn ⊢
    tauto
  have hq : forward q = s q := gidneyCompareTrace_frame input dirty constant q c r f s q hqnot
  have hinput : wireValues input forward = wireValues input s := by
    apply List.map_congr_left
    intro w hw
    apply gidneyCompareTrace_frame
    have hn := hnotHead w (by simp [hw])
    have hdw : w ∉ dirty := fun hdw => hpd.2.2 w hw w hdw rfl
    simp only [List.mem_cons,List.not_mem_nil,not_or] at hn ⊢; tauto
  have hclean := gidneyCompareTrace_clean input dirty constant q c r t f s hk hd hnd hr
  have harith := gidneyCompareTrace_arithmetic input dirty constant q c r t f s hk hd hnd
  have hxor := controlledConstCarryXor_correct input dirty constant q c forward hk hd hshort hclean.1
  have hword : wireValues dirty (run (controlledConstCarryXor input dirty constant q c) forward) = wireValues dirty s := by
    rw [hxor.1,hinput,hq]
    rw [show wireValues dirty forward = _ from harith.1]
    rw [hc]
    apply gidneyXorWord_cancel
    rw [gidneyCarryBits_length (wireValues input s) (constant.map (fun k => s q && k)) false (by simp [wireValues,hk])]
    simp [wireValues,hd]
  have hf : forward f = Bool.xor (s f) (carryAddOverflow false (wireValues input s) (constant.map (fun k => s q && k))) := by
    cases input with
    | nil =>
      have he : constant = [] := List.eq_nil_of_length_eq_zero hk.symm
      subst constant
      simpa [forward,hc,carryAddOverflow,wireValues] using harith.2.2
    | cons a input => simpa only [List.isEmpty_cons,Bool.false_eq_true,↓reduceIte,hc] using harith.2.2
  funext w
  by_cases hwd : w ∈ dirty
  · have hn := hnotHead w (by simp [hwd])
    have hwf : w ≠ f := by intro h; apply hn; simp [h]
    have hv := List.map_inj_left.mp hword w hwd
    simpa [gidneyCompareIdealState,upd,hwf] using hv
  · rw [hxor.2 w hwd]
    by_cases hwf : w = f
    · subst w; simpa [gidneyCompareIdealState,upd] using hf
    by_cases hwc : w = c
    · subst w; simp [gidneyCompareIdealState,upd,hwf,hclean.1,hc,forward]
    by_cases hwr : w = r
    · subst w; simp [gidneyCompareIdealState,upd,hwf,hclean.2,hr,forward]
    have hframe := gidneyCompareTrace_frame input dirty constant q c r f s w (by simp [hwc,hwr,hwf,hwd])
    simpa [gidneyCompareIdealState,upd,hwf] using hframe

private theorem gidneyCompareCorrected_branch (a d q c r t f : Wire) (input dirty : List Wire)
    (k : Bool) (constant : List Bool) (s : BasisState)
    (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (hnd : ([q,c,r,t,f] ++ (a :: input) ++ d :: dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (Quantum.AdaptiveCircuit.unitary (gidneyCompareCarryCell q c r t a d f k input.isEmpty)
      (gidneyCompareTail q r c t f (fun outcomes => Quantum.registerZCorrection (d :: dirty) outcomes ++
        controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q c ++
        Quantum.registerZCorrection (d :: dirty) outcomes)
        (List.nil : List Bool) input dirty constant)).run) :
    branch.history.length = (d :: dirty).length ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude (d :: dirty).length •
        Quantum.ket (gidneyCompareIdealState (a :: input) (k :: constant) q f s) := by
  obtain ⟨outcomes,hist,hlen,hbranch⟩ := gidneyCompareRoot_branch a d q c r t f input dirty k constant s _
    hk hd hnd hc hr ht branch hb
  let forward := (gidneyCompareTrace q c r f (a :: input) (d :: dirty) (k :: constant) s).1
  let ideal := gidneyCompareIdealState (a :: input) (k :: constant) q f s
  let carries := (constantCarryBits false (wireValues (a :: input) s)
    ((k :: constant).map (fun k => s q && k)))
  have hbits : (wireValues (a :: input) s).length = ((k :: constant).map (fun k => s q && k)).length := by simp [wireValues,hk]
  have hcarrylen : carries.length = (d :: dirty).length := by
    rw [show carries = constantCarryBits false (wireValues (a :: input) s)
      ((k :: constant).map (fun k => s q && k)) from rfl,gidneyCarryBits_length _ _ false hbits]
    simp [wireValues,hd]
  have hclean := gidneyCompareCleanup (a :: input) (d :: dirty) (k :: constant) q c r t f s
    (by simpa using hk) (by simpa using hd) hnd hc hr
  change run (controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q c) forward = ideal at hclean
  have hp := List.nodup_append.mp hnd
  have hdirtyIdeal : wireValues (d :: dirty) ideal = wireValues (d :: dirty) s := by
    apply List.map_congr_left
    intro w hw
    have hwf : w ≠ f := by
      intro he; subst w
      exact hp.2.2 f (by simp) f hw rfl
    simp [ideal,gidneyCompareIdealState,upd,hwf]
  have htrace := gidneyCompareTrace_arithmetic (a :: input) (d :: dirty) (k :: constant) q c r t f s
    (by simpa using hk) (by simpa using hd) hnd
  have hxor : wireValues (d :: dirty) forward = List.zipWith Bool.xor (wireValues (d :: dirty) ideal) carries := by
    rw [hdirtyIdeal]
    simpa only [hc] using htrace.1
  have hphase := gidneyBorrowedPhaseCancellation (d :: dirty) outcomes carries forward ideal hcarrylen.symm hxor
  refine ⟨by rw [hist,hlen],?_⟩
  rw [hbranch]
  change gidneyRawCoefficient outcomes carries • Quantum.run
    ((Quantum.registerZCorrection (d :: dirty) outcomes ++
      controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q c) ++
      Quantum.registerZCorrection (d :: dirty) outcomes) (Quantum.ket forward) = _
  rw [Quantum.run_append,Quantum.run_append,Quantum.run_registerZCorrection_ket,map_smul,
    Quantum.run_ket_agrees_classical _ forward (gidneyCarryXor_HPFree _ _ _ q c (by simpa using hk) (by simpa using hd)),
    hclean,map_smul,Quantum.run_registerZCorrection_ket]
  rw [gidneyRawCoefficient_phase outcomes carries (hlen.trans hcarrylen.symm)]
  simp only [smul_smul]
  have hscalar : (Quantum.registerXResetMagnitude outcomes.length * gidneyRecordedPhase outcomes carries) *
      (Quantum.registerXPhase (d :: dirty) outcomes forward * Quantum.registerXPhase (d :: dirty) outcomes ideal) =
        Quantum.registerXResetMagnitude (d :: dirty).length := by
    rw [mul_assoc,← mul_assoc (gidneyRecordedPhase outcomes carries),hphase,mul_one,hlen]
  rw [hscalar]


/-- Every outcome implements the same carry predicate with an input-independent amplitude. -/
theorem controlledGidneyCompareCarry_branch_correct (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (s : BasisState) (hk : input.length = constant.length)
    (hd : input.length = dirty.length) (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (controlledGidneyCompareCarry input dirty constant q c r t f).run) :
    branch.history.length = input.length ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude input.length •
        Quantum.ket (gidneyCompareIdealState input constant q f s) := by
  cases input with
  | nil =>
    have he : constant = [] := List.eq_nil_of_length_eq_zero hk.symm
    subst constant
    have hh := gidneyDoneBranch branch hb
    have hi : gidneyCompareIdealState (List.nil : List Wire) (List.nil : List Bool) q f s = s := by
      funext w; by_cases hw : w = f <;> simp [gidneyCompareIdealState,carryAddOverflow,wireValues,upd,hw]
    rw [hh.1,hh.2,hi]
    simp [Quantum.registerXResetMagnitude]
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        have hh := gidneyCompareCorrected_branch a d q c r t f input dirty k constant s
          (by simpa using hk) (by simpa using hd) hnd hc hr ht branch hb
        simpa [← hd] using hh

private theorem gidneyCompareCell_wellFormed (q c r t a d f : Wire) (k last : Bool)
    (hnd : [q,c,r,t,a,d,f].Nodup) : CircuitWellFormed (gidneyCompareCarryCell q c r t a d f k last) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
  rcases hnd with ⟨⟨hqc,hqr,hqt,hqa,hqd,hqf⟩,⟨⟨hcr,hct,hca,hcd,hcf⟩,
    ⟨⟨hrt,hra,hrd,hrf⟩,⟨⟨hta,htd,htf⟩,⟨⟨had,haf⟩,hdf,_⟩⟩⟩⟩⟩
  cases k <;> cases last <;> simp_all [gidneyCompareCarryCell,CircuitWellFormed,Gate.WellFormed,Ne.symm]

private theorem gidneyCompareTail_wellFormed (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hcallback : ∀ outcomes, CircuitWellFormed (callback outcomes))
    (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup) :
    (gidneyCompareTail q c r t f callback history input dirty constant).WellFormed := by
  induction input generalizing dirty constant c r history with
  | nil =>
    have he : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have he' : constant = [] := List.eq_nil_of_length_eq_zero hk.symm
    subst dirty; subst constant
    exact ⟨⟨hcallback _,trivial⟩,hcallback _,trivial⟩
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        have hl := gidneyCompareLayoutStep q c r t f a d input dirty hnd
        exact ⟨gidneyCompareCell_wellFormed q c r t a d f k input.isEmpty hl.1,
          ih dirty constant r c _ (by simpa using hk) (by simpa using hd) hl.2,
          ih dirty constant r c _ (by simpa using hk) (by simpa using hd) hl.2⟩

/-- The concrete comparison instrument is well formed under the ordinary physical layout. -/
theorem controlledGidneyCompareCarry_wellFormed (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup) :
    (controlledGidneyCompareCarry input dirty constant q c r t f).WellFormed := by
  cases input with
  | nil => trivial
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        have hl := gidneyCompareLayoutStep q c r t f a d input dirty hnd
        have hshort : (q :: c :: (a :: input) ++ d :: dirty).Nodup := by
          apply List.Nodup.sublist (l₂ := [q,c,r,t,f] ++ (a :: input) ++ d :: dirty) ?_ hnd
          exact (((by simp : [q,c].Sublist [q,c,r,t,f]).append (List.Sublist.refl _)).append (List.Sublist.refl _))
        have hw := controlledConstCarryXor_wellFormed _ _ _ q c hk hd hshort
        refine ⟨gidneyCompareCell_wellFormed q c r t a d f k input.isEmpty hl.1,?_⟩
        apply gidneyCompareTail_wellFormed input dirty constant q r c t f _ _ ?_
          (by simpa using hk) (by simpa using hd) hl.2
        intro outcomes
        have hz := Quantum.registerZCorrection_wellFormed (d :: dirty) outcomes
        simpa only [CircuitWellFormed,List.forall_mem_append] using And.intro (And.intro hz hw) hz


private theorem gidneyCompareBits_value (n k : Nat) (hk : k < 2 ^ n) :
    boolWordToNat ((List.range n).map (Nat.testBit k)) = k := by
  induction n generalizing k with
  | zero =>
    have he : k = 0 := by simpa using hk
    subst k
    rfl
  | succ n ih =>
    have hhalf : k / 2 < 2 ^ n := by rw [Nat.pow_succ] at hk; omega
    rw [List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Function.comp_def,Nat.testBit_succ]
    rw [boolWordToNat,ih (k / 2) hhalf,Nat.testBit_zero]
    have hmod := Nat.mod_lt k (by omega : 0 < 2)
    by_cases h : k % 2 = 1 <;> simp [h] <;> omega

private theorem gidneyCompareConstant_value (constant : List Bool) (control : Bool) :
    boolWordToNat (constant.map (fun k => control && k)) = if control then boolWordToNat constant else 0 := by
  cases control with
  | true => simp
  | false =>
    simp only [Bool.false_and,↓reduceIte]
    induction constant with
    | nil => rfl
    | cons k ks ih => simpa only [List.map_cons,boolWordToNat,Bool.toNat_false,Nat.zero_add] using congrArg (2 * ·) ih

private theorem gidneyCompareOverflow (input constant : List Bool) (control : Bool) (threshold : Nat)
    (hlen : input.length = constant.length) (hk : 0 < threshold) (hbound : threshold < 2 ^ input.length)
    (hconstant : boolWordToNat constant = 2 ^ input.length - threshold) :
    carryAddOverflow false input (constant.map (fun k => control && k)) =
      (control && decide (threshold ≤ boolWordToNat input)) := by
  have hv := carryAddOverflow_value false input (constant.map (fun k => control && k)) (by simp [hlen])
  rw [gidneyCompareConstant_value,hconstant] at hv
  have hinput := boolWordToNat_lt_pow_two input
  cases hc : control with
  | false =>
    simp only [hc,Bool.false_eq_true,↓reduceIte,Bool.toNat_false,Nat.zero_add,Nat.add_zero] at hv
    rw [Nat.div_eq_of_lt hinput] at hv
    cases ho : carryAddOverflow false input (constant.map (fun k => false && k)) <;> simp_all
  | true =>
    simp only [hc,Bool.false_eq_true,↓reduceIte,Bool.toNat_false,Nat.zero_add] at hv
    by_cases h : threshold ≤ boolWordToNat input
    · have hdiv : (boolWordToNat input + (2 ^ input.length - threshold)) / 2 ^ input.length = 1 := by
        apply Nat.div_eq_of_lt_le <;> omega
      rw [hdiv] at hv
      cases ho : carryAddOverflow false input (constant.map (fun k => true && k)) <;> simp_all
    · have hdiv : (boolWordToNat input + (2 ^ input.length - threshold)) / 2 ^ input.length = 0 :=
        Nat.div_eq_of_lt (by omega)
      rw [hdiv] at hv
      cases ho : carryAddOverflow false input (constant.map (fun k => true && k)) <;> simp_all


/-- The source threshold wrapper toggles exactly `control && (threshold ≤ input)`.
Every measurement branch has the same coefficient, and every other wire is unchanged. -/
theorem controlledGidneyCompareGE_branch_correct (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (s : BasisState) (hd : input.length = dirty.length)
    (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (controlledGidneyCompareGE input dirty threshold q c r t f).run) :
    let m := if threshold = 0 ∨ 2 ^ input.length ≤ threshold then 0 else input.length
    branch.history.length = m ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude m •
        Quantum.ket (upd s f (Bool.xor (s f) (s q && decide (threshold ≤ boolWordToNat (wireValues input s))))) := by
  dsimp only
  by_cases hz : threshold = 0
  · subst threshold
    simp only [controlledGidneyCompareGE,if_pos rfl] at hb
    obtain ⟨last,hl,hhist,hsem⟩ := gidneyUnitaryBranch _ _ branch hb
    have hh := gidneyDoneBranch last hl
    rw [hhist,hh.1,hsem,hh.2,Quantum.run_ket_agrees_classical _ s (by simp)]
    simp [Quantum.registerXResetMagnitude,run,applyGate,Bool.xor_comm]
  · by_cases hlarge : 2 ^ input.length ≤ threshold
    · simp only [controlledGidneyCompareGE,if_neg hz,if_pos hlarge] at hb
      have hh := gidneyDoneBranch branch hb
      have hfalse : ¬ threshold ≤ boolWordToNat (wireValues input s) := by
        have hinput := boolWordToNat_lt_pow_two (wireValues input s)
        have hinput' : boolWordToNat (wireValues input s) < 2 ^ input.length := by
          simpa only [wireValues,List.length_map] using hinput
        omega
      have hi : upd s f (Bool.xor (s f) (s q && decide (threshold ≤ boolWordToNat (wireValues input s)))) = s := by
        funext w; by_cases hw : w = f <;> simp [upd,hfalse,hw]
      rw [hh.1,hh.2,hi]
      simp [hlarge,Quantum.registerXResetMagnitude]
    · have hlt : threshold < 2 ^ input.length := by omega
      let constant := (List.range input.length).map (Nat.testBit (2 ^ input.length - threshold))
      have hk : input.length = constant.length := by simp [constant]
      have hv : boolWordToNat constant = 2 ^ input.length - threshold :=
        gidneyCompareBits_value _ _ (by omega)
      have hi : gidneyCompareIdealState input constant q f s =
          upd s f (Bool.xor (s f) (s q && decide (threshold ≤ boolWordToNat (wireValues input s)))) := by
        unfold gidneyCompareIdealState
        rw [gidneyCompareOverflow (wireValues input s) constant (s q) threshold
          (by simp [wireValues,hk]) (by omega) (by simpa [wireValues] using hlt) (by simpa [wireValues] using hv)]
      have hh := controlledGidneyCompareCarry_branch_correct input dirty constant q c r t f s hk hd hnd hc hr ht branch
        (by simpa only [controlledGidneyCompareGE,if_neg hz,if_neg hlarge] using hb)
      rw [hi] at hh
      simpa [hz,hlarge] using hh

/-- Threshold shortcuts and the measured comparison core are all well formed. -/
theorem controlledGidneyCompareGE_wellFormed (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (hd : input.length = dirty.length)
    (hnd : ([q,c,r,t,f] ++ input ++ dirty).Nodup) :
    (controlledGidneyCompareGE input dirty threshold q c r t f).WellFormed := by
  by_cases hz : threshold = 0
  · have hqf : q ≠ f := by intro h; subst q; simp at hnd
    simp [controlledGidneyCompareGE,hz,Quantum.AdaptiveCircuit.WellFormed,CircuitWellFormed,Gate.WellFormed,hqf]
  by_cases hh : 2 ^ input.length ≤ threshold
  · simp [controlledGidneyCompareGE,hz,hh,Quantum.AdaptiveCircuit.WellFormed]
  simp only [controlledGidneyCompareGE,if_neg hz,if_neg hh]
  exact controlledGidneyCompareCarry_wellFormed _ _ _ q c r t f (by simp) hd hnd


private def gidneyCompareForwardCost (cell : Bool → Bool → Nat) : List Bool → Nat
  | [] => 0
  | k :: constant => cell k constant.isEmpty + gidneyCompareForwardCost cell constant

private theorem gidneyCompareTail_counts (cost : Gate → Nat) (cell : Bool → Bool → Nat)
    (hcell : ∀ q c r t a d f k last, ((gidneyCompareCarryCell q c r t a d f k last).map cost).sum = cell k last)
    (input dirty : List Wire) (constant : List Bool) (q c r t f : Wire)
    (callback : List Bool → Circuit) (history : List Bool) (budget : Nat)
    (hcallback : ∀ outcomes, ((callback outcomes).map cost).sum = budget)
    (hk : input.length = constant.length) (hd : input.length = dirty.length) :
    gidneyGateCount cost (gidneyCompareTail q c r t f callback history input dirty constant) =
      gidneyCompareForwardCost cell constant + budget ∧
    (gidneyCompareTail q c r t f callback history input dirty constant).measurementCount = input.length + 1 := by
  induction input generalizing dirty constant c r history with
  | nil =>
    have he : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have he' : constant = [] := List.eq_nil_of_length_eq_zero hk.symm
    subst dirty; subst constant
    simp [gidneyCompareTail,gidneyGateCount,gidneyCompareForwardCost,Quantum.AdaptiveCircuit.measurementCount,hcallback]
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        have hf := ih dirty constant r c (history ++ [false]) (by simpa using hk) (by simpa using hd)
        have ht := ih dirty constant r c (history ++ [true]) (by simpa using hk) (by simpa using hd)
        have he : input.isEmpty = constant.isEmpty := by
          cases input <;> cases constant <;> simp_all only [List.length_cons,List.length_nil,List.isEmpty_cons,List.isEmpty_nil] <;> omega
        simp only [gidneyCompareTail,gidneyGateCount,Quantum.AdaptiveCircuit.measurementCount,hcell,
          hf.1,ht.1,hf.2,ht.2,max_self,gidneyCompareForwardCost,he]
        simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem gidneyCompareRoot_counts (cost : Gate → Nat) (cell : Bool → Bool → Nat)
    (hX : ∀ w, cost (.X w) = 0) (hH : ∀ w, cost (.H w) = 0)
    (hcell : ∀ q c r t a d f k last, ((gidneyCompareCarryCell q c r t a d f k last).map cost).sum = cell k last)
    (a d q c r t f : Wire) (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length) :
    gidneyGateCount cost (controlledGidneyCompareCarry (a :: input) (d :: dirty) (k :: constant) q c r t f) =
      gidneyCompareForwardCost cell (k :: constant) +
        ((controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q c).map cost).sum ∧
    (controlledGidneyCompareCarry (a :: input) (d :: dirty) (k :: constant) q c r t f).measurementCount = input.length + 1 := by
  have hh := gidneyCompareTail_counts cost cell hcell input dirty constant q r c t f
    (fun outcomes => Quantum.registerZCorrection (d :: dirty) outcomes ++
      controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q c ++
      Quantum.registerZCorrection (d :: dirty) outcomes) (List.nil : List Bool)
    (((controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q c).map cost).sum)
    (by intro outcomes; simp [List.map_append,List.sum_append,gidneyZ_cost cost hX hH]) hk hd
  have he : input.isEmpty = constant.isEmpty := by cases input <;> cases constant <;> simp_all only [List.length_cons,List.length_nil,List.isEmpty_cons,List.isEmpty_nil] <;> omega
  simp only [controlledGidneyCompareCarry,gidneyGateCount,Quantum.AdaptiveCircuit.measurementCount,
    hcell,hh.1,hh.2,gidneyCompareForwardCost,he]
  simp [Nat.add_assoc]


private theorem gidneyCompareCell_wires (q c r t a d f w : Wire) (k last : Bool) :
    w ∈ circuitWires (gidneyCompareCarryCell q c r t a d f k last) → w ∈ [q,c,r,t,a,d,f] := by
  cases k <;> cases last <;> simp [gidneyCompareCarryCell,circuitWires,gateWires] <;> tauto

private theorem gidneyCompareTail_usesOnly (allowed input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hroles : ∀ w ∈ [q,c,r,t,f] ++ input ++ dirty, w ∈ allowed)
    (hcallback : ∀ outcomes w, w ∈ circuitWires (callback outcomes) → w ∈ allowed) :
    ∀ w ∈ (gidneyCompareTail q c r t f callback history input dirty constant).wires, w ∈ allowed := by
  induction input generalizing dirty constant c r history with
  | nil =>
    cases dirty with
    | cons d ds => simp [gidneyCompareTail,Quantum.AdaptiveCircuit.wires]
    | nil =>
      cases constant with
      | cons k ks => simp [gidneyCompareTail,Quantum.AdaptiveCircuit.wires]
      | nil =>
        intro w hw
        simp only [gidneyCompareTail,Quantum.AdaptiveCircuit.wires,List.append_nil,List.mem_cons,List.mem_append] at hw
        rcases hw with h | h | h
        · subst w; exact hroles c (by simp)
        · exact hcallback _ w h
        · exact hcallback _ w h
  | cons a input ih =>
    cases dirty with
    | nil => simp [gidneyCompareTail,Quantum.AdaptiveCircuit.wires]
    | cons d dirty =>
      cases constant with
      | nil => simp [gidneyCompareTail,Quantum.AdaptiveCircuit.wires]
      | cons k constant =>
        have ht : ∀ w ∈ [q,r,c,t,f] ++ input ++ dirty, w ∈ allowed := by
          intro w hw; apply hroles w
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢; tauto
        intro w hw
        simp only [gidneyCompareTail,Quantum.AdaptiveCircuit.wires,List.mem_append,List.mem_cons] at hw
        rcases hw with h | h | h | h
        · apply hroles w
          have hm := gidneyCompareCell_wires q c r t a d f w k input.isEmpty h
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hm ⊢; tauto
        · subst w; exact hroles c (by simp)
        · exact ih dirty constant r c _ ht w h
        · exact ih dirty constant r c _ ht w h

private theorem gidneyCompareTail_covers (input dirty : List Wire) (constant : List Bool)
    (q c r t f : Wire) (callback : List Bool → Circuit) (history : List Bool)
    (hk : input.length = constant.length) (hd : input.length = dirty.length) (hne : input ≠ []) :
    ∀ w ∈ input ++ dirty ++ [f], w ∈ (gidneyCompareTail q c r t f callback history input dirty constant).wires := by
  induction input generalizing dirty constant c r history with
  | nil => contradiction
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        intro w hw
        have hcell : w ∈ [a,d] ∨ (w = f ∧ input = []) →
            w ∈ circuitWires (gidneyCompareCarryCell q c r t a d f k input.isEmpty) := by
          intro h
          cases input <;> cases k <;> simp_all [gidneyCompareCarryCell,circuitWires,gateWires] <;> tauto
        simp only [gidneyCompareTail,Quantum.AdaptiveCircuit.wires,List.mem_append,List.mem_cons]
        by_cases h : w ∈ [a,d] ∨ (w = f ∧ input = [])
        · exact Or.inl (hcell h)
        · apply Or.inr; apply Or.inr; apply Or.inl
          have hi : input ≠ [] := by
            intro he; subst input
            have he' : dirty = [] := List.eq_nil_of_length_eq_zero (by simpa using hd.symm)
            subst dirty
            simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false] at hw h
            tauto
          apply ih dirty constant r c _ (by simpa using hk) (by simpa using hd) hi w
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hw h ⊢; tauto

private theorem gidneyCompareCell_covers (q c r t a d f w : Wire) (last : Bool) :
    w ∈ circuitWires (gidneyCompareCarryCell q c r t a d f true last) ↔
      w ∈ [q,c,r,t,a,d] ∨ (last = true ∧ w = f) := by
  cases last <;> simp [gidneyCompareCarryCell,circuitWires,gateWires] <;> tauto

private theorem gidneyCompareRoot_wires (a d q c r t f : Wire) (input dirty : List Wire)
    (constant : List Bool) (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (w : Wire) :
    w ∈ (controlledGidneyCompareCarry (a :: input) (d :: dirty) (true :: constant) q c r t f).wires ↔
      w ∈ [q,c,r,t,f] ++ (a :: input) ++ d :: dirty := by
  let allowed := [q,c,r,t,f] ++ (a :: input) ++ d :: dirty
  let callback := fun outcomes => Quantum.registerZCorrection (d :: dirty) outcomes ++
    controlledConstCarryXor (a :: input) (d :: dirty) (true :: constant) q c ++
    Quantum.registerZCorrection (d :: dirty) outcomes
  have hcallback : ∀ outcomes x, x ∈ circuitWires (callback outcomes) → x ∈ allowed := by
    intro outcomes x hx
    have hz := gidneyZ_usesOnly (d :: dirty) outcomes x
    have hc : x ∈ circuitWires (controlledConstCarryXor (a :: input) (d :: dirty) (true :: constant) q c) →
        x ∈ q :: c :: (a :: input) ++ d :: dirty := by
      intro h; obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp h
      exact controlledConstCarryXor_usesOnly _ _ _ q c g hg x hw
    simp only [callback,circuitWires,List.flatMap_append,List.mem_append] at hx
    change (x ∈ circuitWires (Quantum.registerZCorrection (d :: dirty) outcomes) ∨
      x ∈ circuitWires (controlledConstCarryXor (a :: input) (d :: dirty) (true :: constant) q c)) ∨
      x ∈ circuitWires (Quantum.registerZCorrection (d :: dirty) outcomes) at hx
    have : x ∈ (d :: dirty) ∨ x ∈ q :: c :: (a :: input) ++ d :: dirty := by tauto
    simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at this ⊢; tauto
  have hroles : ∀ x ∈ [q,r,c,t,f] ++ input ++ dirty, x ∈ allowed := by
    intro x hx; simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at hx ⊢; tauto
  have ht := gidneyCompareTail_usesOnly allowed input dirty constant q r c t f callback (List.nil : List Bool) hroles hcallback w
  simp only [controlledGidneyCompareCarry,Quantum.AdaptiveCircuit.wires]
  rw [List.mem_append]
  change (w ∈ circuitWires (gidneyCompareCarryCell q c r t a d f true input.isEmpty) ∨
    w ∈ (gidneyCompareTail q r c t f callback (List.nil : List Bool) input dirty constant).wires) ↔ w ∈ allowed
  constructor
  · intro h
    rcases h with h | h
    · have hh := gidneyCompareCell_wires q c r t a d f w true input.isEmpty h
      simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at hh ⊢; tauto
    · exact ht h
  · intro h
    by_cases hcell : w ∈ [q,c,r,t,a,d] ∨ (w = f ∧ input = [])
    · apply Or.inl
      apply (gidneyCompareCell_covers q c r t a d f w input.isEmpty).2
      rcases hcell with hm | ⟨hf,he⟩
      · exact Or.inl hm
      · exact Or.inr ⟨by rw [he]; rfl,hf⟩
    · apply Or.inr
      have hi : input ≠ [] := by
        intro he; subst input
        have he' : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
        subst dirty
        simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false] at h hcell
        tauto
      apply gidneyCompareTail_covers input dirty constant q r c t f callback _ hk hd hi w
      simp only [allowed,List.mem_append,List.mem_cons,List.not_mem_nil] at h hcell ⊢; tauto

/-- Exact wire count for the low-bit-one comparison core used by the production threshold. -/
theorem controlledGidneyCompareCarry_qubitCount (a d q c r t f : Wire) (input dirty : List Wire)
    (constant : List Bool) (hk : input.length = constant.length) (hd : input.length = dirty.length)
    (hnd : ([q,c,r,t,f] ++ (a :: input) ++ d :: dirty).Nodup) :
    (controlledGidneyCompareCarry (a :: input) (d :: dirty) (true :: constant) q c r t f).qubitCount =
      2 * (input.length + 1) + 5 := by
  have heq : (controlledGidneyCompareCarry (a :: input) (d :: dirty) (true :: constant) q c r t f).wires.dedup.toFinset =
      ([q,c,r,t,f] ++ (a :: input) ++ d :: dirty).toFinset := by
    ext w; simpa [or_assoc,or_left_comm,or_comm] using gidneyCompareRoot_wires a d q c r t f input dirty constant hk hd w
  have hc := congrArg Finset.card heq
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_card_of_nodup hnd] at hc
  simp only [List.length_append,List.length_cons,List.length_nil] at hc
  unfold Quantum.AdaptiveCircuit.qubitCount
  omega


/-- Production comparison against the secp256k1 modulus, with an arbitrary result flag. -/
def secp256k1GidneyCompare : Quantum.AdaptiveCircuit :=
  controlledGidneyCompareGE (List.range' 5 256) (List.range' 261 256)
    (2 ^ 256 - (2 ^ 32 + 977)) 0 1 2 3 4

set_option maxRecDepth 10000 in
private theorem gidneyCompareProduction_core : secp256k1GidneyCompare =
    controlledGidneyCompareCarry (List.range' 5 256) (List.range' 261 256)
      secp256k1ReductionConstantBits 0 1 2 3 4 := by
  unfold secp256k1GidneyCompare controlledGidneyCompareGE
  rw [if_neg (by decide)]
  simp only [List.length_range']
  rw [if_neg (by decide),Nat.sub_sub_self (by decide : 2 ^ 32 + 977 ≤ 2 ^ 256)]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyCompareProduction_layout :
    ([0,1,2,3,4] ++ List.range' 5 256 ++ List.range' 261 256).Nodup := by decide

set_option maxRecDepth 100000 in
private theorem gidneyCompareProduction_cleanup_counts :
    let gates := controlledConstCarryXor (List.range' 5 256) (List.range' 261 256) secp256k1ReductionConstantBits 0 1
    eeaToffoliCount gates = 511 ∧ eeaCnotCount gates = 47 ∧ tCount gates = 3577 := by
  have h := controlledConstCarryXor_counts 5 (List.range' 6 255) (List.range' 261 256) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) 0 1 (by simp) (by simp)
  have hw : constantBitWeight ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) = 6 := by decide
  dsimp only
  change eeaToffoliCount (controlledConstCarryXor (5 :: List.range' 6 255) _
    (true :: (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) 0 1) = 511 ∧ _
  simpa [hw] using And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyCompareProduction_toffoli : gidneyToffoliCount secp256k1GidneyCompare = 767 ∧
    secp256k1GidneyCompare.measurementCount = 256 := by
  have h := gidneyCompareRoot_counts (fun g => match g with | .CCX _ _ _ => 1 | _ => 0) (fun _ _ => 1)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d f k last; cases k <;> cases last <;> simp [gidneyCompareCarryCell,tCost])
    5 261 0 1 2 3 4 (List.range' 6 255) (List.range' 262 255) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) (by simp) (by simp)
  have hb : gidneyCompareForwardCost (fun _ _ => 1)
    (true :: (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) = 256 := by decide
  have hc := gidneyCompareProduction_cleanup_counts.1
  rw [
    show List.range' 5 256 = 5 :: List.range' 6 255 from rfl,
    show List.range' 261 256 = 261 :: List.range' 262 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl] at hc
  rw [gidneyCompareProduction_core,
    show List.range' 5 256 = 5 :: List.range' 6 255 from rfl,
    show List.range' 261 256 = 261 :: List.range' 262 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  constructor
  · unfold gidneyToffoliCount
    apply h.1.trans
    rw [hb]
    change 256 + eeaToffoliCount _ = 767
    rw [hc]
  · exact h.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyCompareProduction_cnot : gidneyCnotCount secp256k1GidneyCompare = 1598 ∧
    secp256k1GidneyCompare.measurementCount = 256 := by
  have h := gidneyCompareRoot_counts (fun g => match g with | .CX _ _ => 1 | _ => 0) (fun k last => 6 + 2 * k.toNat + last.toNat)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d f k last; cases k <;> cases last <;> simp [gidneyCompareCarryCell,tCost])
    5 261 0 1 2 3 4 (List.range' 6 255) (List.range' 262 255) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) (by simp) (by simp)
  have hb : gidneyCompareForwardCost (fun k last => 6 + 2 * k.toNat + last.toNat)
    (true :: (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) = 1551 := by decide
  have hc := gidneyCompareProduction_cleanup_counts.2.1
  rw [
    show List.range' 5 256 = 5 :: List.range' 6 255 from rfl,
    show List.range' 261 256 = 261 :: List.range' 262 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl] at hc
  rw [gidneyCompareProduction_core,
    show List.range' 5 256 = 5 :: List.range' 6 255 from rfl,
    show List.range' 261 256 = 261 :: List.range' 262 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  constructor
  · unfold gidneyCnotCount
    apply h.1.trans
    rw [hb]
    change 1551 + eeaCnotCount _ = 1598
    rw [hc]
  · exact h.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem gidneyCompareProduction_t : secp256k1GidneyCompare.tCount = 5369 ∧
    secp256k1GidneyCompare.measurementCount = 256 := by
  have h := gidneyCompareRoot_counts tCost (fun _ _ => 7)
    (by intro w; rfl) (by intro w; rfl)
    (by intro q c r t a d f k last; cases k <;> cases last <;> simp [gidneyCompareCarryCell,tCost])
    5 261 0 1 2 3 4 (List.range' 6 255) (List.range' 262 255) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) (by simp) (by simp)
  have hb : gidneyCompareForwardCost (fun _ _ => 7)
    (true :: (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) = 1792 := by decide
  have hc := gidneyCompareProduction_cleanup_counts.2.2
  rw [
    show List.range' 5 256 = 5 :: List.range' 6 255 from rfl,
    show List.range' 261 256 = 261 :: List.range' 262 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl] at hc
  rw [gidneyCompareProduction_core,
    show List.range' 5 256 = 5 :: List.range' 6 255 from rfl,
    show List.range' 261 256 = 261 :: List.range' 262 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  constructor
  · rw [← gidneyGateCount_tCount]
    apply h.1.trans
    rw [hb]
    change 1792 + tCount _ = 5369
    rw [hc]
  · exact h.2

set_option maxRecDepth 100000 in
private theorem gidneyCompareProduction_qubits : secp256k1GidneyCompare.qubitCount = 517 := by
  rw [gidneyCompareProduction_core,
    show List.range' 5 256 = 5 :: List.range' 6 255 from rfl,
    show List.range' 261 256 = 261 :: List.range' 262 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  exact controlledGidneyCompareCarry_qubitCount 5 261 0 1 2 3 4 _ _ _
    (by simp) (by simp) gidneyCompareProduction_layout


set_option maxRecDepth 100000 in
/-- Readable same-circuit certificate for comparison with the secp256k1 modulus.
The arbitrary result flag is XORed with the controlled predicate; every other wire is
restored in every branch, and total probability is one. The concrete source circuit
uses 767 CCX, 1,598 CX, 5,369 T, 256 measurement/resets and exactly 517 physical wires. -/
theorem secp256k1GidneyCompare_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) :
    (∀ branch ∈ secp256k1GidneyCompare.run,
      branch.history.length = 256 ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude 256 •
        Quantum.ket (upd s 4 (Bool.xor (s 4) (s 0 && decide
          (2 ^ 256 - (2 ^ 32 + 977) ≤ boolWordToNat (wireValues (List.range' 5 256) s)))))) ∧
    Quantum.Instrument.bornMass secp256k1GidneyCompare.run (Quantum.ket s) = 1 ∧
    secp256k1GidneyCompare.WellFormed ∧
    gidneyToffoliCount secp256k1GidneyCompare = 767 ∧
    gidneyCnotCount secp256k1GidneyCompare = 1598 ∧
    secp256k1GidneyCompare.tCount = 5369 ∧
    secp256k1GidneyCompare.measurementCount = 256 ∧ secp256k1GidneyCompare.qubitCount = 517 := by
  have hd : (List.range' 5 256).length = (List.range' 261 256).length := by simp
  have hw := controlledGidneyCompareGE_wellFormed _ _ (2 ^ 256 - (2 ^ 32 + 977)) 0 1 2 3 4 hd gidneyCompareProduction_layout
  have hsmall : ¬ (2 ^ 256 - (2 ^ 32 + 977) = 0 ∨ 2 ^ 256 ≤ 2 ^ 256 - (2 ^ 32 + 977)) := by decide
  refine ⟨?_,?_,hw,gidneyCompareProduction_toffoli.1,gidneyCompareProduction_cnot.1,
    gidneyCompareProduction_t.1,gidneyCompareProduction_t.2,gidneyCompareProduction_qubits⟩
  · intro branch hb
    have hh := controlledGidneyCompareGE_branch_correct _ _ (2 ^ 256 - (2 ^ 32 + 977)) 0 1 2 3 4 s hd
      gidneyCompareProduction_layout hc hr ht branch hb
    simpa only [List.length_range',if_neg hsmall] using hh
  · exact Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket s)

end ShorECDLP.Paper2607_13816
