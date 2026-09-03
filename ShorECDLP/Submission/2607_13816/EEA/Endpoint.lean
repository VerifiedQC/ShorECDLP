import ShorECDLP.Submission.«2607_13816».EEA.Affine

/-!
# Source affine endpoint transforms

The fast-dual remainder block temporarily converts the stored length words into the two absolute
interval endpoints

`L = (ell_t - 1) + (ell_q - 1) + 4 - k` and
`R = n + 2 - (ell_s - 1) - k`.

This file implements the pinned generator's literal gate order.  One physical scratch bank is
shared by the differently sized endpoint words; each arithmetic call takes the corresponding
prefix and restores it.  The direct theorem states the complete word action, scratch cleanup, and
outside-wire preservation.  The later interval aggregate will place its unary traversal between
this preparation and the source restoration stream.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

set_option linter.unusedSimpArgs false

/-- The prefix of the common endpoint scratch bank used by one word. -/
def endpointScratch (register scratch : List Wire) : List Wire :=
  scratch.take register.length

/-- One global physical layout permits the two endpoint calls to reuse the same scratch prefix. -/
def IntervalEndpointLayout
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire) : Prop :=
  (carry :: (scratch ++ (lengthT ++ (lengthQ ++ lengthS)))).Nodup

private theorem endpointScratch_length
    (register scratch : List Wire) (hwidth : register.length ≤ scratch.length) :
    (endpointScratch register scratch).length = register.length := by
  simp [endpointScratch, List.length_take, Nat.min_eq_left hwidth]

private theorem endpoint_q_sublist
    (lengthT lengthQ lengthS : List Wire) :
    lengthQ.Sublist (lengthT ++ (lengthQ ++ lengthS)) := by
  exact (List.sublist_append_left lengthQ lengthS).trans
    (List.sublist_append_right lengthT (lengthQ ++ lengthS))

private theorem endpoint_s_sublist
    (lengthT lengthQ lengthS : List Wire) :
    lengthS.Sublist (lengthT ++ (lengthQ ++ lengthS)) := by
  exact (List.sublist_append_right lengthQ lengthS).trans
    (List.sublist_append_right lengthT (lengthQ ++ lengthS))

private theorem endpoint_tq_sublist
    (lengthT lengthQ lengthS : List Wire) :
    (lengthT ++ lengthQ).Sublist (lengthT ++ (lengthQ ++ lengthS)) := by
  exact (List.sublist_append_left lengthQ lengthS).append_left lengthT

private theorem endpoint_constant_layout_q
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    ConstantLayout lengthQ (endpointScratch lengthQ scratch) carry := by
  apply List.Sublist.nodup
    (l₂ := carry :: (scratch ++ (lengthT ++ (lengthQ ++ lengthS))))
  · exact ((List.take_sublist lengthQ.length scratch).append
      (endpoint_q_sublist lengthT lengthQ lengthS)).cons₂ carry
  · exact hlayout

private theorem endpoint_constant_layout_s
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    ConstantLayout lengthS (endpointScratch lengthS scratch) carry := by
  apply List.Sublist.nodup
    (l₂ := carry :: (scratch ++ (lengthT ++ (lengthQ ++ lengthS))))
  · exact ((List.take_sublist lengthS.length scratch).append
      (endpoint_s_sublist lengthT lengthQ lengthS)).cons₂ carry
  · exact hlayout

private theorem endpoint_cuccaro_layout
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    (carry :: lengthT ++ lengthQ).Nodup := by
  apply List.Sublist.nodup
    (l₂ := carry :: (scratch ++ (lengthT ++ (lengthQ ++ lengthS))))
  · exact ((endpoint_tq_sublist lengthT lengthQ lengthS).trans
      (List.sublist_append_right scratch
        (lengthT ++ (lengthQ ++ lengthS)))).cons₂ carry
  · exact hlayout

private theorem endpoint_q_not_mem_s
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    ∀ wire ∈ lengthQ, wire ∉ lengthS := by
  have hregs : (lengthT ++ (lengthQ ++ lengthS)).Nodup :=
    (List.sublist_append_right scratch
      (lengthT ++ (lengthQ ++ lengthS))).nodup
        (List.nodup_cons.mp hlayout).2
  have hqs : (lengthQ ++ lengthS).Nodup :=
    (List.sublist_append_right lengthT (lengthQ ++ lengthS)).nodup hregs
  intro wire hq hs
  exact (List.nodup_append.mp hqs).2.2 wire hq wire hs rfl

private theorem endpoint_t_not_mem_q
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    ∀ wire ∈ lengthT, wire ∉ lengthQ := by
  have htq := endpoint_cuccaro_layout lengthT lengthQ lengthS scratch carry hlayout
  intro wire ht hq
  exact (List.nodup_append.mp (List.nodup_cons.mp htq).2).2.2
    wire ht wire hq rfl

private theorem endpoint_t_not_mem_s
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    ∀ wire ∈ lengthT, wire ∉ lengthS := by
  have hregs : (lengthT ++ (lengthQ ++ lengthS)).Nodup :=
    (List.sublist_append_right scratch
      (lengthT ++ (lengthQ ++ lengthS))).nodup
        (List.nodup_cons.mp hlayout).2
  obtain ⟨ht, hqs, hcross⟩ := List.nodup_append.mp hregs
  intro wire hwire hmem
  exact hcross wire hwire wire (by simp [hmem]) rfl

private theorem endpoint_s_not_mem_q
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    ∀ wire ∈ lengthS, wire ∉ lengthQ := by
  intro wire hs hq
  exact endpoint_q_not_mem_s lengthT lengthQ lengthS scratch carry hlayout
    wire hq hs

private theorem endpoint_work_not_mem_q
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    ∀ wire ∈ scratch ++ [carry], wire ∉ lengthQ := by
  have hcarryBody := List.nodup_cons.mp hlayout
  have hbody := List.nodup_append.mp hcarryBody.2
  intro wire hwire hq
  rcases List.mem_append.mp hwire with hscratch | hcarry
  · exact hbody.2.2 wire hscratch wire (by simp [hq]) rfl
  · simp only [List.mem_singleton] at hcarry
    subst wire
    exact hcarryBody.1 (by simp [hq])

private theorem endpoint_work_not_mem_s
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    ∀ wire ∈ scratch ++ [carry], wire ∉ lengthS := by
  have hcarryBody := List.nodup_cons.mp hlayout
  have hbody := List.nodup_append.mp hcarryBody.2
  intro wire hwire hs
  rcases List.mem_append.mp hwire with hscratch | hcarry
  · exact hbody.2.2 wire hscratch wire (by simp [hs]) rfl
  · simp only [List.mem_singleton] at hcarry
    subst wire
    exact hcarryBody.1 (by simp [hs])

private theorem endpoint_wireValues_congr
    (wires : List Wire) (left right : BasisState)
    (h : ∀ wire ∈ wires, left wire = right wire) :
    wireValues wires left = wireValues wires right := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨h wire (by simp), ih (fun next hnext ↦
        h next (by simp [hnext]))⟩

/-- Gate-independent left endpoint word. -/
def intervalLeftBits
    (lengthT lengthQ : List Bool) (offset : Nat) : List Bool :=
  cuccaroSubBits false (constantBits lengthQ.length offset)
    (cuccaroAddBits false (constantBits lengthQ.length 4)
      (cuccaroAddBits false lengthT lengthQ))

/-- Gate-independent right endpoint word. -/
def intervalRightBits
    (lengthS : List Bool) (modulusBits offset : Nat) : List Bool :=
  cuccaroSubBits false (constantBits lengthS.length offset)
    (constMinusBits lengthS (modulusBits + 2))

/-- Gate-independent word action of the source restoration stream on the left endpoint. -/
def restoredIntervalLeftBits
    (lengthT lengthQ : List Bool) (offset : Nat) : List Bool :=
  cuccaroSubBits false lengthT
    (cuccaroSubBits false (constantBits lengthQ.length 4)
      (cuccaroAddBits false (constantBits lengthQ.length offset) lengthQ))

/-- Gate-independent word action of the source restoration stream on the right endpoint. -/
def restoredIntervalRightBits
    (lengthS : List Bool) (modulusBits offset : Nat) : List Bool :=
  constMinusBits
    (cuccaroAddBits false (constantBits lengthS.length offset) lengthS)
    (modulusBits + 2)

/-- Literal preparation stream from `lc_interval_addsub_unary_gate`. -/
def prepareIntervalEndpoints
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat) : Circuit :=
  cuccaroAdd lengthT lengthQ carry ++
    addConstant lengthQ (endpointScratch lengthQ scratch) carry 4 ++
    constMinus lengthS (endpointScratch lengthS scratch) carry (modulusBits + 2) ++
    subConstant lengthQ (endpointScratch lengthQ scratch) carry offset ++
    subConstant lengthS (endpointScratch lengthS scratch) carry offset

/-- Literal restoration stream emitted after the interval scans.  This is intentionally the
source program, including a second forward `constMinus` rather than a fictional circuit dagger. -/
def restoreIntervalEndpoints
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat) : Circuit :=
  addConstant lengthS (endpointScratch lengthS scratch) carry offset ++
    addConstant lengthQ (endpointScratch lengthQ scratch) carry offset ++
    constMinus lengthS (endpointScratch lengthS scratch) carry (modulusBits + 2) ++
    subConstant lengthQ (endpointScratch lengthQ scratch) carry 4 ++
    cuccaroSub lengthT lengthQ carry

/-- Named physical support of either endpoint transform. -/
def intervalEndpointSupport
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire) : List Wire :=
  scratch ++ [carry] ++ lengthT ++ lengthQ ++ lengthS

private theorem endpoint_cuccaro_mem_support
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire) :
    ∀ wire, wire ∈ carry :: lengthT ++ lengthQ →
      wire ∈ intervalEndpointSupport lengthT lengthQ lengthS scratch carry := by
  intro wire hwire
  simp only [List.mem_cons, List.mem_append] at hwire
  rcases hwire with (rfl | ht) | hq
  · simp [intervalEndpointSupport]
  · simp [intervalEndpointSupport, ht]
  · simp [intervalEndpointSupport, hq]

private theorem endpoint_q_constant_mem_support
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire) :
    ∀ wire, wire ∈ endpointScratch lengthQ scratch ++ lengthQ ++ [carry] →
      wire ∈ intervalEndpointSupport lengthT lengthQ lengthS scratch carry := by
  intro wire hwire
  simp only [List.mem_append, List.mem_singleton] at hwire
  rcases hwire with hwire | hcarry
  · rcases hwire with hscratch | hq
    · exact by
        have := List.mem_of_mem_take hscratch
        simp [intervalEndpointSupport, this]
    · simp [intervalEndpointSupport, hq]
  · simp [intervalEndpointSupport, hcarry]

private theorem endpoint_s_constant_mem_support
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire) :
    ∀ wire, wire ∈ endpointScratch lengthS scratch ++ lengthS ++ [carry] →
      wire ∈ intervalEndpointSupport lengthT lengthQ lengthS scratch carry := by
  intro wire hwire
  simp only [List.mem_append, List.mem_singleton] at hwire
  rcases hwire with hwire | hcarry
  · rcases hwire with hscratch | hs
    · exact by
        have := List.mem_of_mem_take hscratch
        simp [intervalEndpointSupport, this]
    · simp [intervalEndpointSupport, hs]
  · simp [intervalEndpointSupport, hcarry]

/-- Direct word semantics, scratch restoration, and locality of endpoint preparation. -/
theorem prepareIntervalEndpoints_correct
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat) (state : BasisState)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hsPositive : 0 < lengthS.length)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry)
    (hclean : Clean (scratch ++ [carry]) state) :
    let after := run
      (prepareIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) state
    wireValues lengthT after = wireValues lengthT state ∧
      wireValues lengthQ after =
        intervalLeftBits (wireValues lengthT state)
          (wireValues lengthQ state) offset ∧
      wireValues lengthS after =
        intervalRightBits (wireValues lengthS state) modulusBits offset ∧
      Clean (scratch ++ [carry]) after ∧
      ∀ wire, wire ∉ lengthQ → wire ∉ lengthS → after wire = state wire := by
  let qScratch := endpointScratch lengthQ scratch
  let sScratch := endpointScratch lengthS scratch
  have hqLength : qScratch.length = lengthQ.length := by
    exact endpointScratch_length lengthQ scratch hqWidth
  have hsLength : sScratch.length = lengthS.length := by
    exact endpointScratch_length lengthS scratch hsWidth
  have hqLayout : ConstantLayout lengthQ qScratch carry := by
    exact endpoint_constant_layout_q lengthT lengthQ lengthS scratch carry hlayout
  have hsLayout : ConstantLayout lengthS sScratch carry := by
    exact endpoint_constant_layout_s lengthT lengthQ lengthS scratch carry hlayout
  have htqLayout :=
    endpoint_cuccaro_layout lengthT lengthQ lengthS scratch carry hlayout
  have hqClean : Clean (qScratch ++ [carry]) state := by
    intro wire hwire
    apply hclean wire
    rcases List.mem_append.mp hwire with hwire | hwire
    · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
    · exact List.mem_append_right _ hwire
  have hsClean : Clean (sScratch ++ [carry]) state := by
    intro wire hwire
    apply hclean wire
    rcases List.mem_append.mp hwire with hwire | hwire
    · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
    · exact List.mem_append_right _ hwire
  let addedLengths := run (cuccaroAdd lengthT lengthQ carry) state
  have haddLengths := cuccaroAdd_correct lengthT lengthQ carry state
    htqLength htqLayout
  have hscratchAfterLengths : Clean (scratch ++ [carry]) addedLengths := by
    intro wire hwire
    rw [show addedLengths wire = state wire by
      exact haddLengths.2.2 wire (by
        intro hmem
        rcases List.mem_append.mp hwire with hscratch | hcarry
        · have hcross := (List.nodup_append.mp
              (List.nodup_cons.mp hlayout).2).2.2
          exact hcross wire hscratch wire (by simp [hmem]) rfl
        · simp only [List.mem_singleton] at hcarry
          subst wire
          exact (List.nodup_cons.mp htqLayout).1
            (List.mem_append_right lengthT hmem))]
    exact hclean wire hwire
  let addedFour := run (addConstant lengthQ qScratch carry 4) addedLengths
  have haddFour := addConstant_correct lengthQ qScratch carry 4 addedLengths
    hqLength hqLayout (by
      intro wire hwire
      exact hscratchAfterLengths wire (by
        rcases List.mem_append.mp hwire with hwire | hwire
        · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
        · exact List.mem_append_right _ hwire))
  have hworkCleanAddedFour : Clean (scratch ++ [carry]) addedFour := by
    intro wire hwire
    change run (addConstant lengthQ qScratch carry 4) addedLengths wire = false
    rw [haddFour.2.2 wire
      (endpoint_work_not_mem_q _ _ _ _ _ hlayout wire hwire)]
    exact hscratchAfterLengths wire hwire
  let reflectedS := run
    (constMinus lengthS sScratch carry (modulusBits + 2)) addedFour
  have hsCleanAddedFour : Clean (sScratch ++ [carry]) addedFour := by
    intro wire hwire
    exact hworkCleanAddedFour wire (by
      rcases List.mem_append.mp hwire with hwire | hwire
      · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
      · exact List.mem_append_right _ hwire)
  have hreflect := constMinus_correct lengthS sScratch carry
    (modulusBits + 2) addedFour hsPositive hsLength hsLayout hsCleanAddedFour
  have hworkCleanReflected : Clean (scratch ++ [carry]) reflectedS := by
    intro wire hwire
    change run
      (constMinus lengthS sScratch carry (modulusBits + 2)) addedFour wire = false
    rw [hreflect.2.2 wire
      (endpoint_work_not_mem_s _ _ _ _ _ hlayout wire hwire)]
    exact hworkCleanAddedFour wire hwire
  let shiftedQ := run (subConstant lengthQ qScratch carry offset) reflectedS
  have hqCleanReflected : Clean (qScratch ++ [carry]) reflectedS := by
    intro wire hwire
    exact hworkCleanReflected wire (by
      rcases List.mem_append.mp hwire with hwire | hwire
      · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
      · exact List.mem_append_right _ hwire)
  have hshiftQ := subConstant_correct lengthQ qScratch carry offset reflectedS
    hqLength hqLayout hqCleanReflected
  have hworkCleanShiftedQ : Clean (scratch ++ [carry]) shiftedQ := by
    intro wire hwire
    change run (subConstant lengthQ qScratch carry offset) reflectedS wire = false
    rw [hshiftQ.2.2 wire
      (endpoint_work_not_mem_q _ _ _ _ _ hlayout wire hwire)]
    exact hworkCleanReflected wire hwire
  let after := run (subConstant lengthS sScratch carry offset) shiftedQ
  have hsCleanShifted : Clean (sScratch ++ [carry]) shiftedQ := by
    intro wire hwire
    exact hworkCleanShiftedQ wire (by
      rcases List.mem_append.mp hwire with hwire | hwire
      · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
      · exact List.mem_append_right _ hwire)
  have hshiftS := subConstant_correct lengthS sScratch carry offset shiftedQ
    hsLength hsLayout hsCleanShifted
  have hworkCleanAfter : Clean (scratch ++ [carry]) after := by
    intro wire hwire
    change run (subConstant lengthS sScratch carry offset) shiftedQ wire = false
    rw [hshiftS.2.2 wire
      (endpoint_work_not_mem_s _ _ _ _ _ hlayout wire hwire)]
    exact hworkCleanShiftedQ wire hwire
  rw [prepareIntervalEndpoints, run_append, run_append, run_append, run_append]
  change wireValues lengthT after = wireValues lengthT state ∧
    wireValues lengthQ after =
      intervalLeftBits (wireValues lengthT state)
        (wireValues lengthQ state) offset ∧
    wireValues lengthS after =
      intervalRightBits (wireValues lengthS state) modulusBits offset ∧
    Clean (scratch ++ [carry]) after ∧
    ∀ wire, wire ∉ lengthQ → wire ∉ lengthS → after wire = state wire
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      wireValues lengthT after = wireValues lengthT addedLengths := by
        apply endpoint_wireValues_congr
        intro wire hwire
        change run (subConstant lengthS sScratch carry offset) shiftedQ wire =
          addedLengths wire
        rw [hshiftS.2.2 wire
          (endpoint_t_not_mem_s _ _ _ _ _ hlayout wire hwire)]
        change run (subConstant lengthQ qScratch carry offset) reflectedS wire =
          addedLengths wire
        rw [hshiftQ.2.2 wire
          (endpoint_t_not_mem_q _ _ _ _ _ hlayout wire hwire)]
        change run
          (constMinus lengthS sScratch carry (modulusBits + 2)) addedFour wire =
            addedLengths wire
        rw [hreflect.2.2 wire
          (endpoint_t_not_mem_s _ _ _ _ _ hlayout wire hwire)]
        change run (addConstant lengthQ qScratch carry 4) addedLengths wire =
          addedLengths wire
        rw [haddFour.2.2 wire
          (endpoint_t_not_mem_q _ _ _ _ _ hlayout wire hwire)]
      _ = wireValues lengthT state := by
        simpa only [addedLengths] using haddLengths.1
  · rw [show wireValues lengthQ after = wireValues lengthQ shiftedQ by
      apply endpoint_wireValues_congr
      intro wire hwire
      change run (subConstant lengthS sScratch carry offset) shiftedQ wire =
        shiftedQ wire
      exact hshiftS.2.2 wire
        (endpoint_q_not_mem_s _ _ _ _ _ hlayout wire hwire)]
    rw [hshiftQ.1, hqLength]
    unfold intervalLeftBits
    rw [show wireValues lengthQ reflectedS = wireValues lengthQ addedFour by
      apply endpoint_wireValues_congr
      intro wire hwire
      change run
        (constMinus lengthS sScratch carry (modulusBits + 2)) addedFour wire =
          addedFour wire
      exact hreflect.2.2 wire
        (endpoint_q_not_mem_s _ _ _ _ _ hlayout wire hwire), haddFour.1,
      hqLength]
    rw [show wireValues lengthQ addedLengths =
        cuccaroAddBits false (wireValues lengthT state)
          (wireValues lengthQ state) by
      simpa only [addedLengths, hclean carry (by simp)] using haddLengths.2.1]
    simp only [wireValues, List.length_map]
  · rw [hshiftS.1, hsLength]
    unfold intervalRightBits
    rw [show wireValues lengthS shiftedQ = wireValues lengthS reflectedS by
      apply endpoint_wireValues_congr
      intro wire hwire
      change run (subConstant lengthQ qScratch carry offset) reflectedS wire =
        reflectedS wire
      exact hshiftQ.2.2 wire
        (endpoint_s_not_mem_q _ _ _ _ _ hlayout wire hwire)]
    rw [show wireValues lengthS reflectedS =
        constMinusBits (wireValues lengthS state) (modulusBits + 2) by
      calc
        wireValues lengthS reflectedS =
            constMinusBits (wireValues lengthS addedFour)
              (modulusBits + 2) := by
          simpa only [reflectedS] using hreflect.1
        _ = constMinusBits (wireValues lengthS state)
              (modulusBits + 2) := by
          congr 1
          apply endpoint_wireValues_congr
          intro wire hwire
          change run (addConstant lengthQ qScratch carry 4) addedLengths wire =
            state wire
          rw [haddFour.2.2 wire
            (endpoint_s_not_mem_q _ _ _ _ _ hlayout wire hwire)]
          change run (cuccaroAdd lengthT lengthQ carry) state wire = state wire
          rw [haddLengths.2.2 wire
            (endpoint_s_not_mem_q _ _ _ _ _ hlayout wire hwire)]]
    simp only [wireValues, List.length_map]
  · exact hworkCleanAfter
  · intro wire hq hs
    change run (subConstant lengthS sScratch carry offset) shiftedQ wire =
      state wire
    rw [hshiftS.2.2 wire hs]
    change run (subConstant lengthQ qScratch carry offset) reflectedS wire =
      state wire
    rw [hshiftQ.2.2 wire hq]
    change run
      (constMinus lengthS sScratch carry (modulusBits + 2)) addedFour wire =
        state wire
    rw [hreflect.2.2 wire hs]
    change run (addConstant lengthQ qScratch carry 4) addedLengths wire =
      state wire
    rw [haddFour.2.2 wire hq]
    change run (cuccaroAdd lengthT lengthQ carry) state wire = state wire
    rw [haddLengths.2.2 wire hq]

/-- Direct word semantics, scratch restoration, and locality of the literal restoration stream. -/
theorem restoreIntervalEndpoints_correct
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat) (state : BasisState)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hsPositive : 0 < lengthS.length)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry)
    (hclean : Clean (scratch ++ [carry]) state) :
    let after := run
      (restoreIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) state
    wireValues lengthT after = wireValues lengthT state ∧
      wireValues lengthQ after =
        restoredIntervalLeftBits (wireValues lengthT state)
          (wireValues lengthQ state) offset ∧
      wireValues lengthS after =
        restoredIntervalRightBits (wireValues lengthS state) modulusBits offset ∧
      Clean (scratch ++ [carry]) after ∧
      ∀ wire, wire ∉ lengthQ → wire ∉ lengthS → after wire = state wire := by
  let qScratch := endpointScratch lengthQ scratch
  let sScratch := endpointScratch lengthS scratch
  have hqLength : qScratch.length = lengthQ.length :=
    endpointScratch_length lengthQ scratch hqWidth
  have hsLength : sScratch.length = lengthS.length :=
    endpointScratch_length lengthS scratch hsWidth
  have hqLayout : ConstantLayout lengthQ qScratch carry :=
    endpoint_constant_layout_q lengthT lengthQ lengthS scratch carry hlayout
  have hsLayout : ConstantLayout lengthS sScratch carry :=
    endpoint_constant_layout_s lengthT lengthQ lengthS scratch carry hlayout
  have htqLayout :=
    endpoint_cuccaro_layout lengthT lengthQ lengthS scratch carry hlayout
  have hqClean : Clean (qScratch ++ [carry]) state := by
    intro wire hwire
    apply hclean wire
    rcases List.mem_append.mp hwire with hwire | hwire
    · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
    · exact List.mem_append_right _ hwire
  have hsClean : Clean (sScratch ++ [carry]) state := by
    intro wire hwire
    apply hclean wire
    rcases List.mem_append.mp hwire with hwire | hwire
    · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
    · exact List.mem_append_right _ hwire
  let addedS := run (addConstant lengthS sScratch carry offset) state
  have haddS := addConstant_correct lengthS sScratch carry offset state
    hsLength hsLayout hsClean
  have hworkCleanAddedS : Clean (scratch ++ [carry]) addedS := by
    intro wire hwire
    change run (addConstant lengthS sScratch carry offset) state wire = false
    rw [haddS.2.2 wire
      (endpoint_work_not_mem_s _ _ _ _ _ hlayout wire hwire)]
    exact hclean wire hwire
  let addedQ := run (addConstant lengthQ qScratch carry offset) addedS
  have hqCleanAddedS : Clean (qScratch ++ [carry]) addedS := by
    intro wire hwire
    exact hworkCleanAddedS wire (by
      rcases List.mem_append.mp hwire with hwire | hwire
      · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
      · exact List.mem_append_right _ hwire)
  have haddQ := addConstant_correct lengthQ qScratch carry offset addedS
    hqLength hqLayout hqCleanAddedS
  have hworkCleanAddedQ : Clean (scratch ++ [carry]) addedQ := by
    intro wire hwire
    change run (addConstant lengthQ qScratch carry offset) addedS wire = false
    rw [haddQ.2.2 wire
      (endpoint_work_not_mem_q _ _ _ _ _ hlayout wire hwire)]
    exact hworkCleanAddedS wire hwire
  let reflectedS := run
    (constMinus lengthS sScratch carry (modulusBits + 2)) addedQ
  have hsCleanAddedQ : Clean (sScratch ++ [carry]) addedQ := by
    intro wire hwire
    exact hworkCleanAddedQ wire (by
      rcases List.mem_append.mp hwire with hwire | hwire
      · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
      · exact List.mem_append_right _ hwire)
  have hreflect := constMinus_correct lengthS sScratch carry
    (modulusBits + 2) addedQ hsPositive hsLength hsLayout hsCleanAddedQ
  have hworkCleanReflected : Clean (scratch ++ [carry]) reflectedS := by
    intro wire hwire
    change run
      (constMinus lengthS sScratch carry (modulusBits + 2)) addedQ wire = false
    rw [hreflect.2.2 wire
      (endpoint_work_not_mem_s _ _ _ _ _ hlayout wire hwire)]
    exact hworkCleanAddedQ wire hwire
  let subFour := run (subConstant lengthQ qScratch carry 4) reflectedS
  have hqCleanReflected : Clean (qScratch ++ [carry]) reflectedS := by
    intro wire hwire
    exact hworkCleanReflected wire (by
      rcases List.mem_append.mp hwire with hwire | hwire
      · exact List.mem_append_left _ (List.mem_of_mem_take hwire)
      · exact List.mem_append_right _ hwire)
  have hsubFour := subConstant_correct lengthQ qScratch carry 4 reflectedS
    hqLength hqLayout hqCleanReflected
  have hworkCleanSubFour : Clean (scratch ++ [carry]) subFour := by
    intro wire hwire
    change run (subConstant lengthQ qScratch carry 4) reflectedS wire = false
    rw [hsubFour.2.2 wire
      (endpoint_work_not_mem_q _ _ _ _ _ hlayout wire hwire)]
    exact hworkCleanReflected wire hwire
  let after := run (cuccaroSub lengthT lengthQ carry) subFour
  have hsub := cuccaroSub_correct lengthT lengthQ carry subFour
    htqLength htqLayout
  rw [restoreIntervalEndpoints, run_append, run_append, run_append, run_append]
  change wireValues lengthT after = wireValues lengthT state ∧
    wireValues lengthQ after =
      restoredIntervalLeftBits (wireValues lengthT state)
        (wireValues lengthQ state) offset ∧
    wireValues lengthS after =
      restoredIntervalRightBits (wireValues lengthS state) modulusBits offset ∧
    Clean (scratch ++ [carry]) after ∧
    ∀ wire, wire ∉ lengthQ → wire ∉ lengthS → after wire = state wire
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      wireValues lengthT after = wireValues lengthT subFour := hsub.1
      _ = wireValues lengthT state := by
        apply endpoint_wireValues_congr
        intro wire hwire
        change run (subConstant lengthQ qScratch carry 4) reflectedS wire =
          state wire
        rw [hsubFour.2.2 wire
          (endpoint_t_not_mem_q _ _ _ _ _ hlayout wire hwire)]
        change run
          (constMinus lengthS sScratch carry (modulusBits + 2)) addedQ wire =
            state wire
        rw [hreflect.2.2 wire
          (endpoint_t_not_mem_s _ _ _ _ _ hlayout wire hwire)]
        change run (addConstant lengthQ qScratch carry offset) addedS wire =
          state wire
        rw [haddQ.2.2 wire
          (endpoint_t_not_mem_q _ _ _ _ _ hlayout wire hwire)]
        change run (addConstant lengthS sScratch carry offset) state wire =
          state wire
        rw [haddS.2.2 wire
          (endpoint_t_not_mem_s _ _ _ _ _ hlayout wire hwire)]
  · rw [hsub.2.1]
    unfold restoredIntervalLeftBits
    rw [show subFour carry = false by
      exact hworkCleanSubFour carry (by simp)]
    rw [show wireValues lengthT subFour = wireValues lengthT state by
      apply endpoint_wireValues_congr
      intro wire hwire
      change run (subConstant lengthQ qScratch carry 4) reflectedS wire =
        state wire
      rw [hsubFour.2.2 wire
        (endpoint_t_not_mem_q _ _ _ _ _ hlayout wire hwire)]
      change run
        (constMinus lengthS sScratch carry (modulusBits + 2)) addedQ wire =
          state wire
      rw [hreflect.2.2 wire
        (endpoint_t_not_mem_s _ _ _ _ _ hlayout wire hwire)]
      change run (addConstant lengthQ qScratch carry offset) addedS wire =
        state wire
      rw [haddQ.2.2 wire
        (endpoint_t_not_mem_q _ _ _ _ _ hlayout wire hwire)]
      change run (addConstant lengthS sScratch carry offset) state wire = state wire
      rw [haddS.2.2 wire
        (endpoint_t_not_mem_s _ _ _ _ _ hlayout wire hwire)]]
    rw [hsubFour.1, hqLength]
    rw [show wireValues lengthQ reflectedS = wireValues lengthQ addedQ by
      apply endpoint_wireValues_congr
      intro wire hwire
      change run
        (constMinus lengthS sScratch carry (modulusBits + 2)) addedQ wire =
          addedQ wire
      rw [hreflect.2.2 wire
        (endpoint_q_not_mem_s _ _ _ _ _ hlayout wire hwire)]]
    rw [haddQ.1, hqLength]
    rw [show wireValues lengthQ addedS = wireValues lengthQ state by
      apply endpoint_wireValues_congr
      intro wire hwire
      change run (addConstant lengthS sScratch carry offset) state wire = state wire
      rw [haddS.2.2 wire
        (endpoint_q_not_mem_s _ _ _ _ _ hlayout wire hwire)]]
    simp only [wireValues, List.length_map]
  · calc
      wireValues lengthS after = wireValues lengthS reflectedS := by
        apply endpoint_wireValues_congr
        intro wire hwire
        change run (cuccaroSub lengthT lengthQ carry) subFour wire =
          reflectedS wire
        rw [hsub.2.2 wire
          (endpoint_s_not_mem_q _ _ _ _ _ hlayout wire hwire)]
        change run (subConstant lengthQ qScratch carry 4) reflectedS wire =
          reflectedS wire
        rw [hsubFour.2.2 wire
          (endpoint_s_not_mem_q _ _ _ _ _ hlayout wire hwire)]
      _ = restoredIntervalRightBits (wireValues lengthS state)
          modulusBits offset := by
        rw [show wireValues lengthS reflectedS =
            constMinusBits (wireValues lengthS addedQ) (modulusBits + 2) by
          simpa only [reflectedS] using hreflect.1]
        unfold restoredIntervalRightBits
        rw [show wireValues lengthS addedQ = wireValues lengthS addedS by
          apply endpoint_wireValues_congr
          intro wire hwire
          change run (addConstant lengthQ qScratch carry offset) addedS wire =
            addedS wire
          rw [haddQ.2.2 wire
            (endpoint_s_not_mem_q _ _ _ _ _ hlayout wire hwire)]]
        rw [show wireValues lengthS addedS =
            cuccaroAddBits false (constantBits sScratch.length offset)
              (wireValues lengthS state) by
          simpa only [addedS] using haddS.1, hsLength]
        simp only [wireValues, List.length_map]
  · intro wire hwire
    change run (cuccaroSub lengthT lengthQ carry) subFour wire = false
    rw [hsub.2.2 wire
      (endpoint_work_not_mem_q _ _ _ _ _ hlayout wire hwire)]
    exact hworkCleanSubFour wire hwire
  · intro wire hq hs
    change run (cuccaroSub lengthT lengthQ carry) subFour wire = state wire
    rw [hsub.2.2 wire hq]
    change run (subConstant lengthQ qScratch carry 4) reflectedS wire = state wire
    rw [hsubFour.2.2 wire hq]
    change run
      (constMinus lengthS sScratch carry (modulusBits + 2)) addedQ wire = state wire
    rw [hreflect.2.2 wire hs]
    change run (addConstant lengthQ qScratch carry offset) addedS wire = state wire
    rw [haddQ.2.2 wire hq]
    change run (addConstant lengthS sScratch carry offset) state wire = state wire
    rw [haddS.2.2 wire hs]

theorem prepareIntervalEndpoints_usesOnly
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat) :
    PaperCircuitUsesOnly
      (intervalEndpointSupport lengthT lengthQ lengthS scratch carry)
      (prepareIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) := by
  rw [prepareIntervalEndpoints]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply PaperCircuitUsesOnly.append
      · apply PaperCircuitUsesOnly.append
        · apply (cuccaroAdd_usesOnly lengthT lengthQ carry).mono
          exact endpoint_cuccaro_mem_support _ _ _ _ _
        · apply (addConstant_usesOnly lengthQ
            (endpointScratch lengthQ scratch) carry 4).mono
          exact endpoint_q_constant_mem_support _ _ _ _ _
      · apply (constMinus_usesOnly lengthS
          (endpointScratch lengthS scratch) carry (modulusBits + 2)).mono
        exact endpoint_s_constant_mem_support _ _ _ _ _
    · apply (subConstant_usesOnly lengthQ
        (endpointScratch lengthQ scratch) carry offset).mono
      exact endpoint_q_constant_mem_support _ _ _ _ _
  · apply (subConstant_usesOnly lengthS
      (endpointScratch lengthS scratch) carry offset).mono
    exact endpoint_s_constant_mem_support _ _ _ _ _

theorem restoreIntervalEndpoints_usesOnly
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat) :
    PaperCircuitUsesOnly
      (intervalEndpointSupport lengthT lengthQ lengthS scratch carry)
      (restoreIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) := by
  rw [restoreIntervalEndpoints]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply PaperCircuitUsesOnly.append
      · apply PaperCircuitUsesOnly.append
        · apply (addConstant_usesOnly lengthS
            (endpointScratch lengthS scratch) carry offset).mono
          exact endpoint_s_constant_mem_support _ _ _ _ _
        · apply (addConstant_usesOnly lengthQ
            (endpointScratch lengthQ scratch) carry offset).mono
          exact endpoint_q_constant_mem_support _ _ _ _ _
      · apply (constMinus_usesOnly lengthS
          (endpointScratch lengthS scratch) carry (modulusBits + 2)).mono
        exact endpoint_s_constant_mem_support _ _ _ _ _
    · apply (subConstant_usesOnly lengthQ
        (endpointScratch lengthQ scratch) carry 4).mono
      exact endpoint_q_constant_mem_support _ _ _ _ _
  · apply (cuccaroSub_usesOnly lengthT lengthQ carry).mono
    exact endpoint_cuccaro_mem_support _ _ _ _ _

theorem prepareIntervalEndpoints_wellFormed
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    CircuitWellFormed
      (prepareIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) := by
  have hqLength := endpointScratch_length lengthQ scratch hqWidth
  have hsLength := endpointScratch_length lengthS scratch hsWidth
  have hqLayout :=
    endpoint_constant_layout_q lengthT lengthQ lengthS scratch carry hlayout
  have hsLayout :=
    endpoint_constant_layout_s lengthT lengthQ lengthS scratch carry hlayout
  simp only [prepareIntervalEndpoints, circuitWellFormed_append]
  exact ⟨⟨⟨⟨
    cuccaroAdd_wellFormed lengthT lengthQ carry htqLength
      (endpoint_cuccaro_layout _ _ _ _ _ hlayout),
    addConstant_wellFormed lengthQ _ carry 4 hqLength hqLayout⟩,
    constMinus_wellFormed lengthS _ carry (modulusBits + 2)
      hsLength hsLayout⟩,
    subConstant_wellFormed lengthQ _ carry offset hqLength hqLayout⟩,
    subConstant_wellFormed lengthS _ carry offset hsLength hsLayout⟩

theorem restoreIntervalEndpoints_wellFormed
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hlayout : IntervalEndpointLayout lengthT lengthQ lengthS scratch carry) :
    CircuitWellFormed
      (restoreIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) := by
  have hqLength := endpointScratch_length lengthQ scratch hqWidth
  have hsLength := endpointScratch_length lengthS scratch hsWidth
  have hqLayout :=
    endpoint_constant_layout_q lengthT lengthQ lengthS scratch carry hlayout
  have hsLayout :=
    endpoint_constant_layout_s lengthT lengthQ lengthS scratch carry hlayout
  simp only [restoreIntervalEndpoints, circuitWellFormed_append]
  exact ⟨⟨⟨⟨
    addConstant_wellFormed lengthS _ carry offset hsLength hsLayout,
    addConstant_wellFormed lengthQ _ carry offset hqLength hqLayout⟩,
    constMinus_wellFormed lengthS _ carry (modulusBits + 2)
      hsLength hsLayout⟩,
    subConstant_wellFormed lengthQ _ carry 4 hqLength hqLayout⟩,
    cuccaroSub_wellFormed lengthT lengthQ carry htqLength
      (endpoint_cuccaro_layout _ _ _ _ _ hlayout)⟩

/-- Closed coherent Toffoli formula shared by preparation and restoration. -/
def intervalEndpointToffoliFormula
    (lengthT lengthQ lengthS : Nat) : Nat :=
  2 * lengthT + 4 * lengthQ + 2 * (lengthS - 2) + 4 * lengthS

/-- Closed coherent CNOT formula shared by preparation and restoration. -/
def intervalEndpointCnotFormula
    (lengthT lengthQ lengthS : Nat) : Nat :=
  4 * lengthT + 8 * lengthQ + 9 * lengthS + 1

/-- Framework-derived coherent T formula. -/
def intervalEndpointTFormula
    (lengthT lengthQ lengthS : Nat) : Nat :=
  14 * lengthT + 28 * lengthQ + 14 * (lengthS - 2) + 28 * lengthS

theorem prepareIntervalEndpoints_toffoliCount
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hsPositive : 0 < lengthS.length) :
    eeaToffoliCount
      (prepareIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) =
      intervalEndpointToffoliFormula lengthT.length lengthQ.length lengthS.length := by
  have hqLength := endpointScratch_length lengthQ scratch hqWidth
  have hsLength := endpointScratch_length lengthS scratch hsWidth
  simp only [prepareIntervalEndpoints, eeaToffoliCount_append]
  rw [cuccaroAdd_toffoliCount lengthT lengthQ carry htqLength,
    addConstant_toffoliCount lengthQ _ carry 4 hqLength,
    constMinus_toffoliCount lengthS _ carry (modulusBits + 2)
      hsPositive hsLength,
    subConstant_toffoliCount lengthQ _ carry offset hqLength,
    subConstant_toffoliCount lengthS _ carry offset hsLength]
  simp [intervalEndpointToffoliFormula]
  omega

theorem restoreIntervalEndpoints_toffoliCount
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hsPositive : 0 < lengthS.length) :
    eeaToffoliCount
      (restoreIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) =
      intervalEndpointToffoliFormula lengthT.length lengthQ.length lengthS.length := by
  have hqLength := endpointScratch_length lengthQ scratch hqWidth
  have hsLength := endpointScratch_length lengthS scratch hsWidth
  simp only [restoreIntervalEndpoints, eeaToffoliCount_append]
  rw [addConstant_toffoliCount lengthS _ carry offset hsLength,
    addConstant_toffoliCount lengthQ _ carry offset hqLength,
    constMinus_toffoliCount lengthS _ carry (modulusBits + 2)
      hsPositive hsLength,
    subConstant_toffoliCount lengthQ _ carry 4 hqLength,
    cuccaroSub_toffoliCount lengthT lengthQ carry htqLength]
  simp [intervalEndpointToffoliFormula]
  omega

theorem prepareIntervalEndpoints_cnotCount
    (lengthT lengthQ scratch sRest : List Wire)
    (sLow sNext carry : Wire) (modulusBits offset : Nat)
    (htqLength : lengthT.length = (lengthQ : List Wire).length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : (sLow :: sNext :: sRest).length ≤ scratch.length) :
    eeaCnotCount
      (prepareIntervalEndpoints lengthT lengthQ (sLow :: sNext :: sRest)
        scratch carry modulusBits offset) =
      intervalEndpointCnotFormula lengthT.length lengthQ.length
        (sLow :: sNext :: sRest).length := by
  have hqLength := endpointScratch_length lengthQ scratch hqWidth
  have hsLength := endpointScratch_length (sLow :: sNext :: sRest) scratch hsWidth
  simp only [prepareIntervalEndpoints, eeaCnotCount_append]
  rw [cuccaroAdd_cnotCount lengthT lengthQ carry htqLength,
    addConstant_cnotCount lengthQ _ carry 4 hqLength,
    constMinus_cnotCount sLow sNext sRest _ carry (modulusBits + 2) hsLength,
    subConstant_cnotCount lengthQ _ carry offset hqLength,
    subConstant_cnotCount (sLow :: sNext :: sRest) _ carry offset hsLength]
  simp [intervalEndpointCnotFormula]
  omega

theorem restoreIntervalEndpoints_cnotCount
    (lengthT lengthQ scratch sRest : List Wire)
    (sLow sNext carry : Wire) (modulusBits offset : Nat)
    (htqLength : lengthT.length = (lengthQ : List Wire).length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : (sLow :: sNext :: sRest).length ≤ scratch.length) :
    eeaCnotCount
      (restoreIntervalEndpoints lengthT lengthQ (sLow :: sNext :: sRest)
        scratch carry modulusBits offset) =
      intervalEndpointCnotFormula lengthT.length lengthQ.length
        (sLow :: sNext :: sRest).length := by
  have hqLength := endpointScratch_length lengthQ scratch hqWidth
  have hsLength := endpointScratch_length (sLow :: sNext :: sRest) scratch hsWidth
  simp only [restoreIntervalEndpoints, eeaCnotCount_append]
  rw [addConstant_cnotCount (sLow :: sNext :: sRest) _ carry offset hsLength,
    addConstant_cnotCount lengthQ _ carry offset hqLength,
    constMinus_cnotCount sLow sNext sRest _ carry (modulusBits + 2) hsLength,
    subConstant_cnotCount lengthQ _ carry 4 hqLength,
    cuccaroSub_cnotCount lengthT lengthQ carry htqLength]
  simp [intervalEndpointCnotFormula]
  omega

theorem prepareIntervalEndpoints_tCount
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hsPositive : 0 < lengthS.length) :
    ShorECDLP.tCount
      (prepareIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) =
      intervalEndpointTFormula lengthT.length lengthQ.length lengthS.length := by
  have hqLength := endpointScratch_length lengthQ scratch hqWidth
  have hsLength := endpointScratch_length lengthS scratch hsWidth
  simp only [prepareIntervalEndpoints, tCount_append]
  rw [cuccaroAdd_tCount lengthT lengthQ carry htqLength,
    addConstant_tCount lengthQ _ carry 4 hqLength,
    constMinus_tCount lengthS _ carry (modulusBits + 2) hsPositive hsLength,
    subConstant_tCount lengthQ _ carry offset hqLength,
    subConstant_tCount lengthS _ carry offset hsLength]
  simp [intervalEndpointTFormula]
  omega

theorem restoreIntervalEndpoints_tCount
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat)
    (htqLength : lengthT.length = lengthQ.length)
    (hqWidth : lengthQ.length ≤ scratch.length)
    (hsWidth : lengthS.length ≤ scratch.length)
    (hsPositive : 0 < lengthS.length) :
    ShorECDLP.tCount
      (restoreIntervalEndpoints lengthT lengthQ lengthS scratch carry
        modulusBits offset) =
      intervalEndpointTFormula lengthT.length lengthQ.length lengthS.length := by
  have hqLength := endpointScratch_length lengthQ scratch hqWidth
  have hsLength := endpointScratch_length lengthS scratch hsWidth
  simp only [restoreIntervalEndpoints, tCount_append]
  rw [addConstant_tCount lengthS _ carry offset hsLength,
    addConstant_tCount lengthQ _ carry offset hqLength,
    constMinus_tCount lengthS _ carry (modulusBits + 2) hsPositive hsLength,
    subConstant_tCount lengthQ _ carry 4 hqLength,
    cuccaroSub_tCount lengthT lengthQ carry htqLength]
  simp [intervalEndpointTFormula]
  omega

@[simp]
theorem prepareIntervalEndpoints_HPFree
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat) :
    HPFree (prepareIntervalEndpoints lengthT lengthQ lengthS scratch carry
      modulusBits offset) := by
  simp [prepareIntervalEndpoints]

@[simp]
theorem restoreIntervalEndpoints_HPFree
    (lengthT lengthQ lengthS scratch : List Wire) (carry : Wire)
    (modulusBits offset : Nat) :
    HPFree (restoreIntervalEndpoints lengthT lengthQ lengthS scratch carry
      modulusBits offset) := by
  simp [restoreIntervalEndpoints]

end ShorECDLP.Paper2607_13816
