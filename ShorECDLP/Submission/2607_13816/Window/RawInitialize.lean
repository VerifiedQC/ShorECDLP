import ShorECDLP.Submission.«2607_13816».Window.RawSchedule
import ShorECDLP.Submission.«2607_13816».Window.FirstWindowReplacement
/-! Physical first lookup followed by a conditional raw tail. The excluded set
is characterized by the first failed call on the actual preceding state.
No measure or sampling-error bound is asserted for this set. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

def rawInitialState (A P : Point) (s : BasisState) : BasisState :=
  pointWrite (firstWindowTable A P (tableAddressValue (List.range' 855 16) s)) s

def initializedRawProgram (A P : Point) (x y : Nat → Nat → Nat) (js : List Nat) : AdaptiveCircuit :=
  (physicalPointLookup (firstWindowTable A P)).seq (rawWindowSchedule x y js)

def InitializedRawDomain (A P : Point) (x y : Nat → Nat → Nat) (js : List Nat)
    (s : BasisState) : Prop :=
  PointInitializeValid s ∧ RawWindowScheduleDomain x y js (rawInitialState A P s)

private theorem lookup_input (s : BasisState) (hs : PointInitializeValid s) :
    DirectPointLookupValid (List.range' 519 16) 836 s := by
  refine ⟨?_,?_,hs.1.2⟩
  · intro w hw
    apply hs.1.1.1 w
    simp only [List.mem_append,List.mem_range'_1] at hw ⊢
    omega
  · intro w hw
    have h : s w ∈ wireValues pointLogicalWires s := List.mem_map.mpr ⟨w,hw,rfl⟩
    rw [hs.2] at h
    exact (List.mem_replicate.mp h).2

theorem initializedRawProgram_coherent (A P : Point) (x y : Nat → Nat → Nat) (js : List Nat) :
    CoherentlyImplementsOn (initializedRawProgram A P x y js)
      (Finsupp.lmapDomain ℂ ℂ (fun s => rawWindowScheduleState x y js (rawInitialState A P s)))
      (InitializedRawDomain A P x y js) := by
  obtain ⟨cs,ha,hm⟩ := physicalPointLookup_coherent (firstWindowTable A P)
  have h : CoherentlyImplementsOn (physicalPointLookup (firstWindowTable A P))
      (Finsupp.lmapDomain ℂ ℂ (rawInitialState A P)) (InitializedRawDomain A P x y js) :=
    ⟨cs,ha.imp (fun b c hb s hs => hb s (lookup_input s hs.1)),hm⟩
  have hh := h.seq (rawWindowSchedule_coherent x y js) (by
    intro s hs
    simpa [ket] using supportedOn_ket _ _ hs.2)
  apply hh.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

/-- The first lookup establishes clean query readiness, even when its point is
infinity. This statement does not establish either next nonzero condition. -/
theorem rawInitialState_ready (A P : Point) (s : BasisState) (hs : PointInitializeValid s) :
    WindowPointValid (rawInitialState A P s) :=
  pointInitialize_ready _ s hs

/-- A first failure includes a valid prefix, so no invalid raw call is used to
justify the state where this failure occurs. `j` is the next physical bank. -/
def RawFirstFailure (x y : Nat → Nat → Nat) (js : List Nat) (s : BasisState) : Prop :=
  ∃ pre j post, js = pre ++ j::post ∧ RawWindowScheduleDomain x y pre s ∧
    ¬ PreparedRawDomain x y j (rawWindowScheduleState x y pre s)

theorem rawWindowSchedule_domain_or_firstFailure (x y : Nat → Nat → Nat)
    (js : List Nat) (s : BasisState) :
    RawWindowScheduleDomain x y js s ∨ RawFirstFailure x y js s := by
  induction js generalizing s with
  | nil => exact Or.inl trivial
  | cons j js ih =>
    by_cases h : PreparedRawDomain x y j s
    · rcases ih (preparedRawState x y j s) with ht | ⟨pre,k,post,he,hpre,hbad⟩
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr ⟨j::pre,k,post,by simp [he],⟨h,hpre⟩,hbad⟩
    · exact Or.inr ⟨[],j,js,rfl,trivial,h⟩

private theorem domain_append (x y : Nat → Nat → Nat) (pre tail : List Nat) (s : BasisState)
    (h : RawWindowScheduleDomain x y (pre++tail) s) :
    RawWindowScheduleDomain x y tail (rawWindowScheduleState x y pre s) := by
  induction pre generalizing s with
  | nil => exact h
  | cons j pre ih => exact ih (preparedRawState x y j s) h.2

theorem initializedRawDomain_iff_no_firstFailure (A P : Point) (x y : Nat → Nat → Nat)
    (js : List Nat) (s : BasisState) (hs : PointInitializeValid s) :
    InitializedRawDomain A P x y js s ↔ ¬ RawFirstFailure x y js (rawInitialState A P s) := by
  constructor
  · rintro ⟨_,h⟩ ⟨pre,j,post,he,_,hbad⟩
    rw [he] at h
    exact hbad (domain_append x y pre (j::post) _ h).1
  · intro h
    rcases rawWindowSchedule_domain_or_firstFailure x y js (rawInitialState A P s) with hg | hb
    · exact ⟨hs,hg⟩
    · exact False.elim (h hb)
end
end ShorECDLP.Paper2607_13816
