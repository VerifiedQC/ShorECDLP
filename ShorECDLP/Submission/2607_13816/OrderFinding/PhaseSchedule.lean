import ShorECDLP.Submission.«2607_13816».OrderFinding.PhaseProduct
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum
open scoped BigOperators
noncomputable section
/-- Actual point-oracle sampling with one measured and reset control wire. -/
def pointPhaseSchedule (P : Secp256k1.Point) : List Nat → List Bool → AdaptiveCircuit
  | [], _ => .done
  | t::ts, prior => .unitary [.H 836] ((pointAddProgram (t • P)).seq
      (.unitary (fourierHistoryRotations .inverse 836 prior 2)
        (.xMeasureReset 836 (pointPhaseSchedule P ts (false::prior))
          (pointPhaseSchedule P ts (true::prior)))))
/-- Sample bits are kept separately from the oracle's internal measurement history. -/
structure PhaseSampleBranch where
  samples : List Bool
  branch : InstrumentBranch

def pointPhaseRecords (P : Secp256k1.Point) : List Nat → List Bool → List PhaseSampleBranch
  | [], _ => [⟨[],⟨[],LinearMap.id⟩⟩]
  | t::ts, prior => (pointAddProgram (t • P)).run.flatMap fun oracle =>
      (pointPhaseRecords P ts (false::prior)).map
        (fun tail => ⟨false::tail.samples,(pointPhaseBranch prior false oracle).seq tail.branch⟩) ++
      (pointPhaseRecords P ts (true::prior)).map
        (fun tail => ⟨true::tail.samples,(pointPhaseBranch prior true oracle).seq tail.branch⟩)

theorem pointPhaseRecords_run (P : Secp256k1.Point) (ts : List Nat) (prior : List Bool) :
    (pointPhaseRecords P ts prior).map PhaseSampleBranch.branch = (pointPhaseSchedule P ts prior).run := by
  induction ts generalizing prior with
  | nil => rfl
  | cons t ts ih =>
    simp only [pointPhaseRecords,pointPhaseSchedule,AdaptiveCircuit.run,AdaptiveCircuit.run_seq,
      Instrument.seq,List.map_flatMap,List.map_append,List.map_map]
    rw [← ih (false::prior),← ih (true::prior)]
    simp only [List.map_map]
    congr 1
    funext oracle
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro tail _
      simp only [Function.comp_apply]
      apply congrArg₂ InstrumentBranch.mk
      · exact List.append_assoc _ _ _
      · ext ψ
        rfl
    · apply List.map_congr_left
      intro tail _
      simp only [Function.comp_apply]
      apply congrArg₂ InstrumentBranch.mk
      · exact List.append_assoc _ _ _
      · ext ψ
        rfl
/-- Consume exactly the outcomes used by an adaptive subprogram. -/
def consumeAdaptiveHistory : AdaptiveCircuit → List Bool → Option (List Bool)
  | .done, hist => some hist
  | .unitary _ next, hist => consumeAdaptiveHistory next hist
  | .xMeasureReset _ no yes, b::hist => consumeAdaptiveHistory (if b then yes else no) hist
  | .xMeasureReset _ _ _, [] => none

theorem consumeAdaptiveHistory_run (p : AdaptiveCircuit) (branch : InstrumentBranch)
    (hb : branch∈p.run) (suffix : List Bool) :
    consumeAdaptiveHistory p (branch.history++suffix)=some suffix := by
  induction p generalizing branch with
  | done =>
    simp only [AdaptiveCircuit.run,List.mem_cons,List.not_mem_nil,or_false] at hb
    subst branch
    simp [consumeAdaptiveHistory]
  | unitary gates next ih =>
    obtain ⟨b,hmem,rfl⟩ := List.mem_map.mp hb
    rw [consumeAdaptiveHistory]
    change consumeAdaptiveHistory next (((none : Option Bool).toList++b.history)++suffix)=some suffix
    simpa using ih b hmem
  | xMeasureReset w no yes ihn ihy =>
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨b,hmem,rfl⟩ := List.mem_map.mp hb
      change consumeAdaptiveHistory (.xMeasureReset w no yes) (([false]++b.history)++suffix)=_
      simpa [consumeAdaptiveHistory] using ihn b hmem
    · obtain ⟨b,hmem,rfl⟩ := List.mem_map.mp hb
      change consumeAdaptiveHistory (.xMeasureReset w no yes) (([true]++b.history)++suffix)=_
      simpa [consumeAdaptiveHistory] using ihy b hmem

/-- Decode the external samples by following the oracle's own history tree. -/
def decodePointPhaseSamples (P : Secp256k1.Point) : List Nat → List Bool → Option (List Bool)
  | [], hist => if hist=[] then some [] else none
  | t::ts, hist => do
      let rest ← consumeAdaptiveHistory (pointAddProgram (t • P)) hist
      match rest with
      | [] => none
      | b::rest => return b :: (← decodePointPhaseSamples P ts rest)

theorem pointPhaseRecords_decode (P : Secp256k1.Point) (ts : List Nat) (prior : List Bool)
    (record : PhaseSampleBranch) (hr : record∈pointPhaseRecords P ts prior) :
    decodePointPhaseSamples P ts record.branch.history=some record.samples := by
  induction ts generalizing prior record with
  | nil =>
    simp only [pointPhaseRecords,List.mem_cons,List.not_mem_nil,or_false] at hr
    subst record
    rfl
  | cons t ts ih =>
    obtain ⟨oracle,ho,hr⟩ := List.mem_flatMap.mp hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp hr
      change decodePointPhaseSamples P (t::ts) ((oracle.history++[false])++tail.branch.history)=_
      rw [List.append_assoc]
      simp only [decodePointPhaseSamples,consumeAdaptiveHistory_run _ oracle ho]
      simp [ih _ tail ht]
    · obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp hr
      change decodePointPhaseSamples P (t::ts) ((oracle.history++[true])++tail.branch.history)=_
      rw [List.append_assoc]
      simp only [decodePointPhaseSamples,consumeAdaptiveHistory_run _ oracle ho]
      simp [ih _ tail ht]
theorem pointPhaseRecords_length (P : Secp256k1.Point) (ts : List Nat) (prior : List Bool)
    (record : PhaseSampleBranch) (hr : record∈pointPhaseRecords P ts prior) :
    record.samples.length=ts.length := by
  induction ts generalizing prior record with
  | nil =>
    simp only [pointPhaseRecords,List.mem_cons,List.not_mem_nil,or_false] at hr
    subst record
    rfl
  | cons t ts ih =>
    obtain ⟨oracle,_,hr⟩ := List.mem_flatMap.mp hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp hr
      exact congrArg Nat.succ (ih _ tail ht)
    · obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp hr
      exact congrArg Nat.succ (ih _ tail ht)

/-- The branches for one fixed external output, still retaining every internal oracle outcome. -/
def pointPhaseSlice (P : Secp256k1.Point) : List Nat → List Bool → List Bool → Instrument
  | [], _, [] => [⟨[],LinearMap.id⟩]
  | t::ts, prior, b::bs => (pointAddProgram (t • P)).run.flatMap fun oracle =>
      (pointPhaseSlice P ts (b::prior) bs).map fun tail => (pointPhaseBranch prior b oracle).seq tail
  | _, _, _ => []

theorem pointPhaseSlice_records (P : Secp256k1.Point) (ts : List Nat) (prior bs : List Bool) :
    pointPhaseSlice P ts prior bs =
      ((pointPhaseRecords P ts prior).filter (fun rec => rec.samples==bs)).map PhaseSampleBranch.branch := by
  induction ts generalizing prior bs with
  | nil => cases bs <;> simp [pointPhaseSlice,pointPhaseRecords]
  | cons t ts ih =>
    cases bs with
    | nil => simp [pointPhaseSlice,pointPhaseRecords,List.filter_flatMap,List.filter_map]
    | cons b bs =>
      cases b <;> simp [pointPhaseSlice,pointPhaseRecords,List.filter_flatMap,List.filter_map,
        List.map_flatMap,List.map_map,Function.comp_def,ih]
def pointScheduleCoeff (r k : Nat) : List Nat → List Bool → List Bool → ℂ
  | [], _, [] => 1
  | t::ts, prior, b::bs => pointPhaseStepCoeff r k t prior b * pointScheduleCoeff r k ts (b::prior) bs
  | _, _, _ => 0
private theorem phaseCoefficients_mass (cs ds : List ℂ) :
    ((coherentSeqCoefficients cs ds).map Complex.normSq).sum =
      (cs.map Complex.normSq).sum*(ds.map Complex.normSq).sum := by
  induction cs with
  | nil => simp [coherentSeqCoefficients]
  | cons c cs ih =>
    simp only [coherentSeqCoefficients,List.flatMap_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,Complex.normSq_mul,List.sum_map_mul_left,List.map_cons,List.sum_cons]
    change _ + ((coherentSeqCoefficients cs ds).map Complex.normSq).sum = _
    rw [ih]
    ring

private theorem phaseAligned_append {R : InstrumentBranch → ℂ → Prop}
    {xs ys : Instrument} {cs ds : List ℂ}
    (h : List.Forall₂ R xs cs) (h' : List.Forall₂ R ys ds) : List.Forall₂ R (xs++ys) (cs++ds) := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h ih

private theorem phaseAligned_seq {r : Nat} (psi : Fin r → State) (prior : List Bool) (b : Bool)
    (first rest : Fin r → ℂ) {oracles tails : Instrument} {cs ds : List ℂ}
    (ho : List.Forall₂ (fun oracle c => ∀ k,
      (pointPhaseBranch prior b oracle).kraus (psi k)=(c*first k) • psi k) oracles cs)
    (ht : List.Forall₂ (fun tail d => ∀ k,
      tail.kraus (psi k)=(d*rest k) • psi k) tails ds) :
    List.Forall₂ (fun branch c => ∀ k, branch.kraus (psi k)=(c*(first k*rest k)) • psi k)
      (oracles.flatMap fun oracle => tails.map fun tail => (pointPhaseBranch prior b oracle).seq tail)
      (coherentSeqCoefficients cs ds) := by
  induction ho with
  | nil => exact .nil
  | @cons oracle c os cs hc _ ih =>
    apply phaseAligned_append
    · clear ih
      induction ht with
      | nil => exact .nil
      | @cons tail d ts ds hd _ ih' =>
        apply List.Forall₂.cons
        · intro k
          change tail.kraus ((pointPhaseBranch prior b oracle).kraus (psi k))=_
          rw [hc,map_smul,hd,smul_smul]
          congr 1
          ring
        · exact ih'
    · exact ih

theorem pointPhaseSlice_eigenstate {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (ts : List Nat) (prior bs : List Bool) (hlen : bs.length=ts.length) :
    ∃ cs : List ℂ, List.Forall₂
      (fun branch c => ∀ (k : Fin r), branch.kraus (pointCyclicState P (s[836 ↦ false]) k)=
        (c*pointScheduleCoeff r k.val ts prior bs) • pointCyclicState P (s[836 ↦ false]) k)
      (pointPhaseSlice P ts prior bs) cs ∧ (cs.map Complex.normSq).sum=1 := by
  induction ts generalizing prior bs with
  | nil =>
    have hb : bs=[] := List.length_eq_zero_iff.mp hlen
    subst bs
    refine ⟨[1],.cons ?_ .nil,by simp⟩
    intro k
    simp [pointScheduleCoeff]
  | cons t ts ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hl : bs.length=ts.length := by simpa using hlen
      obtain ⟨cs,hcs,hcm⟩ := pointPhaseBranch_eigenstate hr P horder s hs t prior
      obtain ⟨ds,hds,hdm⟩ := ih (b::prior) bs hl
      refine ⟨coherentSeqCoefficients cs ds,?_,by rw [phaseCoefficients_mass,hcm,hdm,mul_one]⟩
      exact phaseAligned_seq (fun k => pointCyclicState P (s[836 ↦ false]) k) prior b
        (fun k => pointPhaseStepCoeff r k.val t prior b)
        (fun k => pointScheduleCoeff r k.val ts (b::prior) bs)
        (hcs.imp (fun oracle c h k => h k b)) hds
/-- Descending powers implement least-significant-bit-first phase sampling. -/
def pointPhasePowers : Nat → List Nat
  | 0 => []
  | n+1 => 2^n :: pointPhasePowers n
@[simp] theorem pointPhasePowers_length (n : Nat) : (pointPhasePowers n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pointPhasePowers,ih]

theorem pointScheduleCoeff_powers (r k : Nat) (prior bs : List Bool) :
    pointScheduleCoeff r k (pointPhasePowers bs.length) prior bs = phaseProduct ((k:ℝ)/(r:ℝ)) prior bs := by
  induction bs generalizing prior with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons,pointPhasePowers,pointScheduleCoeff,ih,phaseProduct_cons_point]

theorem pointPhaseSlice_amplitude {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (bs : List Bool) :
    ∃ cs : List ℂ, List.Forall₂
      (fun branch c => ∀ (k : Fin r), branch.kraus (pointCyclicState P (s[836 ↦ false]) k)=
        (c*paperPhaseAmplitude bs.length ((k.val:ℝ)/(r:ℝ)) (fourierWordLSB bs)) •
          pointCyclicState P (s[836 ↦ false]) k)
      (pointPhaseSlice P (pointPhasePowers bs.length) List.nil bs) cs ∧ (cs.map Complex.normSq).sum=1 := by
  obtain ⟨cs,hcs,hm⟩ := pointPhaseSlice_eigenstate hr P horder s hs (pointPhasePowers bs.length) List.nil bs
    (pointPhasePowers_length bs.length).symm
  refine ⟨cs,?_,hm⟩
  simpa only [pointScheduleCoeff_powers,phaseProduct_eq_amplitude] using hcs
/-- Summing internal outcomes preserves the full interference within each character superposition. -/
theorem pointPhaseSlice_mass {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (bs : List Bool) (a : Fin r → ℂ) :
    Instrument.bornMass (pointPhaseSlice P (pointPhasePowers bs.length) List.nil bs)
      (∑ k : Fin r, a k • pointCyclicState P (s[836 ↦ false]) k) =
      ∑ k : Fin r, Complex.normSq (a k * paperPhaseAmplitude bs.length ((k.val:ℝ)/(r:ℝ)) (fourierWordLSB bs)) := by
  obtain ⟨cs,hcs,hm⟩ := pointPhaseSlice_amplitude hr P horder s hs bs
  let mass := ∑ k : Fin r, Complex.normSq
    (a k * paperPhaseAmplitude bs.length ((k.val:ℝ)/(r:ℝ)) (fourierWordLSB bs))
  have hmass (branch : InstrumentBranch) (c : ℂ)
      (h : ∀ (k : Fin r), branch.kraus (pointCyclicState P (s[836 ↦ false]) k)=
        (c*paperPhaseAmplitude bs.length ((k.val:ℝ)/(r:ℝ)) (fourierWordLSB bs)) •
          pointCyclicState P (s[836 ↦ false]) k) :
      normSq (branch.kraus (∑ k : Fin r, a k • pointCyclicState P (s[836 ↦ false]) k))=
        Complex.normSq c * mass := by
    simp_rw [map_sum,map_smul,h,smul_smul]
    simp only [pointCyclicState]
    rw [cyclicState_mass hr _ (pointCyclicBasis_orthonormal P _ horder)]
    simp only [mass,Finset.mul_sum,Complex.normSq_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have haligned : Instrument.bornMass (pointPhaseSlice P (pointPhasePowers bs.length) List.nil bs)
      (∑ k : Fin r, a k • pointCyclicState P (s[836 ↦ false]) k) =
      (cs.map Complex.normSq).sum * mass := by
    clear hm
    generalize he : pointPhaseSlice P (pointPhasePowers bs.length) List.nil bs = branches at hcs ⊢
    clear he
    induction hcs with
    | nil => simp [Instrument.bornMass]
    | @cons branch c branches cs h _ ih =>
      change normSq (branch.kraus _) + Instrument.bornMass branches _ =
        (Complex.normSq c+(cs.map Complex.normSq).sum)*mass
      rw [hmass branch c h,ih]
      ring
  rw [haligned,hm,one_mul]
/-- The fixed-output instrument is obtained by decoding and filtering the actual physical run. -/
theorem pointPhaseSlice_run (P : Secp256k1.Point) (ts : List Nat) (prior bs : List Bool) :
    pointPhaseSlice P ts prior bs = ((pointPhaseSchedule P ts prior).run.filter
      (fun branch => decodePointPhaseSamples P ts branch.history == some bs)) := by
  rw [← pointPhaseRecords_run, List.filter_map,pointPhaseSlice_records]
  apply congrArg (List.map PhaseSampleBranch.branch)
  apply List.filter_congr
  intro record hrecord
  simp [pointPhaseRecords_decode P ts prior record hrecord]

/-- Sampling from the identity point yields the uniform mixture of character amplitudes. -/
theorem pointPhaseSlice_identity_mass {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (bs : List Bool) :
    Instrument.bornMass (pointPhaseSlice P (pointPhasePowers bs.length) List.nil bs)
      (ket (pointWrite 0 (s[836 ↦ false]))) =
      (1/(r:ℝ)) * ∑ k : Fin r,
        Complex.normSq (paperPhaseAmplitude bs.length ((k.val:ℝ)/(r:ℝ)) (fourierWordLSB bs)) := by
  have hav := cyclicState_average hr (pointCyclicBasis P (s[836 ↦ false]))
  have hstate : (∑ k : Fin r, (((Real.sqrt r)⁻¹:ℝ):ℂ) • pointCyclicState P (s[836 ↦ false]) k)=
      ket (pointWrite 0 (s[836 ↦ false])) := by
    rw [← Finset.smul_sum]
    simpa [pointCyclicState,pointCyclicBasis] using hav
  rw [← hstate,pointPhaseSlice_mass hr P horder s hs]
  have hnorm : Complex.normSq ((((Real.sqrt r)⁻¹:ℝ):ℂ))=1/(r:ℝ) := by
    simp [Complex.normSq_ofReal]
  simp only [Complex.normSq_mul,hnorm,Finset.mul_sum]
end
end ShorECDLP.Paper2607_13816
