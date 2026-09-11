import ShorECDLP.Submission.«2607_13816».OrderFinding.PhaseSchedule
import ShorECDLP.Submission.«2607_13816».OrderFinding.PairSampling
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum Quantum.OrderFinding Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
private theorem eigenvalue_nat (n : Nat) : eigenvalue (n:ℝ)=1 := by
  unfold eigenvalue
  have h : Complex.I * (2 * (Real.pi:ℂ) * (n:ℂ))=(n:ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by ring
  push_cast
  rw [h,Complex.exp_nat_mul]
  simp [Complex.exp_two_pi_mul_I]

theorem paperPhaseAmplitude_mod (precision r x value : Nat) (hr : 0<r) :
    paperPhaseAmplitude precision ((x:ℝ)/(r:ℝ)) value =
      paperPhaseAmplitude precision (((x%r:Nat):ℝ)/(r:ℝ)) value := by
  have he : (x:ℝ)/(r:ℝ)=((x%r:Nat):ℝ)/(r:ℝ)+(x/r:Nat) := by
    have h : (x:ℝ)=((x%r:Nat):ℝ)+(r:ℝ)*(x/r:Nat) := by exact_mod_cast (Nat.mod_add_div x r).symm
    rw [h]
    have hn : (r:ℝ)≠0 := by positivity
    field_simp
  unfold paperPhaseAmplitude
  rw [he]
  have hd : ((x%r:Nat):ℝ)/(r:ℝ)+(x/r:Nat)-(value:ℝ)/(2^precision:Nat)=
      (((x%r:Nat):ℝ)/(r:ℝ)-(value:ℝ)/(2^precision:Nat))+(x/r:Nat) := by ring
  rw [hd,eigenvalue_add,eigenvalue_nat,mul_one]

theorem pointScheduleCoeff_scaled (r k d : Nat) (prior bs : List Bool) :
    pointScheduleCoeff r k ((pointPhasePowers bs.length).map (d*·)) prior bs =
      phaseProduct (((d*k:Nat):ℝ)/(r:ℝ)) prior bs := by
  induction bs generalizing prior with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons,pointPhasePowers,List.map_cons,pointScheduleCoeff,ih]
    rw [phaseProduct_cons_point]
    congr 1
    unfold pointPhaseStepCoeff
    rw [show k*(d*2^bs.length)=(d*k)*2^bs.length by ring]

theorem pointPhaseSlice_scaled_eigenstate {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d : Nat) (bs : List Bool) :
    ∃ cs : List ℂ, List.Forall₂
      (fun branch c => ∀ (k : Fin r), branch.kraus (pointCyclicState P (s[836 ↦ false]) k)=
        (c*paperPhaseAmplitude bs.length ((((d*k.val)%r:Nat):ℝ)/(r:ℝ)) (fourierWordLSB bs)) •
          pointCyclicState P (s[836 ↦ false]) k)
      (pointPhaseSlice P ((pointPhasePowers bs.length).map (d*·)) List.nil bs) cs ∧
      (cs.map Complex.normSq).sum=1 := by
  obtain ⟨cs,hcs,hm⟩ := pointPhaseSlice_eigenstate hr P horder s hs
    ((pointPhasePowers bs.length).map (d*·)) List.nil bs (by simp)
  refine ⟨cs,?_,hm⟩
  apply hcs.imp
  intro branch c h k
  have hk := h k
  rw [pointScheduleCoeff_scaled,phaseProduct_eq_amplitude,
    paperPhaseAmplitude_mod _ r (d*k.val) _ hr.pos] at hk
  exact hk
theorem pointPhaseSlice_nsmul (P : Secp256k1.Point) (d : Nat) (ts : List Nat) (prior bs : List Bool) :
    pointPhaseSlice (d • P) ts prior bs = pointPhaseSlice P (ts.map (d*·)) prior bs := by
  induction ts generalizing prior bs with
  | nil => cases bs <;> rfl
  | cons t ts ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [pointPhaseSlice,List.map_cons,ih,← mul_nsmul]

def pointPhasePairProgram (P Q : Secp256k1.Point) (precision : Nat) : AdaptiveCircuit :=
  (pointPhaseSchedule P (pointPhasePowers precision) List.nil).seq
    (pointPhaseSchedule Q (pointPhasePowers precision) List.nil)
def pointPhasePairSlice (P Q : Secp256k1.Point) (precision : Nat) (a b : List Bool) : Instrument :=
  Instrument.seq (pointPhaseSlice P (pointPhasePowers precision) List.nil a)
    (pointPhaseSlice Q (pointPhasePowers precision) List.nil b)

private theorem pairAligned_append {R : InstrumentBranch → ℂ → Prop}
    {xs ys : Instrument} {cs ds : List ℂ}
    (h : List.Forall₂ R xs cs) (h' : List.Forall₂ R ys ds) : List.Forall₂ R (xs++ys) (cs++ds) := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h ih
private theorem pairAligned_seq {r : Nat} (psi : Fin r → State) (first rest : Fin r → ℂ)
    {oracles tails : Instrument} {cs ds : List ℂ}
    (ho : List.Forall₂ (fun oracle c => ∀ k, oracle.kraus (psi k)=(c*first k) • psi k) oracles cs)
    (ht : List.Forall₂ (fun tail d => ∀ k, tail.kraus (psi k)=(d*rest k) • psi k) tails ds) :
    List.Forall₂ (fun branch c => ∀ k, branch.kraus (psi k)=(c*(first k*rest k)) • psi k)
      (Instrument.seq oracles tails) (coherentSeqCoefficients cs ds) := by
  induction ho with
  | nil => exact .nil
  | @cons oracle c os cs hc _ ih =>
    apply pairAligned_append
    · clear ih
      induction ht with
      | nil => exact .nil
      | @cons tail d ts ds hd _ ih' =>
        apply List.Forall₂.cons
        · intro k
          change tail.kraus (oracle.kraus (psi k))=_
          rw [hc,map_smul,hd,smul_smul]
          congr 1
          ring
        · exact ih'
    · exact ih
private theorem pairCoefficients_mass (cs ds : List ℂ) :
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

theorem pointPhasePairSlice_eigenstate {r : Nat} (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d precision : Nat) (hQ : Q=d • P) (a b : List Bool) (ha : a.length=precision) (hb : b.length=precision) :
    ∃ cs : List ℂ, List.Forall₂
      (fun branch c => ∀ (k : Fin r), branch.kraus (pointCyclicState P (s[836 ↦ false]) k)=
        (c*(paperPhaseAmplitude precision ((k.val:ℝ)/(r:ℝ)) (fourierWordLSB a) *
          paperPhaseAmplitude precision ((((d*k.val)%r:Nat):ℝ)/(r:ℝ)) (fourierWordLSB b))) •
          pointCyclicState P (s[836 ↦ false]) k)
      (pointPhasePairSlice P Q precision a b) cs ∧ (cs.map Complex.normSq).sum=1 := by
  obtain ⟨cs,hcs,hcm⟩ := pointPhaseSlice_amplitude hr P horder s hs a
  obtain ⟨ds,hds,hdm⟩ := pointPhaseSlice_scaled_eigenstate hr P horder s hs d b
  rw [ha] at hcs
  rw [hb] at hds
  refine ⟨coherentSeqCoefficients cs ds,?_,by rw [pairCoefficients_mass,hcm,hdm,mul_one]⟩
  rw [pointPhasePairSlice,hQ,pointPhaseSlice_nsmul]
  exact pairAligned_seq _ _ _ hcs hds
theorem pointPhasePairSlice_mass {r : Nat} (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d precision : Nat) (hQ : Q=d • P) (a b : List Bool) (ha : a.length=precision) (hb : b.length=precision)
    (out : Fin (2^precision) × Fin (2^precision)) (hva : fourierWordLSB a=out.1.val)
    (hvb : fourierWordLSB b=out.2.val) :
    Instrument.bornMass (pointPhasePairSlice P Q precision a b)
      (ket (pointWrite 0 (s[836 ↦ false])))=paperPairMass r precision d out := by
  obtain ⟨cs,hcs,hm⟩ := pointPhasePairSlice_eigenstate hr P Q horder s hs d precision hQ a b ha hb
  let coeff (k : Fin r) := paperPhaseAmplitude precision ((k.val:ℝ)/(r:ℝ)) out.1.val *
    paperPhaseAmplitude precision ((((d*k.val)%r:Nat):ℝ)/(r:ℝ)) out.2.val
  rw [hva,hvb] at hcs
  have hnorm : Complex.normSq ((((Real.sqrt r)⁻¹:ℝ):ℂ))=1/(r:ℝ) := by simp [Complex.normSq_ofReal]
  have hstate : (∑ k : Fin r, (((Real.sqrt r)⁻¹:ℝ):ℂ) • pointCyclicState P (s[836 ↦ false]) k)=
      ket (pointWrite 0 (s[836 ↦ false])) := by
    rw [← Finset.smul_sum]
    simpa [pointCyclicState,pointCyclicBasis] using cyclicState_average hr (pointCyclicBasis P (s[836 ↦ false]))
  have hmass (branch : InstrumentBranch) (c : ℂ)
      (h : ∀ (k : Fin r), branch.kraus (pointCyclicState P (s[836 ↦ false]) k)=
        (c*coeff k) • pointCyclicState P (s[836 ↦ false]) k) :
      normSq (branch.kraus (ket (pointWrite 0 (s[836 ↦ false])))) =
        Complex.normSq c * paperPairMass r precision d out := by
    rw [← hstate]
    simp_rw [map_sum,map_smul,h,smul_smul]
    simp only [pointCyclicState]
    rw [cyclicState_mass hr _ (pointCyclicBasis_orthonormal P _ horder)]
    simp only [Complex.normSq_mul,hnorm,coeff,paperPairMass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have haligned : Instrument.bornMass (pointPhasePairSlice P Q precision a b)
      (ket (pointWrite 0 (s[836 ↦ false]))) =
      (cs.map Complex.normSq).sum * paperPairMass r precision d out := by
    clear hm
    generalize he : pointPhasePairSlice P Q precision a b = branches at hcs ⊢
    clear he
    induction hcs with
    | nil => simp [Instrument.bornMass]
    | @cons branch c branches cs h _ ih =>
      change normSq (branch.kraus _) + Instrument.bornMass branches _ =
        (Complex.normSq c+(cs.map Complex.normSq).sum)*paperPairMass r precision d out
      rw [hmass branch c h,ih]
      ring
  rw [haligned,hm,one_mul]
/-- Split the complete history using the first physical program, then decode each sample register. -/
def decodePointPhasePair (P Q : Secp256k1.Point) (precision : Nat) (hist : List Bool) :
    Option (List Bool × List Bool) := do
  let rest ← consumeAdaptiveHistory (pointPhaseSchedule P (pointPhasePowers precision) List.nil) hist
  let first ← decodePointPhaseSamples P (pointPhasePowers precision) (hist.take (hist.length-rest.length))
  let second ← decodePointPhaseSamples Q (pointPhasePowers precision) rest
  return (first,second)

theorem decodePointPhasePair_seq (P Q : Secp256k1.Point) (precision : Nat)
    (first second : InstrumentBranch)
    (hf : first∈(pointPhaseSchedule P (pointPhasePowers precision) List.nil).run) :
    decodePointPhasePair P Q precision (first.seq second).history = do
      let a ← decodePointPhaseSamples P (pointPhasePowers precision) first.history
      let b ← decodePointPhaseSamples Q (pointPhasePowers precision) second.history
      return (a,b) := by
  simp [decodePointPhasePair,InstrumentBranch.seq,consumeAdaptiveHistory_run _ first hf]
private theorem filterPairInstrument (xs ys : Instrument) (p q z : InstrumentBranch → Bool)
    (hz : ∀ x∈xs, ∀ y∈ys, z (x.seq y)=(p x && q y)) :
    Instrument.seq (xs.filter p) (ys.filter q)=(Instrument.seq xs ys).filter z := by
  induction xs with
  | nil => simp [Instrument.seq]
  | cons x xs ih =>
    have htail : ∀ a∈xs, ∀ y∈ys, z (a.seq y)=(p a && q y) := by
      intro a ha y hy
      exact hz a (by simp [ha]) y hy
    have hmap : ((ys.map x.seq).filter z) = if p x then (ys.filter q).map x.seq else [] := by
      rw [List.filter_map]
      have he : ys.filter (z ∘ x.seq)=ys.filter (fun y => p x && q y) := by
        apply List.filter_congr
        intro y hy
        exact hz x (by simp) y hy
      rw [he]
      cases p x <;> simp
    have iht := ih htail
    unfold Instrument.seq at iht
    cases hp : p x <;> simp [Instrument.seq,hp,hmap,iht]

theorem pointPhasePairSlice_run (P Q : Secp256k1.Point) (precision : Nat) (a b : List Bool) :
    pointPhasePairSlice P Q precision a b = (pointPhasePairProgram P Q precision).run.filter
      (fun branch => decodePointPhasePair P Q precision branch.history == some (a,b)) := by
  rw [pointPhasePairSlice,pointPhaseSlice_run,pointPhaseSlice_run,
    pointPhasePairProgram,AdaptiveCircuit.run_seq]
  apply filterPairInstrument
  intro first hf second _
  rw [decodePointPhasePair_seq P Q precision first second hf]
  cases decodePointPhaseSamples P (pointPhasePowers precision) first.history <;>
    cases decodePointPhaseSamples Q (pointPhasePowers precision) second.history <;> simp
  rfl
/-- The unique fixed-width output bits for a dyadic integer outcome. -/
def paperOutcomeBits (precision : Nat) (value : Fin (2^precision)) : List Bool :=
  (fourierWordLSB_surjective precision value.val value.isLt).choose
@[simp] theorem paperOutcomeBits_length (precision : Nat) (value : Fin (2^precision)) :
    (paperOutcomeBits precision value).length=precision :=
  (fourierWordLSB_surjective precision value.val value.isLt).choose_spec.1
@[simp] theorem paperOutcomeBits_word (precision : Nat) (value : Fin (2^precision)) :
    fourierWordLSB (paperOutcomeBits precision value)=value.val :=
  (fourierWordLSB_surjective precision value.val value.isLt).choose_spec.2

def physicalPairOutputMass (P Q : Secp256k1.Point) (precision : Nat)
    (out : Fin (2^precision) × Fin (2^precision)) (s : BasisState) : ℝ :=
  Instrument.bornMass ((pointPhasePairProgram P Q precision).run.filter
    (fun branch => decodePointPhasePair P Q precision branch.history ==
      some (paperOutcomeBits precision out.1,paperOutcomeBits precision out.2)))
    (ket (pointWrite 0 (s[836 ↦ false])))

theorem physicalPairOutputMass_eq {r : Nat} (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d precision : Nat) (hQ : Q=d • P) (out : Fin (2^precision) × Fin (2^precision)) :
    physicalPairOutputMass P Q precision out s=paperPairMass r precision d out := by
  unfold physicalPairOutputMass
  rw [← pointPhasePairSlice_run]
  exact pointPhasePairSlice_mass hr P Q horder s hs d precision hQ _ _
    (paperOutcomeBits_length _ _) (paperOutcomeBits_length _ _) out
    (paperOutcomeBits_word _ _) (paperOutcomeBits_word _ _)

def physicalPairSuccessMass (r : Nat) (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (d precision : Nat) (s : BasisState) : ℝ :=
  ∑ out : Fin (2^precision) × Fin (2^precision),
    if orderFindingPostprocess r precision hr out=some (d:ZMod r) then
      physicalPairOutputMass P Q precision out s else 0

theorem physicalPairSuccessMass_eq {r : Nat} (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d precision : Nat) (hQ : Q=d • P) :
    physicalPairSuccessMass r hr P Q d precision s=paperSuccessMass r precision d hr := by
  unfold physicalPairSuccessMass paperSuccessMass
  simp only [physicalPairOutputMass_eq hr P Q horder s hs d precision hQ]

/-- Same-program success mass after the canonical classical postprocessor. -/
theorem physicalPairSuccessMass_lower {r : Nat} (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d precision : Nat) (hQ : Q=d • P) (hprecision : r<2^precision) :
    (((r-1:Nat):ℝ)/(r:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ physicalPairSuccessMass r hr P Q d precision s := by
  rw [physicalPairSuccessMass_eq hr P Q horder s hs d precision hQ]
  exact paperSuccessMass_lower r precision d hr hprecision
theorem paperOutcomeBits_injective (precision : Nat) : Function.Injective (paperOutcomeBits precision) := by
  intro a b h
  apply Fin.ext
  have hw := congrArg fourierWordLSB h
  simpa only [paperOutcomeBits_word] using hw

/-- Distinct dyadic output events never count the same physical branch twice. -/
theorem physicalPairOutput_unique (P Q : Secp256k1.Point) (precision : Nat) (hist : List Bool)
    (a b : Fin (2^precision) × Fin (2^precision))
    (ha : decodePointPhasePair P Q precision hist=some (paperOutcomeBits precision a.1,paperOutcomeBits precision a.2))
    (hb : decodePointPhasePair P Q precision hist=some (paperOutcomeBits precision b.1,paperOutcomeBits precision b.2)) :
    a=b := by
  have h := Option.some.inj (ha.symm.trans hb)
  apply Prod.ext
  · exact paperOutcomeBits_injective precision (congrArg Prod.fst h)
  · exact paperOutcomeBits_injective precision (congrArg Prod.snd h)
end
end ShorECDLP.Paper2607_13816
