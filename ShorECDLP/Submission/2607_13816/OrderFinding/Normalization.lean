import ShorECDLP.Submission.«2607_13816».OrderFinding.PhysicalPair
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
private theorem phaseBinary_mass (u : ℂ) (hu : Complex.normSq u=1) :
    Complex.normSq ((1/2:ℂ)*(1+u)) + Complex.normSq ((1/2:ℂ)*(1-u))=1 := by
  have h : Complex.normSq (1+u)+Complex.normSq (1-u)=2*(1+Complex.normSq u) := by
    simp [Complex.normSq_apply]
    ring
  simp only [Complex.normSq_mul]
  norm_num
  rw [← mul_add,h,hu]
  norm_num
private def phaseOne (phase : ℝ) (prior : List Bool) (n : Nat) (b : Bool) : ℂ :=
  (((Real.sqrt 2)⁻¹:ℝ):ℂ) * (xResetCoeff b false + eigenvalue (phase*(2:ℝ)^n) *
    Complex.exp (Complex.I*(fourierHistoryAngle .inverse prior 2:ℂ)) * xResetCoeff b true)
private theorem phaseOne_mass (phase : ℝ) (prior : List Bool) (n : Nat) :
    Complex.normSq (phaseOne phase prior n false) + Complex.normSq (phaseOne phase prior n true)=1 := by
  let u := eigenvalue (phase*(2:ℝ)^n) * Complex.exp (Complex.I*(fourierHistoryAngle .inverse prior 2:ℂ))
  have hn (θ : ℝ) : Complex.normSq (eigenvalue θ)=1 := by
    have he : eigenvalue θ=Complex.exp (Complex.I*((2*Real.pi*θ:ℝ):ℂ)) := by
      unfold eigenvalue
      push_cast
      rfl
    rw [he,Complex.normSq_eq_norm_sq,Complex.norm_exp_I_mul_ofReal]
    norm_num
  have hu : Complex.normSq u=1 := by
    rw [Complex.normSq_mul,hn,one_mul,Complex.normSq_eq_norm_sq,Complex.norm_exp_I_mul_ofReal]
    norm_num
  have h : ((((Real.sqrt 2)⁻¹:ℝ):ℂ))^2=(1/2:ℂ) := by
    rw [← Complex.ofReal_pow,inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  push_cast at h
  have hf : phaseOne phase prior n false=(1/2:ℂ)*(1+u) := by
    simp [phaseOne,xResetCoeff,u]
    linear_combination h * (1+u)
  have ht : phaseOne phase prior n true=(1/2:ℂ)*(1-u) := by
    simp [phaseOne,xResetCoeff,u]
    linear_combination h * (1-u)
  rw [hf,ht]
  exact phaseBinary_mass u hu

theorem phaseProduct_totalMass (phase : ℝ) (prior : List Bool) (n : Nat) :
    ((fourierOutcomes n).map (fun bs => Complex.normSq (phaseProduct phase prior bs))).sum=1 := by
  induction n generalizing prior with
  | zero => simp [fourierOutcomes,phaseProduct]
  | succ n ih =>
    have hmap (b : Bool) :
        (((fourierOutcomes n).map (b::·)).map (fun bs => Complex.normSq (phaseProduct phase prior bs))).sum =
          Complex.normSq (phaseOne phase prior n b) *
            ((fourierOutcomes n).map (fun bs => Complex.normSq (phaseProduct phase (b::prior) bs))).sum := by
      rw [List.map_map,← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro bs hbs
      have hl := (fourierOutcomes_mem n bs).mp hbs
      simp only [Function.comp_apply,phaseProduct,Complex.normSq_mul]
      rw [hl]
      simp only [phaseOne,Complex.normSq_mul]
    rw [fourierOutcomes,List.map_append,List.sum_append,hmap,hmap,ih,ih,mul_one,mul_one]
    exact phaseOne_mass phase prior n
theorem paperPhaseAmplitude_totalMass (phase : ℝ) (n : Nat) :
    ∑ v : Fin (2^n), Complex.normSq (paperPhaseAmplitude n phase v.val) = 1 := by
  rw [← phaseProduct_totalMass phase List.nil n,
    ← List.sum_toFinset _ (fourierOutcomes_nodup n)]
  apply Finset.sum_bij (fun v _ => paperOutcomeBits n v)
  · intro v hv
    exact List.mem_toFinset.mpr ((fourierOutcomes_mem n _).mpr (paperOutcomeBits_length n v))
  · intro a ha b hb h
    exact paperOutcomeBits_injective n h
  · intro bs hbs
    have hl := (fourierOutcomes_mem n bs).mp (List.mem_toFinset.mp hbs)
    have hv : fourierWordLSB bs < 2^n := by simpa [hl] using fourierWordLSB_lt bs
    refine ⟨⟨fourierWordLSB bs,hv⟩,Finset.mem_univ _,?_⟩
    apply fourierWordLSB_injective _ _
    · rw [paperOutcomeBits_length,hl]
    · exact paperOutcomeBits_word n _
  · intro v hv
    rw [phaseProduct_eq_amplitude,paperOutcomeBits_length,paperOutcomeBits_word]

theorem paperPairMass_total (r n d : Nat) (hr : 0 < r) :
    ∑ out : Fin (2^n) × Fin (2^n), paperPairMass r n d out = 1 := by
  unfold paperPairMass
  rw [← Finset.mul_sum,Finset.sum_comm]
  have h (k : Fin r) :
      ∑ out : Fin (2^n) × Fin (2^n),
        Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) out.1.val) *
        Complex.normSq (paperPhaseAmplitude n ((((d*k.val)%r:Nat):ℝ)/r) out.2.val)=1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,paperPhaseAmplitude_totalMass,mul_one]
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hr' : (r:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hr
  exact one_div_mul_cancel hr'

theorem paperOutcomeBits_of_word (n : Nat) (bs : List Bool) (hl : bs.length=n) :
    ∃ v : Fin (2^n), paperOutcomeBits n v=bs := by
  have hv : fourierWordLSB bs < 2^n := by simpa [hl] using fourierWordLSB_lt bs
  refine ⟨⟨fourierWordLSB bs,hv⟩,?_⟩
  apply fourierWordLSB_injective _ _
  · rw [paperOutcomeBits_length,hl]
  · exact paperOutcomeBits_word n _

theorem pointPhaseSchedule_decode_complete (P : Secp256k1.Point) (n : Nat)
    (branch : InstrumentBranch)
    (hb : branch∈(pointPhaseSchedule P (pointPhasePowers n) List.nil).run) :
    ∃ v : Fin (2^n), decodePointPhaseSamples P (pointPhasePowers n) branch.history =
      some (paperOutcomeBits n v) := by
  rw [← pointPhaseRecords_run] at hb
  obtain ⟨record,hr,rfl⟩ := List.mem_map.mp hb
  have hl := pointPhaseRecords_length P (pointPhasePowers n) List.nil record hr
  rw [pointPhasePowers_length] at hl
  obtain ⟨v,hv⟩ := paperOutcomeBits_of_word n record.samples hl
  exact ⟨v,by rw [hv]; exact pointPhaseRecords_decode P _ List.nil record hr⟩

theorem pointPhasePair_decode_complete (P Q : Secp256k1.Point) (n : Nat)
    (branch : InstrumentBranch) (hb : branch∈(pointPhasePairProgram P Q n).run) :
    ∃ out : Fin (2^n) × Fin (2^n), decodePointPhasePair P Q n branch.history =
      some (paperOutcomeBits n out.1,paperOutcomeBits n out.2) := by
  rw [pointPhasePairProgram,AdaptiveCircuit.run_seq] at hb
  obtain ⟨first,hf,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨second,hs,rfl⟩ := List.mem_map.mp hb
  obtain ⟨a,ha⟩ := pointPhaseSchedule_decode_complete P n first hf
  obtain ⟨b,hb⟩ := pointPhaseSchedule_decode_complete Q n second hs
  refine ⟨(a,b),?_⟩
  rw [decodePointPhasePair_seq P Q n first second hf,ha,hb]
  rfl

private theorem sum_decoded_mass {α : Type} [Fintype α] [DecidableEq α]
    (branches : Instrument) (decode : InstrumentBranch → Option α) (ψ : Quantum.State)
    (hc : ∀ branch∈branches, ∃ a, decode branch=some a) :
    ∑ a : α, Instrument.bornMass (branches.filter (fun b => decide (decode b=some a))) ψ =
      Instrument.bornMass branches ψ := by
  induction branches with
  | nil => simp [Instrument.bornMass]
  | cons branch branches ih =>
    obtain ⟨a,ha⟩ := hc branch (by simp)
    have ht : ∀ b∈branches, ∃ a, decode b=some a := fun b hb => hc b (by simp [hb])
    have he (v : α) : Instrument.bornMass
        ((branch::branches).filter (fun b => decide (decode b=some v))) ψ =
        (if a=v then normSq (branch.kraus ψ) else 0) +
          Instrument.bornMass (branches.filter (fun b => decide (decode b=some v))) ψ := by
      by_cases h : a=v
      · subst v; simp [ha,Instrument.bornMass]
      · simp [ha,h,Instrument.bornMass]
    simp_rw [he]
    rw [Finset.sum_add_distrib,ih ht]
    simp [Instrument.bornMass]

/-- The numerical decoder for every actual paired-program branch. -/
def decodePhysicalPairOutcome (P Q : Secp256k1.Point) (n : Nat) (branch : InstrumentBranch) :
    Option (Fin (2^n) × Fin (2^n)) :=
  if h : ∃ out : Fin (2^n) × Fin (2^n), decodePointPhasePair P Q n branch.history=
      some (paperOutcomeBits n out.1,paperOutcomeBits n out.2)
  then some h.choose else none

theorem decodePhysicalPairOutcome_eq (P Q : Secp256k1.Point) (n : Nat)
    (branch : InstrumentBranch) (out : Fin (2^n) × Fin (2^n)) :
    decodePhysicalPairOutcome P Q n branch=some out ↔
      decodePointPhasePair P Q n branch.history=some (paperOutcomeBits n out.1,paperOutcomeBits n out.2) := by
  unfold decodePhysicalPairOutcome
  split
  · rename_i h
    constructor
    · intro he
      have he' : h.choose=out := Option.some.inj he
      exact he' ▸ h.choose_spec
    · intro he
      congr 1
      exact physicalPairOutput_unique P Q n branch.history h.choose out h.choose_spec he
  · rename_i h
    constructor
    · simp
    · intro he; exact (h ⟨out,he⟩).elim

theorem physicalPairOutputMass_partition (P Q : Secp256k1.Point) (n : Nat) (s : BasisState) :
    ∑ out : Fin (2^n) × Fin (2^n), physicalPairOutputMass P Q n out s =
      Instrument.bornMass (pointPhasePairProgram P Q n).run (ket (pointWrite 0 (s[836 ↦ false]))) := by
  have hc (b : InstrumentBranch) (hb : b∈(pointPhasePairProgram P Q n).run) :
      ∃ out, decodePhysicalPairOutcome P Q n b=some out := by
    obtain ⟨out,ho⟩ := pointPhasePair_decode_complete P Q n b hb
    exact ⟨out,(decodePhysicalPairOutcome_eq P Q n b out).mpr ho⟩
  have h := sum_decoded_mass (pointPhasePairProgram P Q n).run (decodePhysicalPairOutcome P Q n)
    (ket (pointWrite 0 (s[836 ↦ false]))) hc
  have hp (out : Fin (2^n) × Fin (2^n)) :
      (fun b : InstrumentBranch => decide (decodePhysicalPairOutcome P Q n b=some out)) =
      (fun b : InstrumentBranch => decodePointPhasePair P Q n b.history ==
        some (paperOutcomeBits n out.1,paperOutcomeBits n out.2)) := by
    funext b
    apply Bool.eq_iff_iff.mpr
    simp [decodePhysicalPairOutcome_eq]
  simp only [hp] at h
  exact h

theorem physicalPairOutputMass_total {r : Nat} (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d n : Nat) (hQ : Q=d • P) :
    ∑ out : Fin (2^n) × Fin (2^n), physicalPairOutputMass P Q n out s = 1 := by
  simp only [physicalPairOutputMass_eq hr P Q horder s hs d n hQ]
  exact paperPairMass_total r n d hr.pos

/-- The complete actual adaptive program has total Born mass one on the identity input. -/
theorem pointPhasePairProgram_normalized {r : Nat} (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d n : Nat) (hQ : Q=d • P) :
    Instrument.bornMass (pointPhasePairProgram P Q n).run (ket (pointWrite 0 (s[836 ↦ false])))=1 := by
  rw [← physicalPairOutputMass_partition]
  exact physicalPairOutputMass_total hr P Q horder s hs d n hQ

theorem physicalPairSuccessMass_le_one {r : Nat} (hr : Nat.Prime r) (P Q : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (d n : Nat) (hQ : Q=d • P) : physicalPairSuccessMass r hr P Q d n s ≤ 1 := by
  rw [← physicalPairOutputMass_total hr P Q horder s hs d n hQ]
  unfold physicalPairSuccessMass
  apply Finset.sum_le_sum
  intro out _
  split
  · exact le_rfl
  · rw [physicalPairOutputMass_eq hr P Q horder s hs d n hQ]
    exact paperPairMass_nonneg r n d out

end
end ShorECDLP.Paper2607_13816
