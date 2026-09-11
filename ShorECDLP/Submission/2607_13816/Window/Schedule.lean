import ShorECDLP.Submission.«2607_13816».Window.AddressBank
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

def windowBankStart (j : Nat) : Nat := 855+16*j
private theorem windowBankStart_ge (j : Nat) : 855≤windowBankStart j := by unfold windowBankStart; omega

def windowPointDelta (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (s : BasisState) : ShorECDLP.Secp256k1.Point :=
  if s (windowBankStart j+15) then .some (hc j (tableAddressValue (List.range' (windowBankStart j) 15) s))
  else -(.some (hc j (tableAddressValue (List.range' (windowBankStart j) 15) s)))

def windowCall (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat) : AdaptiveCircuit :=
  parkedWindowProgram (windowBankStart j) (windowBankStart_ge j) (x j) (y j) (hc j)
def windowCallState (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat) : BasisState → BasisState :=
  parkedWindowState (windowBankStart j) (windowBankStart_ge j) (x j) (y j) (hc j)

def WindowPointValid (s : BasisState) : Prop :=
  PointLookupValid s ∧ ∃ P, pointStateCoordinates s=fig14PointEncoding P

theorem windowCallState_correct (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hp : pointStateCoordinates s=fig14PointEncoding P) :
    windowCallState x y hc j s=pointWrite (P+windowPointDelta x y hc j s) s :=
  parkedWindowState_bank_correct _ _ _ _ _ P s hs hp

theorem windowCallState_ready (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (s : BasisState) (hs : WindowPointValid s) : WindowPointValid (windowCallState x y hc j s) := by
  obtain ⟨hv,P,hp⟩ := hs
  rw [windowCallState_correct x y hc j P s hv hp]
  exact ⟨⟨pointWrite_valid _ s hv.1,(pointWrite_frame _ s 836 (by decide +kernel)).trans hv.2⟩,
    _,pointWrite_coordinates _ s⟩
private theorem windowCall_coherent (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat) :
    CoherentlyImplementsOn (windowCall x y hc j) (Finsupp.lmapDomain ℂ ℂ (windowCallState x y hc j)) WindowPointValid := by
  obtain ⟨cs,ha,hm⟩ := parkedWindowProgram_coherent (windowBankStart j) (windowBankStart_ge j) (x j) (y j) (hc j)
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s hs.1),hm⟩

def windowSchedule (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) : Nat → Nat → AdaptiveCircuit
  | 0, _ => .done
  | n+1, j => (windowCall x y hc j).seq (windowSchedule x y hc n (j+1))
def windowScheduleState (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) : Nat → Nat → BasisState → BasisState
  | 0, _, s => s
  | n+1, j, s => windowScheduleState x y hc n (j+1) (windowCallState x y hc j s)

theorem windowScheduleState_ready (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (s : BasisState) (hs : WindowPointValid s) : WindowPointValid (windowScheduleState x y hc n j s) := by
  induction n generalizing j s with
  | zero => exact hs
  | succ n ih => exact ih _ _ (windowCallState_ready x y hc j s hs)

theorem windowSchedule_coherent (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    CoherentlyImplementsOn (windowSchedule x y hc n j)
      (Finsupp.lmapDomain ℂ ℂ (windowScheduleState x y hc n j)) WindowPointValid := by
  induction n generalizing j with
  | zero =>
    refine ⟨[1],?_,by simp⟩
    simp only [windowSchedule,AdaptiveCircuit.run]
    apply List.Forall₂.cons
    · intro s hs; simp [windowScheduleState,ket]
    · exact .nil
  | succ n ih =>
    have h := (windowCall_coherent x y hc j).seq (ih (j+1)) (by
      intro s hs
      simpa [ket] using supportedOn_ket _ _ (windowCallState_ready x y hc j s hs))
    apply h.congrIdeal
    intro s hs
    simp [LinearMap.comp_apply,ket,windowScheduleState]
private theorem high_not_point (w : Wire) (hw : 839≤w) : w∉pointLogicalWires := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1]
  dsimp only [Wire] at *
  omega
private theorem delta_pointWrite (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    windowPointDelta x y hc j (pointWrite P s)=windowPointDelta x y hc j s := by
  have hs : pointWrite P s (windowBankStart j+15)=s (windowBankStart j+15) :=
    pointWrite_frame P s _ (high_not_point _ (by unfold windowBankStart; dsimp only [Wire]; omega))
  have ha : tableAddressValue (List.range' (windowBankStart j) 15) (pointWrite P s)=
      tableAddressValue (List.range' (windowBankStart j) 15) s := by
    apply tableAddressValue_congr
    intro w hw
    apply pointWrite_frame P s w
    apply high_not_point w
    simp only [List.mem_range'_1,windowBankStart] at hw
    dsimp only [Wire] at *
    omega
  simp only [windowPointDelta,hs,ha]
def windowPointSum (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) : Nat → Nat → BasisState → ShorECDLP.Secp256k1.Point
  | 0, _, _ => 0
  | n+1, j, s => windowPointDelta x y hc j s+windowPointSum x y hc n (j+1) s
private theorem sum_pointWrite (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    windowPointSum x y hc n j (pointWrite P s)=windowPointSum x y hc n j s := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [windowPointSum,delta_pointWrite,ih]
private theorem pointWrite_self (P : ShorECDLP.Secp256k1.Point) (s : BasisState)
    (hs : PointLookupValid s) (hp : pointStateCoordinates s=fig14PointEncoding P) : s=pointWrite P s := by
  have hw := pointStateCoordinates_word s hs.1
  rw [hp] at hw
  have he := hw.trans (pointWrite_word P s).symm
  funext w
  by_cases hm : w∈pointLogicalWires
  · exact List.map_inj_left.mp he w hm
  · exact (pointWrite_frame P s w hm).symm

theorem windowScheduleState_correct (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hp : pointStateCoordinates s=fig14PointEncoding P) :
    windowScheduleState x y hc n j s=pointWrite (P+windowPointSum x y hc n j s) s := by
  induction n generalizing j P s with
  | zero => simpa only [windowScheduleState,windowPointSum,add_zero] using pointWrite_self P s hs hp
  | succ n ih =>
    have he := windowCallState_correct x y hc j P s hs hp
    have hv := (windowCallState_ready x y hc j s ⟨hs,P,hp⟩).1
    have hp' : pointStateCoordinates (windowCallState x y hc j s)=fig14PointEncoding (P+windowPointDelta x y hc j s) := by
      rw [he,pointWrite_coordinates]
    rw [windowScheduleState,ih (j+1) _ _ hv hp',he,sum_pointWrite,pointWrite_overwrite,windowPointSum,add_assoc]

theorem windowSchedule_support (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    (windowSchedule x y hc n j).wires ⊆ List.range 839++List.range' 855 (16*(j+n)) := by
  induction n generalizing j with
  | zero => simp [windowSchedule,AdaptiveCircuit.wires]
  | succ n ih =>
    intro w hw
    rw [windowSchedule,modularWires_seq] at hw
    rcases hw with hw | hw
    · have hb := parkedWindowProgram_tight_support (windowBankStart j) (windowBankStart_ge j) (x j) (y j) (hc j) hw
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append_left _ hb
      · apply List.mem_append_right
        simp only [List.mem_range'_1,windowBankStart] at hb ⊢
        dsimp only [Wire] at *
        omega
    · have ht := ih (j+1) hw
      simpa only [show j+1+n=j+(n+1) by omega] using ht

theorem windowSchedule_qubitCount (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    (windowSchedule x y hc n j).qubitCount≤839+16*(j+n) := by
  have hs : (windowSchedule x y hc n j).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 (16*(j+n))).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (windowSchedule_support x y hc n j (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

theorem windowSchedule_34_qubitCount (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) :
    (windowSchedule x y hc 34 0).qubitCount≤1383 :=
  windowSchedule_qubitCount x y hc 34 0

end
end ShorECDLP.Paper2607_13816
