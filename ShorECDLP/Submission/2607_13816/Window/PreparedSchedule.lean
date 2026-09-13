import ShorECDLP.Submission.«2607_13816».Window.Preparation
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

def preparedWindowDelta (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (s : BasisState) : ShorECDLP.Secp256k1.Point :=
  windowPointDelta x y hc j (windowPrepareState j s)
def preparedWindowSchedule (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) : Nat → Nat → AdaptiveCircuit
  | 0, _ => .done
  | n+1, j => (preparedWindowCall x y hc j).seq (preparedWindowSchedule x y hc n (j+1))
def preparedWindowScheduleState (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) : Nat → Nat → BasisState → BasisState
  | 0, _, s => s
  | n+1, j, s => preparedWindowScheduleState x y hc n (j+1) (preparedWindowCallState x y hc j s)

theorem preparedWindowScheduleState_ready (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (s : BasisState) (hs : WindowPointValid s) : WindowPointValid (preparedWindowScheduleState x y hc n j s) := by
  induction n generalizing j s with
  | zero => exact hs
  | succ n ih => exact ih _ _ (preparedWindowCallState_ready x y hc j s hs)

theorem preparedWindowSchedule_coherent (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    CoherentlyImplementsOn (preparedWindowSchedule x y hc n j)
      (Finsupp.lmapDomain ℂ ℂ (preparedWindowScheduleState x y hc n j)) WindowPointValid := by
  induction n generalizing j with
  | zero =>
    refine ⟨[1],?_,by simp⟩
    simp only [preparedWindowSchedule,AdaptiveCircuit.run]
    apply List.Forall₂.cons
    · intro s hs; simp [preparedWindowScheduleState,ket]
    · exact .nil
  | succ n ih =>
    have h := (preparedWindowCall_coherent x y hc j).seq (ih (j+1)) (by
      intro s hs
      simpa [ket] using supportedOn_ket _ _ (preparedWindowCallState_ready x y hc j s hs))
    apply h.congrIdeal
    intro s hs
    simp [LinearMap.comp_apply,ket,preparedWindowScheduleState]
private theorem high_not_point (w : Wire) (hw : 839≤w) : w∉pointLogicalWires := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1]
  dsimp only [Wire] at *
  omega
private theorem raw_delta_pointWrite (x y : Nat → Nat → ShorECDLP.Fp)
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
private theorem delta_pointWrite (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    preparedWindowDelta x y hc j (pointWrite P s)=preparedWindowDelta x y hc j s := by
  rw [preparedWindowDelta,windowPrepareState_pointWrite,raw_delta_pointWrite]
  rfl
def preparedWindowSum (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) : Nat → Nat → BasisState → ShorECDLP.Secp256k1.Point
  | 0, _, _ => 0
  | n+1, j, s => preparedWindowDelta x y hc j s+preparedWindowSum x y hc n (j+1) s
private theorem sum_pointWrite (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    preparedWindowSum x y hc n j (pointWrite P s)=preparedWindowSum x y hc n j s := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [preparedWindowSum,delta_pointWrite,ih]
private theorem pointWrite_self (P : ShorECDLP.Secp256k1.Point) (s : BasisState)
    (hs : PointLookupValid s) (hp : pointStateCoordinates s=fig14PointEncoding P) : s=pointWrite P s := by
  have hw := pointStateCoordinates_word s hs.1
  rw [hp] at hw
  have he := hw.trans (pointWrite_word P s).symm
  funext w
  by_cases hm : w∈pointLogicalWires
  · exact List.map_inj_left.mp he w hm
  · exact (pointWrite_frame P s w hm).symm

theorem preparedWindowScheduleState_correct (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (n j : Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (hs : PointLookupValid s)
    (hp : pointStateCoordinates s=fig14PointEncoding P) :
    preparedWindowScheduleState x y hc n j s=pointWrite (P+preparedWindowSum x y hc n j s) s := by
  induction n generalizing j P s with
  | zero => simpa only [preparedWindowScheduleState,preparedWindowSum,add_zero] using pointWrite_self P s hs hp
  | succ n ih =>
    have he := preparedWindowCallState_correct x y hc j P s hs hp
    have hv := (preparedWindowCallState_ready x y hc j s ⟨hs,P,hp⟩).1
    have hp' : pointStateCoordinates (preparedWindowCallState x y hc j s)=fig14PointEncoding (P+preparedWindowDelta x y hc j s) := by
      rw [he,pointWrite_coordinates]
      rfl
    rw [preparedWindowScheduleState,ih (j+1) _ _ hv hp',he,sum_pointWrite,pointWrite_overwrite,preparedWindowSum,add_assoc]

theorem preparedWindowSchedule_support (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    (preparedWindowSchedule x y hc n j).wires ⊆ List.range 839++List.range' 855 (16*(j+n)) := by
  induction n generalizing j with
  | zero => simp [preparedWindowSchedule,AdaptiveCircuit.wires]
  | succ n ih =>
    intro w hw
    rw [preparedWindowSchedule,modularWires_seq] at hw
    rcases hw with hw | hw
    · have hb := preparedWindowCall_support x y hc j hw
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append_left _ hb
      · apply List.mem_append_right
        simp only [List.mem_range'_1,windowBankStart] at hb ⊢
        dsimp only [Wire] at *
        omega
    · have ht := ih (j+1) hw
      simpa only [show j+1+n=j+(n+1) by omega] using ht

theorem preparedWindowSchedule_qubitCount (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    (preparedWindowSchedule x y hc n j).qubitCount≤839+16*(j+n) := by
  have hs : (preparedWindowSchedule x y hc n j).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 (16*(j+n))).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (preparedWindowSchedule_support x y hc n j (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

theorem preparedWindowSchedule_34_qubitCount (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) :
    (preparedWindowSchedule x y hc 34 0).qubitCount≤1383 :=
  preparedWindowSchedule_qubitCount x y hc 34 0

end
end ShorECDLP.Paper2607_13816
