import ShorECDLP.Submission.«2607_13816».Window.Preparation
import ShorECDLP.Math.EllipticCurve.GeneratorOrder
namespace ShorECDLP.Paper2607_13816
open ShorECDLP.Secp256k1
noncomputable section

def oddWindowPoint (P : Point) (j a : Nat) : Point :=
  (2*(a%32768)+1) • ((2^(16*j)) • signedWindowHalfPoint P order)

private theorem order_large : 65535<order := by norm_num [order]
private theorem order_odd : Odd order := by decide +kernel

theorem oddWindowPoint_ne_zero (P : Point) (hP : P≠0) (hr : order • P=0) (j a : Nat) :
    oddWindowPoint P j a≠0 := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf P=order := addOrderOf_eq_prime hr hP
  have hsmall : 0<2*(a%32768)+1 ∧ 2*(a%32768)+1<order := by
    have hb := Nat.mod_lt a (by decide : 0<32768)
    have hh := order_large
    omega
  have hhalf : 0<(order+1)/2 ∧ (order+1)/2<order := by have hh := order_large; omega
  have hnotodd : ¬order∣2*(a%32768)+1 := fun h => (Nat.le_of_dvd hsmall.1 h).not_gt hsmall.2
  have hnothalf : ¬order∣(order+1)/2 := fun h => (Nat.le_of_dvd hhalf.1 h).not_gt hhalf.2
  have hnottwo : ¬order∣2 := fun h => (Nat.le_of_dvd (by decide : 0<2) h).not_gt (by have hh := order_large; omega)
  intro hz
  have he : ((2*(a%32768)+1)*(2^(16*j))*((order+1)/2)) • P=0 := by
    simpa only [oddWindowPoint,signedWindowHalfPoint,smul_smul,Nat.mul_assoc] using hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  rw [ho] at hd
  rcases order_prime.dvd_mul.mp hd with hd | hd
  · rcases order_prime.dvd_mul.mp hd with hd | hd
    · exact hnotodd hd
    · exact hnottwo (order_prime.dvd_of_dvd_pow hd)
  · exact hnothalf hd
private def finiteCoordinates (P : Point) : ShorECDLP.Fp × ShorECDLP.Fp :=
  (coordinates P).getD (0,0)
private theorem finiteCoordinates_valid (P : Point) (hP : P≠0) :
    curve.toAffine.Nonsingular (finiteCoordinates P).1 (finiteCoordinates P).2 := by
  cases P with
  | zero => exact False.elim (hP rfl)
  | some h => exact h
private theorem finiteCoordinates_point (P : Point) (hP : P≠0) :
    WeierstrassCurve.Affine.Point.some (finiteCoordinates_valid P hP)=P := by
  cases P with
  | zero => exact False.elim (hP rfl)
  | some h => rfl

def oddWindowX (P : Point) (j a : Nat) : ShorECDLP.Fp := (finiteCoordinates (oddWindowPoint P j a)).1
def oddWindowY (P : Point) (j a : Nat) : ShorECDLP.Fp := (finiteCoordinates (oddWindowPoint P j a)).2

theorem oddWindowTable_valid (P : Point) (hP : P≠0) (hr : order • P=0) (j a : Nat) :
    curve.toAffine.Nonsingular (oddWindowX P j a) (oddWindowY P j a) :=
  finiteCoordinates_valid _ (oddWindowPoint_ne_zero P hP hr j a)

theorem oddWindowTable_point (P : Point) (hP : P≠0) (hr : order • P=0) (j a : Nat) :
    WeierstrassCurve.Affine.Point.some (oddWindowTable_valid P hP hr j a)=oddWindowPoint P j a :=
  finiteCoordinates_point _ (oddWindowPoint_ne_zero P hP hr j a)

private theorem rawDigit_low (j : Nat) (s : BasisState) :
    windowRawDigit j s<32768 ↔ s (windowBankStart j+15)=false := by
  have hb := boolWordToNat_lt_pow_two (wireValues (windowAddressBits j) s)
  simp only [wireValues,List.length_map,windowAddressBits,List.length_range'] at hb
  change boolWordToNat (wireValues (windowAddressBits j) s)<32768 at hb
  cases hh : s (windowBankStart j+15) <;> simp_all [windowRawDigit]

private theorem selected_oddWindow (P : Point)
    (k j : Nat) (s : BasisState) :
    (if s (windowBankStart j+15) then oddWindowPoint P k (signedTableAddress 32768 (windowRawDigit j s))
      else -oddWindowPoint P k (signedTableAddress 32768 (windowRawDigit j s)))=
    signedTableOdd 32768 (windowRawDigit j s) • ((2^(16*k)) • signedWindowHalfPoint P order) := by
  have ha := signedTableAddress_bound 32768 (windowRawDigit j s) (windowRawDigit_bound j s)
  simp only [oddWindowPoint,Nat.mod_eq_of_lt ha,signedTableOdd]
  cases hs : s (windowBankStart j+15)
  · rw [if_neg (by decide),if_pos ((rawDigit_low j s).mpr hs)]
    simp only [neg_zsmul,natCast_zsmul]
  · rw [if_pos rfl,if_neg (by intro h; have hh := (rawDigit_low j s).mp h; simp [hs] at hh)]
    simp only [natCast_zsmul]

private theorem oddWindow_digit (P : Point) (hr : order • P=0) (j value : Nat) :
    signedTableOdd 32768 value • ((2^(16*j)) • signedWindowHalfPoint P order)=
      signedWindowDigit 16 value • ((2^(16*j)) • P)+((2^(16*j)) • signedWindowHalfPoint P order) := by
  have hd : (2^(16*j)) • signedWindowHalfPoint P order+(2^(16*j)) • signedWindowHalfPoint P order=
      (2^(16*j)) • P := by
    rw [←nsmul_add,signedWindowHalfPoint_double P order order_odd hr]
  have h := signedTable_point ((2^(16*j)) • signedWindowHalfPoint P order) 32768 value
  rw [hd] at h
  exact sub_eq_iff_eq_add.mp h

theorem preparedOddWindowCall_correct (P : Point) (hP : P≠0) (hr : order • P=0)
    (j : Nat) (A : Point) (s : BasisState) (hs : PointLookupValid s)
    (hA : pointStateCoordinates s=fig14PointEncoding A) :
    preparedWindowCallState (oddWindowX P) (oddWindowY P) (oddWindowTable_valid P hP hr) j s=
      pointWrite (A+(signedWindowDigit 16 (windowRawDigit j s) • ((2^(16*j)) • P)+
        (2^(16*j)) • signedWindowHalfPoint P order)) s := by
  rw [preparedWindowCallState_selected _ _ _ j A s hs hA]
  rw [oddWindowTable_point P hP hr j (signedTableAddress 32768 (windowRawDigit j s))]
  rw [selected_oddWindow P j j s,oddWindow_digit P hr j (windowRawDigit j s)]

/-- An axis may begin at a later physical bank while its radix exponent starts at zero. -/
theorem preparedOddWindowCallAt_correct (P : Point) (hP : P≠0) (hr : order • P=0)
    (start j : Nat) (A : Point) (s : BasisState) (hs : PointLookupValid s)
    (hA : pointStateCoordinates s=fig14PointEncoding A) :
    preparedWindowCallState (fun k => oddWindowX P (k-start)) (fun k => oddWindowY P (k-start))
      (fun k => oddWindowTable_valid P hP hr (k-start)) j s=
      pointWrite (A+(signedWindowDigit 16 (windowRawDigit j s) • ((2^(16*(j-start))) • P)+
        (2^(16*(j-start))) • signedWindowHalfPoint P order)) s := by
  rw [preparedWindowCallState_selected _ _ _ j A s hs hA]
  rw [oddWindowTable_point P hP hr (j-start) (signedTableAddress 32768 (windowRawDigit j s))]
  rw [selected_oddWindow P (j-start) j s,oddWindow_digit P hr (j-start) (windowRawDigit j s)]

end
end ShorECDLP.Paper2607_13816
