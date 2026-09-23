import ShorECDLP.Submission.«2607_13816».Window.RawStream
import ShorECDLP.Submission.«2607_13816».Window.RawFibers
/-! Conditional exceptional-input count for the MSB-first order. Logical banks
record the window assignments before physical reuse; this is not yet a Born
weight bound for the streaming circuit. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime order) := ⟨order_prime⟩

/-- Bank zero is the direct load. Banks 1..15 hold P14..P0 and 16..28 hold Q12..Q0. -/
def streamRawX (P Q : Point) (j : Nat) : Nat → ShorECDLP.Fp :=
  if j < 16 then oddWindowX P (15-j) else oddWindowX Q (28-j)
def streamRawY (P Q : Point) (j : Nat) : Nat → ShorECDLP.Fp :=
  if j < 16 then oddWindowY P (15-j) else oddWindowY Q (28-j)
theorem streamRawTable_valid (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (j a : Nat) :
    curve.toAffine.Nonsingular (streamRawX P Q j a) (streamRawY P Q j a) := by
  unfold streamRawX streamRawY
  split
  · exact oddWindowTable_valid P hP hrP _ _
  · exact oddWindowTable_valid Q hQ hrQ _ _

def streamRawInitialPoint (P Q : Point) (s : BasisState) : Point :=
  firstWindowTable (axisWindowOffset P 16 + axisWindowOffset Q 13)
    ((2^(16*15)) • P) (tableAddressValue streamAddress s)
def streamRawExclusions (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) : Prop :=
  rawAlgebraicExclusions (streamRawX P Q) (streamRawY P Q)
    (streamRawTable_valid P Q hP hQ hrP hrQ) (List.range' 1 28)
    (streamRawInitialPoint P Q s) s

/-- The physical bank-zero call selected by one logical MSB-first index. -/
def streamRawIndexedCall (P Q : Point) (j : Nat) : AdaptiveCircuit :=
  preparedRawProgram (fun _ a => (streamRawX P Q j a).val)
    (fun _ a => (streamRawY P Q j a).val) 0

theorem streamRawIndexedCall_left (P Q : Point) (j : Nat) (hj : j<16) :
    streamRawIndexedCall P Q j = streamRawCall P (15-j) := by
  simp only [streamRawIndexedCall,streamRawX,streamRawY,if_pos hj,streamRawCall]
theorem streamRawIndexedCall_right (P Q : Point) (j : Nat) (hj : 16≤j) :
    streamRawIndexedCall P Q j = streamRawCall Q (28-j) := by
  simp only [streamRawIndexedCall,streamRawX,streamRawY,if_neg (by omega : ¬j<16),streamRawCall]

/-- The counted tables have exactly the actual streaming call order; the first
logical bank is a direct lookup rather than a raw addition. -/
theorem streamRawIndexedCalls_order (P Q : Point) :
    physicalPointLookup (firstWindowTable (axisWindowOffset P 16 + axisWindowOffset Q 13)
      ((2^(16*15)) • P)) :: ((List.range' 1 28).map (streamRawIndexedCall P Q)) =
      streamRawLeftCalls P Q ++ streamRawRightCalls Q := by
  have hp : (List.range' 1 15).map (streamRawIndexedCall P Q) =
      (List.range 15).reverse.map (streamRawCall P) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have h : i<15 := by simpa using hi
      simp only [List.getElem_map,List.getElem_range',List.getElem_reverse,List.length_range,
        List.getElem_range,Nat.one_mul]
      rw [streamRawIndexedCall_left P Q (1+i) (by omega)]
      congr 1
      omega
  have hq : (List.range' 16 13).map (streamRawIndexedCall P Q) =
      (List.range 13).reverse.map (streamRawCall Q) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have h : i<13 := by simpa using hi
      simp only [List.getElem_map,List.getElem_range',List.getElem_reverse,List.length_range,
        List.getElem_range,Nat.one_mul]
      rw [streamRawIndexedCall_right P Q (16+i) (by omega)]
      congr 1
      omega
  have hr : List.range' 1 28 = List.range' 1 15 ++ List.range' 16 13 := by
    exact (List.range'_append (s := 1) (m := 15) (n := 13) (step := 1)).symm
  rw [hr,List.map_append,hp,hq]
  rfl

/-- The varying first word is injective even though its scalar weight is 2^240. -/
theorem streamRawFirstPoint_ne_zero (P : Point) (hP : P≠0) (hrP : order • P=0) :
    (2^(16*15):Nat) • P ≠ 0 := by
  have ho : addOrderOf P=order := addOrderOf_eq_prime hrP hP
  intro hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
  rw [ho] at hd
  have htwo := order_prime.dvd_of_dvd_pow hd
  have hle := Nat.le_of_dvd (by decide : 0<2) htwo
  norm_num [order] at hle

theorem streamRawInitialPoint_firstWord (P Q : Point) (a : Fin 65536) (s : BasisState) :
    streamRawInitialPoint P Q (rawFirstWordState a s) =
      a.val • ((2^(16*15):Nat) • P) +
        (axisWindowOffset P 16 + axisWindowOffset Q 13 +
          signedWindowHalfPoint ((2^(16*15):Nat) • P) order -
          (32768:ℤ) • ((2^(16*15):Nat) • P)) := by
  unfold streamRawInitialPoint streamAddress
  rw [rawFirstWordState_address]
  simp only [firstWindowTable,signedWindowDigit,sub_zsmul,natCast_zsmul]
  norm_num
  abel

/-- For every assignment of the other logical banks, at most 112 first-word
values violate the 28 MSB-first raw-addition exclusions. -/
theorem streamRawExclusions_firstWord_card (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    (Finset.univ.filter (fun a : Fin 65536 =>
      ¬streamRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s))).card ≤ 112 := by
  let R := (2^(16*15):Nat) • P
  let A := axisWindowOffset P 16 + axisWindowOffset Q 13 + signedWindowHalfPoint R order - (32768:ℤ) • R
  have hR : R≠0 := streamRawFirstPoint_ne_zero P hP hrP
  have hrR : order • R=0 := by
    dsimp [R]
    rw [smul_comm,hrP]
    exact nsmul_zero _
  have he (a : Fin 65536) : streamRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s) =
      rawAlgebraicExclusions (streamRawX P Q) (streamRawY P Q)
        (streamRawTable_valid P Q hP hQ hrP hrQ) (List.range' 1 28) (a.val • R + A) s := by
    unfold streamRawExclusions
    rw [rawAlgebraicExclusions_firstWord _ _ _ _ (by
      intro j hj; simp only [List.mem_range'_1] at hj; omega),streamRawInitialPoint_firstWord]
  simp only [he]
  have h := rawAlgebraicExclusions_card (streamRawX P Q) (streamRawY P Q)
    (streamRawTable_valid P Q hP hQ hrP hrQ) (List.range' 1 28)
    R hR hrR 65536 (by norm_num [order]) A s
  simpa only [List.length_range'] using h

/-- A conditional uniform-word fraction, not the weight of the adaptive quantum input. -/
theorem streamRawExclusions_firstWord_fraction (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    ((Finset.univ.filter (fun a : Fin 65536 =>
      ¬streamRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s))).card : ℝ)/65536 ≤ 7/4096 := by
  have h := streamRawExclusions_firstWord_card P Q hP hQ hrP hrQ s
  have hr : ((Finset.univ.filter (fun a : Fin 65536 =>
      ¬streamRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s))).card : ℝ) ≤ 112 := by
    exact_mod_cast h
  calc
    _ ≤ (112:ℝ)/65536 := div_le_div_of_nonneg_right hr (by norm_num)
    _ = 7/4096 := by norm_num
end
end ShorECDLP.Paper2607_13816
