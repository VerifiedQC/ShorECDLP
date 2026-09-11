import ShorECDLP.Math.BitcoinCurve
namespace ShorECDLP.Paper2607_13816
open scoped BigOperators
/-- Little-endian fixed-width radix windows, including leading zero windows. -/
def windowDigits (w : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | count+1, value => value % 2^w :: windowDigits w count (value / 2^w)

def windowValue (base : Nat) : List Nat → Nat
  | [] => 0
  | x::xs => x + base * windowValue base xs

def signedWindowDigit (w value : Nat) : Int := (value:Int) - (2^(w-1):Nat)

def signedWindowValue (base : Nat) : List Int → Int
  | [] => 0
  | x::xs => x + (base:Int) * signedWindowValue base xs

def windowOffset (w : Nat) : Nat → Int
  | 0 => 0
  | n+1 => (2^(w-1):Nat) + (2^w:Nat) * windowOffset w n

@[simp] theorem windowDigits_length (w count value : Nat) :
    (windowDigits w count value).length=count := by
  induction count generalizing value with
  | zero => rfl
  | succ n ih => simp [windowDigits,ih]

theorem windowDigits_bound (w count value digit : Nat) (h : digit∈windowDigits w count value) :
    digit<2^w := by
  induction count generalizing value with
  | zero => simp [windowDigits] at h
  | succ n ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.mod_lt _ (by positivity)
    · exact ih _ h

theorem windowValue_digits (w count value : Nat) (hv : value<(2^w)^count) :
    windowValue (2^w) (windowDigits w count value)=value := by
  induction count generalizing value with
  | zero =>
    simp only [pow_zero] at hv
    have hz : value=0 := by omega
    subst value
    rfl
  | succ n ih =>
    have hb : 0<2^w := by positivity
    have ht : value/2^w<(2^w)^n := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      simpa [pow_succ,Nat.mul_comm] using hv
    simp only [windowDigits,windowValue,ih _ ht]
    exact Nat.mod_add_div _ _

theorem signedWindowValue_map (w : Nat) (digits : List Nat) :
    signedWindowValue (2^w) (digits.map (signedWindowDigit w)) =
      (windowValue (2^w) digits:Int) - windowOffset w digits.length := by
  induction digits with
  | nil => simp [signedWindowValue,windowValue,windowOffset]
  | cons d ds ih =>
    simp only [List.map_cons,List.length_cons,signedWindowValue,windowValue,windowOffset,ih,signedWindowDigit]
    push_cast
    ring

theorem signedWindow_reconstruct (w count value : Nat) (hv : value<(2^w)^count) :
    signedWindowValue (2^w) ((windowDigits w count value).map (signedWindowDigit w)) +
      windowOffset w count = (value:Int) := by
  rw [signedWindowValue_map,windowDigits_length,windowValue_digits w count value hv]
  omega

theorem signedWindowDigit_bounds (w value : Nat) (hw : 0<w) (hv : value<2^w) :
    -(2^(w-1):Int) ≤ signedWindowDigit w value ∧ signedWindowDigit w value < (2^(w-1):Int) := by
  have hpow : 2^w=2*2^(w-1) := by
    conv_lhs => rw [show w=(w-1)+1 by omega,pow_succ]
    omega
  have hpow' : (2:ℤ)^w=2*2^(w-1) := by exact_mod_cast hpow
  have hv' : (value:ℤ)<(2:ℤ)^w := by exact_mod_cast hv
  unfold signedWindowDigit
  push_cast
  constructor <;> omega

/-- Each centered window adds a known, input-independent point offset. -/
theorem signedWindow_point {G : Type} [AddCommGroup G] (P : G) (w count value : Nat)
    (hv : value<(2^w)^count) :
    signedWindowValue (2^w) ((windowDigits w count value).map (signedWindowDigit w)) • P =
      value • P - windowOffset w count • P := by
  have h := signedWindow_reconstruct w count value hv
  have he : signedWindowValue (2^w) ((windowDigits w count value).map (signedWindowDigit w)) =
      (value:Int)-windowOffset w count := by omega
  rw [he,sub_zsmul]
  simp [sub_eq_add_neg]

/-- Both scalar registers retain their exact values up to one fixed initial point. -/
theorem signedWindow_doubleScalar {G : Type} [AddCommGroup G] (P Q : G)
    (w count a b : Nat) (ha : a<(2^w)^count) (hb : b<(2^w)^count) :
    signedWindowValue (2^w) ((windowDigits w count a).map (signedWindowDigit w)) • P +
      signedWindowValue (2^w) ((windowDigits w count b).map (signedWindowDigit w)) • Q +
      (windowOffset w count • P + windowOffset w count • Q) = a • P + b • Q := by
  rw [signedWindow_point P w count a ha,signedWindow_point Q w count b hb]
  abel

/-- The unshortened number of fixed-width windows, including a partial top window. -/
def windowCount (precision width : Nat) : Nat := (precision+width-1)/width

theorem windowCount_257_16 : windowCount 257 16 = 17 := by decide
theorem windowCount_256_16 : windowCount 256 16 = 16 := by decide

private theorem windowPower_cover (base bits width count : Nat) (hb : 0<base)
    (h : bits≤width*count) : base^bits≤(base^width)^count := by
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hb h

theorem signedWindow_secp257 {G : Type} [AddCommGroup G] (P Q : G)
    (a b : Nat) (ha : a<2^257) (hb : b<2^257) :
    signedWindowValue (2^16) ((windowDigits 16 17 a).map (signedWindowDigit 16)) • P +
      signedWindowValue (2^16) ((windowDigits 16 17 b).map (signedWindowDigit 16)) • Q +
      (windowOffset 16 17 • P + windowOffset 16 17 • Q) = a • P + b • Q := by
  have hp : (2:Nat)^257 ≤ (2^16)^17 := windowPower_cover 2 257 16 17 (by decide) (by decide)
  exact signedWindow_doubleScalar P Q 16 17 a b (lt_of_lt_of_le ha hp) (lt_of_lt_of_le hb hp)

theorem signedWindow_secp257_count (a b : Nat) :
    (windowDigits 16 17 a).length + (windowDigits 16 17 b).length = 34 := by
  simp
end ShorECDLP.Paper2607_13816
