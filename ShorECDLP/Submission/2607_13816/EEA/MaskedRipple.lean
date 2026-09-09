import ShorECDLP.Submission.«2607_13816».EEA.RippleArithmetic

/-! # Two-pass ripple fusion with a separate control for every bit

Lists are most-significant-bit first. The first pass visits the tail before the
head; the second visits the head before the tail. These are word-level state
functions; the physical interval-to-word connection is separate.
-/
namespace ShorECDLP.Paper2607_13816
open Classical

def maskedRippleFirstWords (mode : RippleMode) :
    List Bool → List Bool → List Bool → Bool → List Bool × List Bool × Bool
  | e :: es, t :: ts, a :: ads, carry =>
    let rest := maskedRippleFirstWords mode es ts ads carry
    let cell := rippleFirstBits mode e ⟨t, a, rest.2.2⟩
    (cell.target :: rest.1, cell.addend :: rest.2.1, cell.carry)
  | _, ts, ads, carry => (ts, ads, carry)

def maskedRippleSecondWords (mode : RippleMode) :
    List Bool → List Bool → List Bool → Bool → List Bool × List Bool × Bool
  | e :: es, t :: ts, a :: ads, carry =>
    let cell := rippleSecondBits mode e ⟨t, a, carry⟩
    let rest := maskedRippleSecondWords mode es ts ads cell.carry
    (cell.target :: rest.1, cell.addend :: rest.2.1, rest.2.2)
  | _, ts, ads, carry => (ts, ads, carry)

def maskedRippleExpectedWords (mode : RippleMode) :
    List Bool → List Bool → List Bool → Bool → List Bool × Bool
  | e :: es, t :: ts, a :: ads, carry =>
    let rest := maskedRippleExpectedWords mode es ts ads carry
    ((if e then t ^^ a ^^ rest.2 else t) :: rest.1,
      (rippleFirstBits mode e ⟨t, a, rest.2⟩).carry)
  | _, ts, _, carry => (ts, carry)

/-- Matching per-bit controls fuse both passes, restoring the addend and incoming carry.
Disabled first-pass cells are retained: their temporary writes cancel in the second pass. -/
theorem maskedRippleWords_fusion (mode : RippleMode) (es ts ads : List Bool) (carry : Bool)
    (he : es.length = ts.length) (ha : ts.length = ads.length) :
    let first := maskedRippleFirstWords mode es ts ads carry
    let second := maskedRippleSecondWords mode es first.1 first.2.1 first.2.2
    second = ((maskedRippleExpectedWords mode es ts ads carry).1, ads, carry) ∧
      first.2.2 = (maskedRippleExpectedWords mode es ts ads carry).2 := by
  induction es generalizing ts ads carry with
  | nil =>
    have ht : ts = [] := List.eq_nil_of_length_eq_zero he.symm
    subst ts
    have ha' : ads = [] := List.eq_nil_of_length_eq_zero ha.symm
    subst ads
    exact ⟨rfl,rfl⟩
  | cons e es ih =>
    cases ts with
    | nil => simp at he
    | cons t ts =>
      cases ads with
      | nil => simp at ha
      | cons a ads =>
        have hr := ih ts ads carry (by simpa using he) (by simpa using ha)
        dsimp only at hr ⊢
        simp only [maskedRippleFirstWords, maskedRippleSecondWords, maskedRippleExpectedWords]
        have hc := rippleCell_round mode e t a (maskedRippleFirstWords mode es ts ads carry).2.2
        cases hf : rippleFirstBits mode e ⟨t,a,(maskedRippleFirstWords mode es ts ads carry).2.2⟩
        rw [hf] at hc
        rw [hc]
        simp only
        rw [hr.1, hr.2]
        constructor
        · rfl
        · rw [← hr.2, hf]

private theorem expected_append (mode : RippleMode) (es fs ts us ads vs : List Bool)
    (carry : Bool) (he : es.length = ts.length) (ha : ts.length = ads.length) :
    maskedRippleExpectedWords mode (es ++ fs) (ts ++ us) (ads ++ vs) carry =
      let rest := maskedRippleExpectedWords mode fs us vs carry
      let pre := maskedRippleExpectedWords mode es ts ads rest.2
      (pre.1 ++ rest.1, pre.2) := by
  induction es generalizing ts ads carry with
  | nil =>
    have ht : ts = [] := List.eq_nil_of_length_eq_zero he.symm
    subst ts
    have ha' : ads = [] := List.eq_nil_of_length_eq_zero ha.symm
    subst ads
    rfl
  | cons e es ih =>
    cases ts with
    | nil => simp at he
    | cons t ts =>
      cases ads with
      | nil => simp at ha
      | cons a ads =>
        simp only [List.cons_append, maskedRippleExpectedWords]
        rw [ih ts ads carry (by simpa using he) (by simpa using ha)]

private theorem expected_constant (mode : RippleMode) (enabled : Bool)
    (ts ads : List Bool) (carry : Bool) :
    maskedRippleExpectedWords mode (List.replicate ts.length enabled) ts ads carry =
      uniformRippleExpectedWords mode enabled ts ads carry := by
  induction ts generalizing ads carry with
  | nil => rfl
  | cons t ts ih =>
    cases ads with
    | nil => rfl
    | cons a ads =>
      simp only [List.length_cons, List.replicate_succ, maskedRippleExpectedWords,
        uniformRippleExpectedWords, ih]

/-- A contiguous enabled slice performs the uniform ripple operation, leaving both
outside slices unchanged and restoring the entire addend and incoming carry. -/
theorem maskedRippleWords_interval (mode : RippleMode) (enabled : Bool)
    (pre middle post apre amid apost : List Bool) (carry : Bool)
    (hp : pre.length = apre.length) (hm : middle.length = amid.length)
    (hs : post.length = apost.length) :
    let mask := List.replicate pre.length false ++ List.replicate middle.length enabled ++
      List.replicate post.length false
    let first := maskedRippleFirstWords mode mask (pre ++ middle ++ post) (apre ++ amid ++ apost) carry
    let second := maskedRippleSecondWords mode mask first.1 first.2.1 first.2.2
    second = (pre ++ (uniformRippleExpectedWords mode enabled middle amid carry).1 ++ post,
      apre ++ amid ++ apost, carry) ∧
      first.2.2 = (uniformRippleExpectedWords mode enabled middle amid carry).2 := by
  have hf := maskedRippleWords_fusion mode
    (List.replicate pre.length false ++ List.replicate middle.length enabled ++ List.replicate post.length false)
    (pre ++ middle ++ post) (apre ++ amid ++ apost) carry (by simp) (by simp [hp, hm, hs])
  dsimp only at hf ⊢
  have he : maskedRippleExpectedWords mode
      (List.replicate pre.length false ++ List.replicate middle.length enabled ++ List.replicate post.length false)
      (pre ++ middle ++ post) (apre ++ amid ++ apost) carry =
      (pre ++ (uniformRippleExpectedWords mode enabled middle amid carry).1 ++ post,
        (uniformRippleExpectedWords mode enabled middle amid carry).2) := by
    rw [expected_append mode _ _ _ _ _ _ carry (by simp) (by simp [hp, hm])]
    rw [expected_constant, uniformRippleExpectedWords_disabled]
    dsimp only
    rw [expected_append mode _ _ _ _ _ _ carry (by simp) hp]
    rw [expected_constant]
    dsimp only
    rw [expected_constant, uniformRippleExpectedWords_disabled]
  simpa only [he] using hf

/-- Numeric addition/subtraction on the selected slice follows from the same two
masked passes; the input carry is included in the modular result. -/
theorem maskedRippleWords_interval_value (mode : RippleMode)
    (pre middle post apre amid apost : List Bool) (carry : Bool)
    (hp : pre.length = apre.length) (hm : middle.length = amid.length)
    (hs : post.length = apost.length) :
    let mask := List.replicate pre.length false ++ List.replicate middle.length true ++
      List.replicate post.length false
    let first := maskedRippleFirstWords mode mask (pre ++ middle ++ post) (apre ++ amid ++ apost) carry
    let second := maskedRippleSecondWords mode mask first.1 first.2.1 first.2.2
    boolWordToNat (((second.1.drop pre.length).take middle.length).reverse) =
      (match mode with
      | .add => boolWordToNat middle.reverse + boolWordToNat amid.reverse + carry.toNat
      | .sub => boolWordToNat middle.reverse + 2^middle.length - boolWordToNat amid.reverse - carry.toNat) %
        2^middle.length := by
  have hf := (maskedRippleWords_interval mode true pre middle post apre amid apost carry hp hm hs).1
  dsimp only at hf ⊢
  rw [hf]
  simp only [List.append_assoc, List.drop_left, List.take_left', uniformRippleExpectedWords_length]
  cases mode
  · exact uniformRippleExpectedWords_add_mod middle amid carry hm
  · exact uniformRippleExpectedWords_sub_mod middle amid carry hm

end ShorECDLP.Paper2607_13816
