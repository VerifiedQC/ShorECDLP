import ShorECDLP.Submission.«2607_13816».EEA.TopBoundary
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem read_eq_iff (R : List Wire) (s t : BasisState) :
    wireValues R s=wireValues R t ↔ ∀ w ∈ R, s w=t w := List.map_inj_left
theorem registerMatches_pattern (R : List Wire) (pattern s : BasisState) :
    registerMatches R (boolWordToNat (wireValues R pattern)) s = decide (∀ w ∈ R, s w=pattern w) := by
  rw [registerMatches_eq_numeric R _ s (by simpa [wireValues] using boolWordToNat_lt_pow_two (wireValues R pattern))]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact (read_eq_iff R s pattern).mp (boolWordToNat_injective_of_length (by simp [wireValues]) h)
  · intro h
    exact congrArg boolWordToNat ((read_eq_iff R s pattern).mpr h)

/-- Flipping the sole differing bit under an exact match on all other bits
is the endpoint transposition on the entire register word. -/
theorem maskedBitFlip_word_swap (R : List Wire) (t : Wire) (pa pb s : BasisState)
    (ht : t ∈ R) (hbit : pa t≠pb t)
    (hother : ∀ w ∈ R, w≠t → pa w=pb w) :
    wireValues R (s[t ↦ Bool.xor (s t) (decide (∀ w ∈ R, w≠t → s w=pa w))])=
      Equiv.swap (wireValues R pa) (wireValues R pb) (wireValues R s) := by
  have hab : wireValues R pa≠wireValues R pb := by
    intro h
    exact hbit ((read_eq_iff R pa pb).mp h t ht)
  have hnotA : (!(pa t))=pb t := by cases ha : pa t <;> cases hb : pb t <;> simp_all
  have hnotB : (!(pb t))=pa t := by cases ha : pa t <;> cases hb : pb t <;> simp_all
  by_cases hA : wireValues R s=wireValues R pa
  · have hsa := (read_eq_iff R s pa).mp hA
    have hm : ∀ w ∈ R, w≠t → s w=pa w := fun w hw _ => hsa w hw
    rw [Equiv.swap_apply_def,if_pos hA,decide_eq_true hm]
    apply (read_eq_iff R _ pb).mpr
    intro w hw
    by_cases hwt : w=t
    · subst w; simp [upd,hsa t ht,hnotA]
    · simp only [upd_other s t _ hwt]
      exact (hsa w hw).trans (hother w hw hwt)
  · by_cases hB : wireValues R s=wireValues R pb
    · have hsb := (read_eq_iff R s pb).mp hB
      have hm : ∀ w ∈ R, w≠t → s w=pa w := fun w hw hwt =>
        (hsb w hw).trans (hother w hw hwt).symm
      rw [Equiv.swap_apply_def,if_neg hA,if_pos hB,decide_eq_true hm]
      apply (read_eq_iff R _ pa).mpr
      intro w hw
      by_cases hwt : w=t
      · subst w; simp [upd,hsb t ht,hnotB]
      · simp only [upd_other s t _ hwt]
        exact hm w hw hwt
    · have hm : ¬∀ w ∈ R, w≠t → s w=pa w := by
        intro h
        by_cases hst : s t=pa t
        · apply hA
          apply (read_eq_iff R s pa).mpr
          intro w hw
          by_cases he : w=t
          · simpa [he] using hst
          · exact h w hw he
        · have hstb : s t=pb t := by cases ha : pa t <;> cases hb : pb t <;> cases hs : s t <;> simp_all
          apply hB
          apply (read_eq_iff R s pb).mpr
          intro w hw
          by_cases he : w=t
          · simpa [he] using hstb
          · exact (h w hw he).trans (hother w hw he)
      rw [Equiv.swap_apply_def,if_neg hA,if_neg hB,decide_eq_false hm]
      congr 1
      funext w
      by_cases hw : w=t <;> simp [upd,hw]
end ShorECDLP.Paper2607_13816
