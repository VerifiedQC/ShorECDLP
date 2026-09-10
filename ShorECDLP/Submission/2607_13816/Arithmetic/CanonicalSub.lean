import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularSub
namespace ShorECDLP.Paper2607_13816
open Classical
private def replaceWord (ws : List Wire) (n : Nat) (s : BasisState) : BasisState :=
  fun w => if w ∈ ws then ((constantBits ws.length n)[ws.idxOf w]?).getD false else s w
private theorem replaceWord_read (ws : List Wire) (n : Nat) (s : BasisState) (hn : ws.Nodup) :
    wireValues ws (replaceWord ws n s)=constantBits ws.length n := by
  apply List.ext_getElem
  · simp [wireValues]
  · intro i hi hj
    simp only [wireValues,List.getElem_map]
    simp only [replaceWord,List.getElem_mem,if_true,hn.idxOf_getElem]
    simp only [List.getElem?_eq_getElem hj,Option.getD_some]
private theorem replaceWord_value (ws : List Wire) (n : Nat) (s : BasisState) (hn : ws.Nodup)
    (hb : n<2^ws.length) : boolWordToNat (wireValues ws (replaceWord ws n s))=n := by
  rw [replaceWord_read ws n s hn,boolWordToNat_constantBits,Nat.mod_eq_of_lt hb]
private theorem word_ext (ws : List Wire) (s t : BasisState)
    (he : boolWordToNat (wireValues ws s)=boolWordToNat (wireValues ws t))
    (hf : ∀ w, w ∉ ws → s w=t w) : s=t := by
  have hw : wireValues ws s=wireValues ws t := boolWordToNat_injective_of_length (by simp [wireValues]) he
  funext w
  by_cases h : w ∈ ws
  · have hh := List.map_inj_left.mp hw w h
    exact hh
  · exact hf w h
private theorem sub_add_cancel (x y p : Nat) (hx : x<p) (hy : y<p) :
    ((y+p-x)%p+x)%p=y := by
  have hz : x≤y+p := by omega
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.sub_add_cancel hz, Nat.add_mod_right, Nat.mod_eq_of_lt hy]

theorem modularSubIdealState_correct (input acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (s : BasisState)
    (hlen : input.length=acc.length) (hk : acc.length=correction.length) (hm : acc.length=modulus.length)
    (hnd : ([q,c,r,t,f]++input++acc).Nodup) (hc : s c=false) (hf : s f=false)
    (hp : p<2^acc.length) (hx : boolWordToNat (wireValues input s)<p)
    (hy : boolWordToNat (wireValues acc s)<p)
    (hconstant : boolWordToNat correction=2^acc.length-p) (hmodulus : boolWordToNat modulus=p) :
    boolWordToNat (wireValues acc (modularSubIdealState input acc modulus p q c f s))=
      (boolWordToNat (wireValues acc s)+p-(if s q then boolWordToNat (wireValues input s) else 0))%p ∧
    ∀ w, w ∉ acc → modularSubIdealState input acc modulus p q c f s w=s w := by
  let x := if s q then boolWordToNat (wireValues input s) else 0
  let y := boolWordToNat (wireValues acc s)
  let z := (y+p-x)%p
  have hp0 : 0<p := by omega
  have hxp : x<p := by dsimp only [x]; split <;> omega
  have hzp : z<p := Nat.mod_lt _ hp0
  let before := replaceWord acc z s
  have hbvalue : boolWordToNat (wireValues acc before)=z :=
    replaceWord_value acc z s (List.nodup_append.mp hnd).2.1 (Nat.lt_trans hzp hp)
  have hbframe (w : Wire) (hw : w ∉ acc) : before w=s w := by simp [before,replaceWord,hw]
  have hsep (w : Wire) (hw : w ∈ [q,c,r,t,f]++input) : w ∉ acc := by
    intro hh; exact (List.nodup_append.mp hnd).2.2 w hw w hh rfl
  have hbinput : wireValues input before=wireValues input s := by
    apply List.map_congr_left
    intro w hw
    exact hbframe w (hsep w (List.mem_append_right _ hw))
  have hbq : before q=s q := hbframe q (hsep q (by simp))
  have hbc : before c=false := (hbframe c (hsep c (by simp))).trans hc
  have hbf : before f=false := (hbframe f (hsep f (by simp))).trans hf
  have hbx : boolWordToNat (wireValues input before)<p := by rw [hbinput]; exact hx
  have hby : boolWordToNat (wireValues acc before)<p := hbvalue ▸ hzp
  have ha := modularAddIdealState_correct input acc correction p q c r t f before hlen hk hnd hbc hbf hp hbx hby hconstant
  have hafter : modularAddIdealState input acc correction p q c f before=s := by
    apply word_ext acc
    · rw [ha.1,hbvalue,hbinput,hbq]
      exact sub_add_cancel x y p hxp hy
    · intro w hw
      exact (ha.2 w hw).trans (hbframe w hw)
  have hs := modularSubIdealState_after_add input acc correction modulus p q c r t f before
    hlen hk hm hnd hbc hbf hp hbx hby hconstant hmodulus
  rw [hafter] at hs
  rw [hs]
  exact ⟨hbvalue,hbframe⟩
end ShorECDLP.Paper2607_13816
