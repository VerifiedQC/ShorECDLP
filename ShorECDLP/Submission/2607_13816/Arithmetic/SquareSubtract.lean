import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareCoherent
import ShorECDLP.Submission.«2607_13816».Arithmetic.CanonicalSub
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem image_word_ext (ws : List Wire) (s t : BasisState)
    (he : boolWordToNat (wireValues ws s)=boolWordToNat (wireValues ws t))
    (hf : ∀ w, w ∉ ws → s w=t w) : s=t := by
  have hw := boolWordToNat_injective_of_length (by simp [wireValues]) he
  funext w
  by_cases h : w ∈ ws
  · exact List.map_inj_left.mp hw w h
  · exact hf w h
private theorem clear_zero (ws : List Wire) (s : BasisState) :
    boolWordToNat (wireValues ws (hornerClearOutput ws s))=0 := by
  have hh : wireValues ws (hornerClearOutput ws s)=ws.map (fun _ => false) := by
    apply List.map_congr_left
    intro w hw
    simp [hornerClearOutput,hw]
  rw [hh]
  clear hh
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [boolWordToNat] using ih

/-- A canonical square value with clean helpers is in the actual forward image,
regardless of the untouched external register state. -/
theorem squareLoop_image_of_value (input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (copied c r t f : Wire) (s : BasisState)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=correction.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcopy : s copied=false) (hc : s c=false) (hf : s f=false)
    (hp : p<2^(a::rest).length) (hodd : p%2=1)
    (hx : boolWordToNat (wireValues input s)<p)
    (hsquare : boolWordToNat (wireValues (a::rest) s)=
      (boolWordToNat (wireValues input s)*boolWordToNat (wireValues input s))%p)
    (hconstant : boolWordToNat correction=2^(a::rest).length-p) :
    squareLoopIdealState input input (a::rest) correction p copied c f (hornerClearOutput (a::rest) s)=s := by
  have hsep (w : Wire) (hw : w ∈ [copied,c,r,t,f]++input) : w ∉ a::rest := by
    intro hh
    exact (List.nodup_append.mp hnd).2.2 w hw w hh rfl
  have hframe (w : Wire) (hw : w ∉ a::rest) : hornerClearOutput (a::rest) s w=s w := by
    simp [hornerClearOutput,hw]
  have hinput : wireValues input (hornerClearOutput (a::rest) s)=wireValues input s := by
    apply List.map_congr_left
    intro w hw
    exact hframe w (hsep w (List.mem_append_right _ hw))
  have hh := squareLoopIdealState_correct input input a rest correction p copied c r t f
    (hornerClearOutput (a::rest) s) hlen hk hnd (fun _ h => h)
    ((hframe copied (hsep copied (by simp))).trans hcopy)
    ((hframe c (hsep c (by simp))).trans hc)
    ((hframe f (hsep f (by simp))).trans hf) hp hodd
    (by rw [hinput]; exact hx) (clear_zero _ _) hconstant
  apply image_word_ext (a::rest)
  · rw [hh.1,hinput,hsquare]
  · intro w hw
    exact (hh.2 w hw).trans (hframe w hw)
/-- The literal inverse clears any canonical square image, retaining its external frame. -/
theorem squareLoopInverse_branch_of_value (input : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (copied c r t f : Wire) (s : BasisState)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=correction.length)
    (hm : (a::rest).length=modulus.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcopy : s copied=false) (hc : s c=false) (hr : s r=false) (ht : s t=false) (hf : s f=false)
    (hp : p<2^(a::rest).length) (hodd : p%2=1)
    (hx : boolWordToNat (wireValues input s)<p)
    (hsquare : boolWordToNat (wireValues (a::rest) s)=
      (boolWordToNat (wireValues input s)*boolWordToNat (wireValues input s))%p)
    (hconstant : boolWordToNat correction=2^(a::rest).length-p)
    (hmodulus : boolWordToNat modulus=p)
    (b : Quantum.InstrumentBranch)
    (hb : b ∈ (squareLoopInverse input input (a::rest) modulus p copied c r t f).run) :
    b.kraus (Quantum.ket s)=Quantum.registerXResetMagnitude b.history.length •
      Quantum.ket (hornerClearOutput (a::rest) s) := by
  have hsep (w : Wire) (hw : w ∈ [copied,c,r,t,f]++input) : w ∉ a::rest := by
    intro hh
    exact (List.nodup_append.mp hnd).2.2 w hw w hh rfl
  have hframe (w : Wire) (hw : w ∉ a::rest) : hornerClearOutput (a::rest) s w=s w := by
    simp [hornerClearOutput,hw]
  have hinput : wireValues input (hornerClearOutput (a::rest) s)=wireValues input s := by
    apply List.map_congr_left
    intro w hw
    exact hframe w (hsep w (List.mem_append_right _ hw))
  have hi := squareLoop_image_of_value input a rest correction p copied c r t f s
    hlen hk hnd hcopy hc hf hp hodd hx hsquare hconstant
  have hh := squareLoopInverse_after_forward input input a rest correction modulus p copied c r t f
    (hornerClearOutput (a::rest) s) hlen hk hm hnd (fun _ h => h)
    ((hframe copied (hsep copied (by simp))).trans hcopy)
    ((hframe c (hsep c (by simp))).trans hc)
    ((hframe r (hsep r (by simp))).trans hr)
    ((hframe t (hsep t (by simp))).trans ht)
    ((hframe f (hsep f (by simp))).trans hf) hp hodd
    (by rw [hinput]; exact hx) (clear_zero _ _) hconstant hmodulus b hb
  rw [hi] at hh
  exact hh

end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Figure 14's literal square, controlled subtraction and inverse square.
The middle subtraction reuses the source helper slots in their rotated roles. -/
def squareSubtract (x y acc : List Wire) (correction modulus : List Bool) (p : Nat)
    (q copied c r t f : Wire) : Quantum.AdaptiveCircuit :=
  (squareLoop y y acc correction p copied c r t f).seq
    ((controlledModularSub acc x modulus p q copied f r c).seq
      (squareLoopInverse y y acc modulus p copied c r t f))
def squareSubtractIdealState (x y acc : List Wire) (correction modulus : List Bool) (p : Nat)
    (q copied c f : Wire) (s : BasisState) : BasisState :=
  hornerClearOutput acc (modularSubIdealState acc x modulus p q copied c
    (squareLoopIdealState y y acc correction p copied c f s))

private theorem values_frame (ws : List Wire) (s t : BasisState) (h : ∀ w ∈ ws, s w=t w) :
    wireValues ws s=wireValues ws t := List.map_congr_left h

theorem squareSubtract_correct (x y : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire) (s : BasisState)
    (hxlen : x.length=(a::rest).length) (hylen : y.length=(a::rest).length)
    (hk : (a::rest).length=correction.length) (hm : (a::rest).length=modulus.length)
    (hsq : ([copied,c,r,t,f]++y++(a::rest)).Nodup)
    (hsub : ([q,copied,f,r,c]++(a::rest)++x).Nodup)
    (hex : ∀ w ∈ y++[copied,c,r,t,f], w ∉ x)
    (hclean : Clean (a::rest) s) (hcopy : s copied=false) (hc : s c=false)
    (hr : s r=false) (ht : s t=false) (hf : s f=false)
    (hp : p<2^(a::rest).length) (hodd : p%2=1)
    (hx : boolWordToNat (wireValues x s)<p) (hy : boolWordToNat (wireValues y s)<p)
    (hconstant : boolWordToNat correction=2^(a::rest).length-p)
    (hmodulus : boolWordToNat modulus=p) :
    let out := squareSubtractIdealState x y (a::rest) correction modulus p q copied c f s
    boolWordToNat (wireValues x out)=
      (boolWordToNat (wireValues x s)+p-
        (if s q then (boolWordToNat (wireValues y s)*boolWordToNat (wireValues y s))%p else 0))%p ∧
    (∀ w, w ∉ x → out w=s w) ∧
    (∀ b ∈ (squareSubtract x y (a::rest) correction modulus p q copied c r t f).run,
      b.kraus (Quantum.ket s)=Quantum.registerXResetMagnitude b.history.length • Quantum.ket out) := by
  let acc := a::rest
  let u := squareLoopIdealState y y acc correction p copied c f s
  let v := modularSubIdealState acc x modulus p q copied c u
  have hp0 : 0<p := by omega
  have hsqsep (w : Wire) (hw : w ∈ [copied,c,r,t,f]++y) : w ∉ acc := by
    intro ha; exact (List.nodup_append.mp hsq).2.2 w hw w ha rfl
  have hax (w : Wire) (hw : w ∈ acc) : w ∉ x := by
    intro hh; exact (List.nodup_append.mp hsub).2.2 w (List.mem_append_right _ hw) w hh rfl
  have hxa (w : Wire) (hw : w ∈ x) : w ∉ acc := fun ha => hax w ha hw
  have hqa : q ∉ acc := by
    intro ha
    exact (List.nodup_append.mp (List.nodup_append.mp hsub).1).2.2 q (by simp) q ha rfl
  have hz : boolWordToNat (wireValues acc s)=0 := by
    have he : hornerClearOutput acc s=s := by
      funext w
      by_cases hw : w ∈ acc
      · simp [hornerClearOutput,hw,hclean w hw]
      · simp [hornerClearOutput,hw]
    rw [← he]
    exact clear_zero _ _
  have hu := squareLoopIdealState_correct y y a rest correction p copied c r t f s
    hylen hk hsq (fun _ h => h) hcopy hc hf hp hodd hy hz hconstant
  have ux : wireValues x u=wireValues x s := values_frame x u s (fun w hw => hu.2 w (hxa w hw))
  have uy : wireValues y u=wireValues y s := values_frame y u s (fun w hw => hu.2 w (hsqsep w (List.mem_append_right _ hw)))
  have uq : u q=s q := hu.2 q hqa
  have uf (w : Wire) (hw : w ∈ [copied,c,r,t,f]) : u w=s w := hu.2 w (hsqsep w (List.mem_append_left _ hw))
  have hv := modularSubIdealState_correct acc x correction modulus p q copied f r c u hxlen.symm
    (hxlen.trans hk) (hxlen.trans hm) hsub ((uf copied (by simp)).trans hcopy) ((uf c (by simp)).trans hc)
    (by simpa only [hxlen] using hp)
    (by rw [hu.1]; exact Nat.mod_lt _ hp0) (by rw [ux]; exact hx)
    (by simpa only [hxlen] using hconstant) hmodulus
  have va : wireValues acc v=wireValues acc u := values_frame acc v u (fun w hw => hv.2 w (hax w hw))
  have vy : wireValues y v=wireValues y s := (values_frame y v u
    (fun w hw => hv.2 w (hex w (List.mem_append_left _ hw)))).trans uy
  have vf (w : Wire) (hw : w ∈ [copied,c,r,t,f]) : v w=s w :=
    (hv.2 w (hex w (List.mem_append_right _ hw))).trans (uf w hw)
  have vv : boolWordToNat (wireValues acc v)=
      (boolWordToNat (wireValues y v)*boolWordToNat (wireValues y v))%p := by rw [va,hu.1,vy]
  have hvy : boolWordToNat (wireValues y v)<p := by rw [vy]; exact hy
  refine ⟨?_,?_,?_⟩
  · have ho : wireValues x (hornerClearOutput acc v)=wireValues x v := by
      apply values_frame
      intro w hw
      simp [hornerClearOutput,hxa w hw]
    change boolWordToNat (wireValues x (hornerClearOutput acc v))=_
    rw [ho,hv.1,ux,uq,hu.1]
  · intro w hw
    change hornerClearOutput acc v w=s w
    by_cases ha : w ∈ acc
    · simp [hornerClearOutput,ha,hclean w ha]
    · simp only [hornerClearOutput,if_neg ha]
      exact (hv.2 w hw).trans (hu.2 w ha)
  · intro b hb
    apply horner_seq_branch _ _ s u _ ?_ ?_ b hb
    · intro b hb
      exact squareLoop_branch_correct y y a rest correction p copied c r t f s hylen hk hsq
        (fun _ h => h) hcopy hc hr ht hf hp hodd hy hz hconstant b hb
    · intro b hb
      apply horner_seq_branch _ _ u v _ ?_ ?_ b hb
      · intro b hb
        have hh := controlledModularSub_branch_correct acc x modulus p q copied f r c u hxlen.symm
          (by rw [hxlen]; simp) (hxlen.trans hm) hsub
          ((uf copied (by simp)).trans hcopy) ((uf f (by simp)).trans hf) ((uf r (by simp)).trans hr) b hb
        rw [hh.1]; exact hh.2
      · intro b hb
        exact squareLoopInverse_branch_of_value y a rest correction modulus p copied c r t f v
          hylen hk hm hsq ((vf copied (by simp)).trans hcopy) ((vf c (by simp)).trans hc)
          ((vf r (by simp)).trans hr) ((vf t (by simp)).trans ht) ((vf f (by simp)).trans hf)
          hp hodd hvy vv hconstant hmodulus b hb
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

theorem squareSubtract_wellFormed (x y : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire)
    (hxlen : x.length=(a::rest).length) (hylen : y.length=(a::rest).length)
    (hk : (a::rest).length=correction.length) (hm : (a::rest).length=modulus.length)
    (hsq : ([copied,c,r,t,f]++y++(a::rest)).Nodup)
    (hsub : ([q,copied,f,r,c]++(a::rest)++x).Nodup) :
    (squareSubtract x y (a::rest) correction modulus p q copied c r t f).WellFormed :=
  (squareLoop_wellFormed y y a rest correction p copied c r t f hylen hk hsq (fun _ h => h)).seq
    ((controlledModularSub_wellFormed (a::rest) x modulus p q copied f r c hxlen.symm
      (by rw [hxlen]; simp) (hxlen.trans hm) hsub).seq
      (squareLoopInverse_wellFormed y y a rest modulus p copied c r t f hylen hm hsq (fun _ h => h)))

/-- Clean square workspace and canonical input/output field values. -/
def SquareSubtractValid (x y acc : List Wire) (p : Nat) (copied c r t f : Wire) (s : BasisState) : Prop :=
  Clean acc s ∧ s copied=false ∧ s c=false ∧ s r=false ∧ s t=false ∧ s f=false ∧
    boolWordToNat (wireValues x s)<p ∧ boolWordToNat (wireValues y s)<p

/-- Every supported superposition sees the same square-subtraction map,
with one input-independent normalized measurement expansion. -/
theorem squareSubtract_coherent (x y : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire)
    (hxlen : x.length=(a::rest).length) (hylen : y.length=(a::rest).length)
    (hk : (a::rest).length=correction.length) (hm : (a::rest).length=modulus.length)
    (hsq : ([copied,c,r,t,f]++y++(a::rest)).Nodup)
    (hsub : ([q,copied,f,r,c]++(a::rest)++x).Nodup)
    (hex : ∀ w ∈ y++[copied,c,r,t,f], w ∉ x)
    (hp : p<2^(a::rest).length) (hodd : p%2=1)
    (hconstant : boolWordToNat correction=2^(a::rest).length-p)
    (hmodulus : boolWordToNat modulus=p) :
    CoherentlyImplementsOn (squareSubtract x y (a::rest) correction modulus p q copied c r t f)
      (Finsupp.lmapDomain ℂ ℂ (squareSubtractIdealState x y (a::rest) correction modulus p q copied c f))
      (SquareSubtractValid x y (a::rest) p copied c r t f) := by
  have hz (ws : List Wire) : boolWordToNat (wireValues ws (fun _ => false))=0 := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simpa [wireValues,boolWordToNat] using ih
  have hp0 : 0<p := by omega
  apply coherent_history_branches _ _ _
    (squareSubtract_wellFormed x y a rest correction modulus p q copied c r t f hxlen hylen hk hm hsq hsub)
    (fun _ => false) ?_ ?_
  · exact ⟨fun _ _ => rfl,rfl,rfl,rfl,rfl,rfl,by rw [hz]; exact hp0,by rw [hz]; exact hp0⟩
  · intro b hb s hs
    exact (squareSubtract_correct x y a rest correction modulus p q copied c r t f s
      hxlen hylen hk hm hsq hsub hex hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1
      hp hodd hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 hconstant hmodulus).2.2 b hb
end ShorECDLP.Paper2607_13816
