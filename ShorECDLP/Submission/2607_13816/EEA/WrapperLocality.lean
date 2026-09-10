import ShorECDLP.Submission.«2607_13816».EEA.PhysicalSupport
import ShorECDLP.Submission.«2607_13816».EEA.WorkspaceReuse
/-!
# External frame of the complete EEA ideal

Compose the production schedule support through input centering, canonical
rotation, epoch compression, parity correction and Work1 clearing. The complete
ideal preserves external wires and depends only on its 580 allocated inputs.
Replacing an external bank therefore gives another actual forward image, while
preserving the input-validity contract. These are state-level consequences of
the complete adaptive wrapper's coherent contract, not an adaptive resource bound.
-/

namespace ShorECDLP.Paper2607_13816
open Classical
private def Local580 (f : BasisState → BasisState) : Prop :=
  (∀ s w, 580 ≤ w → f s w = s w) ∧
  ∀ s t, (∀ w, w < 580 → s w = t w) → ∀ w, w < 580 → f s w = f t w
private theorem local_comp {f g : BasisState → BasisState}
    (hf : Local580 f) (hg : Local580 g) : Local580 (fun s => g (f s)) := by
  constructor
  · intro s w hw; exact (hg.1 _ _ hw).trans (hf.1 _ _ hw)
  · intro s t h; exact hg.2 _ _ (hf.2 _ _ h)
private theorem local_run {c : Circuit} (hc : PaperCircuitUsesOnly (List.range 580) c) :
    Local580 (run c) := by
  constructor
  · intro s w hw; exact hc.preservesOutside s (by simpa using hw)
  · intro s t h; simpa only [List.mem_range] using hc.run_congrOn s t (by simpa using h)
private theorem upd_congr (s t : BasisState) (h : ∀ w, w < 580 → s w = t w)
    (a : Wire) (b : Bool) : ∀ w, w < 580 → upd s a b w = upd t a b w := by
  intro w hw
  by_cases ha : w=a
  · simp [upd,ha]
  · simp [upd,ha,h w hw]
private def localWrite : List Wire → List Bool → BasisState → BasisState
  | w::ws,b::bs,s => localWrite ws bs (upd s w b)
  | _,_,s => s
private theorem write_frame (ws : List Wire) (bs : List Bool) (s : BasisState)
    (hws : ∀ w ∈ ws, w < 580) : ∀ w, 580 ≤ w → localWrite ws bs s w = s w := by
  induction ws generalizing bs s with
  | nil => intro w hw; rfl
  | cons a as ih =>
    cases bs with
    | nil => intro w hw; rfl
    | cons b bs =>
      intro w hw
      rw [localWrite,ih bs _ (by intro v hv; exact hws v (by simp [hv])) w hw]
      have ha : w ≠ a := by have := hws a (by simp); dsimp only [Wire] at *; omega
      simp [upd,ha]
private theorem write_congr (ws : List Wire) (bs : List Bool) (s t : BasisState)
    (h : ∀ w, w < 580 → s w=t w) :
    ∀ w, w < 580 → localWrite ws bs s w=localWrite ws bs t w := by
  induction ws generalizing bs s t with
  | nil => exact h
  | cons a as ih =>
    cases bs with
    | nil => exact h
    | cons b bs => exact ih bs _ _ (upd_congr s t h a b)
private theorem add_eq_localWrite (input : List Wire) (constant : List Bool) (q : Wire) (s : BasisState) :
    gidneyAddIdealState input constant q s =
      localWrite input (cuccaroAddBits false (wireValues input s) (constant.map (fun k => s q && k))) s := by
  unfold gidneyAddIdealState
  generalize cuccaroAddBits false (wireValues input s) (constant.map (fun k => s q && k)) = bits
  induction input generalizing bits s with
  | nil => rfl
  | cons a as ih =>
    cases bits with
    | nil => rfl
    | cons b bs => exact ih (upd s a b) bs
private theorem local_add (input : List Wire) (constant : List Bool) (q : Wire)
    (hi : ∀ w ∈ input, w < 580) (hq : q < 580) :
    Local580 (gidneyAddIdealState input constant q) := by
  constructor
  · intro s w hw
    rw [add_eq_localWrite]
    exact write_frame input _ s hi w hw
  · intro s t h w hw
    have he : wireValues input s = wireValues input t := List.map_congr_left (fun v hv => h v (hi v hv))
    rw [add_eq_localWrite,add_eq_localWrite]
    rw [he,h q hq]
    exact write_congr input _ s t h w hw
private theorem local_minus (input : List Wire) (modulus : List Bool) (q : Wire)
    (hi : ∀ w ∈ input, w < 580) (hq : q < 580) :
    Local580 (constMinusIdealState input modulus q) := by
  have hc : Local580 (fun s w => if w ∈ input then s w ^^ s q else s w) := by
    constructor
    · intro s w hw
      have hn : w ∉ input := by intro hm; have := hi w hm; dsimp only [Wire] at *; omega
      simp [hn]
    · intro s t h w hw
      simp only [h w hw,h q hq]
  unfold constMinusIdealState
  exact local_comp (local_comp hc (local_add input ((List.range input.length).map (Nat.testBit 1)) q hi hq)) (local_add input modulus q hi hq)
private theorem local_center (input : List Wire) (modulus : List Bool) (p : Nat) (q : Wire)
    (hi : ∀ w ∈ input, w < 580) (hq : q < 580) :
    Local580 (eeaCenterIdealState input modulus p q) := by
  have hc : Local580 (fun s => upd s q
      (s q ^^ decide (p/2+1 ≤ boolWordToNat (wireValues input s)))) := by
    constructor
    · intro s w hw
      have hn : w ≠ q := by dsimp only [Wire] at *; omega
      simp [upd,hn]
    · intro s t h w hw
      have he : wireValues input s = wireValues input t :=
        List.map_congr_left (fun v hv => h v (hi v hv))
      dsimp only
      rw [he,h q hq]
      exact upd_congr s t h _ _ w hw
  unfold eeaCenterIdealState
  exact local_comp hc (local_minus input modulus q hi hq)
private theorem closed_bound (ws : List Wire)
    (h : ws.all (fun w => decide (w < 580)) = true) : ∀ w ∈ ws, w < 580 := by
  intro w hw; exact of_decide_eq_true (List.all_eq_true.mp h w hw)
attribute [local irreducible] workRegistersPrepare eeaLengthSetup
private theorem local_preprocess : Local580 eeaPreprocessIdealState := by
  have hc := local_center (List.range' 266 256).reverse
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 2
    (closed_bound _ (by decide +kernel)) (by decide)
  unfold eeaPreprocessIdealState
  exact local_comp (local_comp (local_run (workRegistersPrepare_usesOnly.mono (by
      intro w hw; exact List.mem_range.mpr (closed_bound _ (by decide +kernel) w hw)))) hc)
    (local_run eeaLengthSetup_usesOnly)
private theorem gate_bound (g : Gate)
    (h : (gateWires g).all (fun w => decide (w < 580)) = true) :
    PaperCircuitUsesOnly (List.range 580) ([g] : Circuit) := by
  intro g' hg w hw
  simp only [List.mem_singleton] at hg
  subst g'
  exact List.mem_range.mpr (closed_bound _ h w hw)
private theorem support_bound (ws : List Wire)
    (h : ws.all (fun w => decide (w < 580)) = true) : ∀ w ∈ ws, w ∈ List.range 580 := by
  simpa only [List.mem_range] using closed_bound ws h
attribute [local irreducible] canonicalWork2RotationBit addConstant subConstant
private theorem canonical_support : PaperCircuitUsesOnly (List.range 580) canonicalWork2Rotation := by
  have hx := gate_bound (.X 559) (by decide +kernel)
  have ha := (addConstant_usesOnly (List.range' 540 9++[559]) (List.range' 560 10) 570 1).mono
    (support_bound _ (by decide +kernel))
  have hs := (subConstant_usesOnly (List.range' 540 9++[559]) (List.range' 560 10) 570 1).mono
    (support_bound _ (by decide +kernel))
  have hr : PaperCircuitUsesOnly (List.range 580)
      ((List.finRange 10).flatMap fun bit => canonicalWork2RotationBit
        (if bit.val<9 then 540+bit.val else 559) bit) := by
    intro g hg w hw
    obtain ⟨bit,_,hg⟩ := List.mem_flatMap.mp hg
    have hm := (canonicalWork2RotationBit_resources (if bit.val<9 then 540+bit.val else 559) bit).2.2.2.2.1 g hg w hw
    simp only [List.mem_cons,List.mem_range'] at hm
    have hb := bit.isLt
    apply List.mem_range.mpr
    dsimp only [Wire] at *
    split_ifs at hm <;> omega
  unfold canonicalWork2Rotation
  exact ((hx.append ha).append hr).append (hs.append hx)
private theorem epoch_support : PaperCircuitUsesOnly (List.range 580) terminalEpochCompression := by
  intro g hg w hw
  have h : (circuitWires terminalEpochCompression).all (fun w => decide (w < 580)) = true := by
    decide +kernel
  exact List.mem_range.mpr (closed_bound _ h w (List.mem_flatMap.mpr ⟨g,hg,hw⟩))

private theorem local_flip (q : Wire) (hq : q < 580) :
    Local580 (fun s => upd s q (!s q)) := by
  constructor
  · intro s w hw
    have hn : w ≠ q := by dsimp only [Wire] at *; omega
    simp [upd,hn]
  · intro s t h w hw
    dsimp only
    rw [h q hq]
    exact upd_congr s t h q _ w hw
attribute [local irreducible] constMinusIdealState
private theorem local_parity : Local580 secp256k1EEAParityIdealState := by
  have hf := local_flip 2 (by decide)
  have hm := local_minus (List.range' 263 256) secp256k1ModulusBits 2
    (closed_bound _ (by decide +kernel)) (by decide)
  unfold secp256k1EEAParityIdealState
  exact local_comp
    (f := fun s => constMinusIdealState (List.range' 263 256) secp256k1ModulusBits 2 (upd s 2 (!s 2)))
    (g := fun s => upd s 2 (!s 2)) (local_comp hf hm) hf
attribute [local irreducible] terminalWork1Clear canonicalWork2Rotation terminalEpochCompression
  secp256k1EEAForwardUnitary eeaPreprocessIdealState secp256k1EEAParityIdealState
private theorem local_output : Local580 secp256k1EEAOutputIdealState := by
  have hs := local_run secp256k1EEAForwardUnitary_production_usesOnly
  have hr := local_run canonical_support
  have he := local_run epoch_support
  have hc : PaperCircuitUsesOnly (List.range 580) terminalWork1Clear := by
    unfold terminalWork1Clear
    exact (xorConstant_usesOnly (List.range' 4 259) (ShorECDLP.p+2^258)).mono
      (support_bound _ (by decide +kernel))
  unfold secp256k1EEAOutputIdealState
  simp only [run_append]
  exact local_comp (local_comp (local_comp (local_comp (local_comp local_preprocess hs) hr) he)
    local_parity) (local_run hc)

/-- The full EEA ideal, including centering and output correction, preserves every external wire. -/
theorem secp256k1EEAOutputIdealState_preservesOutside (s : BasisState) (w : Wire)
    (hw : 580 ≤ w) : secp256k1EEAOutputIdealState s w = s w := local_output.1 s w hw
/-- The full EEA output on its allocated registers depends only on their input values. -/
theorem secp256k1EEAOutputIdealState_congrOn (s t : BasisState)
    (h : ∀ w, w < 580 → s w = t w) :
    ∀ w, w < 580 → secp256k1EEAOutputIdealState s w = secp256k1EEAOutputIdealState t w :=
  local_output.2 s t h
/-- Replacing an external retained bank commutes with the complete EEA ideal.
This constructs the actual forward image needed by the reverse-wrapper contract. -/
theorem secp256k1EEAOutputIdealState_patchOutside (s t : BasisState) :
    secp256k1EEAOutputIdealState (fun w => if w < 580 then s w else t w) =
      fun w => if w < 580 then secp256k1EEAOutputIdealState s w else t w := by
  funext w
  by_cases hw : w < 580
  · rw [if_pos hw]
    exact local_output.2 _ s (by intro v hv; simp [hv]) w hw
  · rw [if_neg hw,local_output.1 _ w (Nat.le_of_not_gt hw)]
    simp [hw]
/-- External retained values cannot change the clean, nonzero canonical EEA input contract. -/
theorem Secp256k1EEAInputValid_congrOn (s t : BasisState)
    (h : ∀ w, w < 580 → s w = t w) :
    Secp256k1EEAInputValid s ↔ Secp256k1EEAInputValid t := by
  have hc : Clean (List.range' 0 263 ++ List.range' 519 61) s ↔
      Clean (List.range' 0 263 ++ List.range' 519 61) t := by
    constructor
    · intro hs w hw
      rw [← h w (closed_bound _ (by decide +kernel) w hw)]
      exact hs w hw
    · intro ht w hw
      rw [h w (closed_bound _ (by decide +kernel) w hw)]
      exact ht w hw
  have hx : wireValues (List.range' 263 256) s = wireValues (List.range' 263 256) t :=
    List.map_congr_left (fun w hw => h w (closed_bound _ (by decide +kernel) w hw))
  simp only [Secp256k1EEAInputValid,hc,hx]
open Classical Quantum
attribute [local irreducible] secp256k1EEAOutputIdealState secp256k1EEAReverseWrapperIdealState
  secp256k1EEAReverseWrapper secp256k1EEAReverseInDataBank
/-- The live EEA registers agree with a valid forward output; retained external values are unrestricted. -/
def Secp256k1EEAForwardLocalImage (s : BasisState) : Prop :=
  ∃ original, Secp256k1EEAInputValid original ∧
    ∀ w, w < 580 → s w = secp256k1EEAOutputIdealState original w
private theorem patched_input (original retained : BasisState) (h : Secp256k1EEAInputValid original) :
    Secp256k1EEAInputValid (fun w => if w < 580 then original w else retained w) :=
  (Secp256k1EEAInputValid_congrOn original _ (by intro w hw; simp [hw])).mp h
private theorem local_image_witness (s : BasisState) (hs : Secp256k1EEAForwardLocalImage s) :
    ∃ original, Secp256k1EEAInputValid original ∧ s = secp256k1EEAOutputIdealState original := by
  obtain ⟨original,ho,hagree⟩ := hs
  refine ⟨fun w => if w < 580 then original w else s w,patched_input original s ho,?_⟩
  rw [secp256k1EEAOutputIdealState_patchOutside]
  funext w
  by_cases hw : w < 580
  · simp only [if_pos hw]; exact hagree w hw
  · simp only [if_neg hw]
/-- The actual inverse supports arbitrary retained external values with the original normalized branches. -/
theorem secp256k1EEAReverseWrapper_coherent_localImage :
    CoherentlyImplementsOn secp256k1EEAReverseWrapper
      (Finsupp.lmapDomain ℂ ℂ secp256k1EEAReverseWrapperIdealState)
      Secp256k1EEAForwardLocalImage := by
  obtain ⟨cs,ha,hm⟩ := secp256k1EEAReverseWrapper_coherent
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (local_image_witness s hs)),hm⟩
/-- Inverting a locally matching output restores the original EEA registers and keeps the retained frame. -/
theorem secp256k1EEAReverseWrapper_output_localImage (s original : BasisState)
    (ho : Secp256k1EEAInputValid original)
    (hagree : ∀ w, w < 580 → s w = secp256k1EEAOutputIdealState original w) :
    secp256k1EEAReverseWrapperIdealState s =
      fun w => if w < 580 then original w else s w := by
  have hout : secp256k1EEAOutputIdealState (fun w => if w < 580 then original w else s w) = s := by
    rw [secp256k1EEAOutputIdealState_patchOutside]
    funext w
    by_cases hw : w < 580
    · simp only [if_pos hw]; exact (hagree w hw).symm
    · simp only [if_neg hw]
  have h := secp256k1EEAReverseWrapper_output _ (patched_input original s ho)
  rw [hout] at h
  exact h
/-- The same retained-frame contract transports to the actual inverse borrowing the cleared data bank. -/
theorem secp256k1EEAReverseInDataBank_coherent_localImage :
    CoherentlyImplementsOn secp256k1EEAReverseInDataBank
      ((relabelState eeaWorkspaceExchange).comp
        ((Finsupp.lmapDomain ℂ ℂ secp256k1EEAReverseWrapperIdealState).comp
          (relabelState eeaWorkspaceExchange.symm)))
      (fun s => Secp256k1EEAForwardLocalImage (relabelBasis eeaWorkspaceExchange.symm s)) := by
  unfold secp256k1EEAReverseInDataBank
  exact secp256k1EEAReverseWrapper_coherent_localImage.relabel eeaWorkspaceExchange

end ShorECDLP.Paper2607_13816
