import ShorECDLP.Submission.«2607_13816».Challenge.ControlSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem andEraseProgram_support (n start : Nat) (a b t : Wire) (support : List Wire)
    (ha : a ∈ support) (hb : b ∈ support) (ht : t ∈ support) :
    straightWires (andEraseProgram n start a b t) ⊆ support := by
  simp only [andEraseProgram,straightWires,recordGates_support,List.append_nil,List.cons_subset]
  refine ⟨ht,?_⟩
  by_cases h : a = b
  · simp [controlledZ,h,circuitWires,gateWires,hb]
  · simp [controlledZ,circuitWires,gateWires,ha,hb]

theorem vchainTailProgram_support (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) (support : List Wire)
    (hc : controls ⊆ support) (ha : acc ∈ support) (ht : target ∈ support)
    (hs : scratch ⊆ support) :
    straightWires (vchainTailProgram n controls acc target scratch start).2 ⊆ support := by
  induction controls generalizing acc scratch start with
  | nil => exact List.nil_subset _
  | cons control controls ih =>
    have hcontrol := hc List.mem_cons_self
    cases controls with
    | nil => simp [vchainTailProgram,literalProgram_support,circuitWires,gateWires,hcontrol,ha,ht]
    | cons next controls =>
      cases scratch with
      | nil => exact List.nil_subset _
      | cons work scratch =>
        have hw := hs List.mem_cons_self
        have hi := ih work scratch start (fun _ h => hc (List.mem_cons_of_mem _ h)) hw (fun _ h => hs (List.mem_cons_of_mem _ h))
        have he cursor := andEraseProgram_support n cursor control acc work support hcontrol ha hw
        simp only [vchainTailProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
        refine ⟨?_,hi,he _⟩
        simp [circuitWires,gateWires,hcontrol,ha,hw]

theorem vchainProgram_support (n start : Nat) (controls : List Wire) (target : Wire)
    (scratch : List Wire) (support : List Wire)
    (hc : controls ⊆ support) (ht : target ∈ support) (hs : scratch ⊆ support) :
    straightWires (vchainProgram n start controls target scratch).2 ⊆ support := by
  cases controls with
  | nil => simp [vchainProgram,literalProgram_support,circuitWires,gateWires,ht]
  | cons first rest =>
    have hf := hc List.mem_cons_self
    cases rest with
    | nil => simp [vchainProgram,literalProgram_support,circuitWires,gateWires,hf,ht]
    | cons second rest =>
      apply vchainTailProgram_support n (first::rest) second target scratch start support
      · intro w hw
        exact hc (by simp only [List.mem_cons] at hw ⊢; tauto)
      · exact hc (by simp)
      · exact ht
      · exact hs

theorem rippleMajProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleMajProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleMajProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,ht,ha,hcarry]

theorem rippleUmaProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleUmaProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleUmaProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,hc,ht,ha,hcarry]

theorem rippleMajInvProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleMajInvProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleMajInvProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,ht,ha,hcarry]

theorem rippleUmaInvProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleUmaInvProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleUmaInvProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,hc,ht,ha,hcarry]

theorem rippleFirstProgram_support (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleFirstProgram n start mode control target addend carry scratch).2 ⊆ support := by
  cases mode
  · exact rippleMajProgram_support n start control target addend carry scratch support hc ht ha hcarry hs
  · exact rippleUmaInvProgram_support n start control target addend carry scratch support hc ht ha hcarry hs

theorem rippleSecondProgram_support (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleSecondProgram n start mode control target addend carry scratch).2 ⊆ support := by
  cases mode
  · exact rippleUmaProgram_support n start control target addend carry scratch support hc ht ha hcarry hs
  · exact rippleMajInvProgram_support n start control target addend carry scratch support hc ht ha hcarry hs


theorem equalityProgram_support (n start : Nat) (register : List Wire) (value : Nat)
    (flag : Wire) (scratch support : List Wire)
    (hr : register ⊆ support) (hf : flag ∈ support) (hs : scratch ⊆ support) :
    straightWires (equalityProgram n start register value flag scratch).2 ⊆ support := by
  have hx := (circuitWires_subset_of_usesOnly (zeroMask_usesOnly register value)).trans hr
  have hb := vchainProgram_support n start register flag scratch support hr hf hs
  simp only [equalityProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

theorem toggleEqualityProgram_support (n start : Nat) (root : Wire) (register : List Wire)
    (value : Nat) (acc flag : Wire) (scratch support : List Wire)
    (hroot : root ∈ support) (hr : register ⊆ support) (ha : acc ∈ support)
    (hf : flag ∈ support) (hs : scratch ⊆ support) :
    straightWires (toggleEqualityProgram n start root register value acc flag scratch).2 ⊆ support := by
  have hb cursor := equalityProgram_support n cursor register value flag scratch support hr hf hs
  simp only [toggleEqualityProgram,appendCompiled_support,prependCompiled_support,List.append_subset]
  refine ⟨hb _,?_,hb _⟩
  simp [circuitWires,gateWires,hroot,ha,hf]

theorem intervalFirstProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (ht : target ∈ support) (had : addend ∈ support) (hc : carry ∈ support)
    (hs : scratch ∈ support) (hrc : rightControl ∈ support) (hlc : leftControl ∈ support) :
    straightWires (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 ⊆ support := by
  have hr := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl acc)).trans
    (show [rightControl,rightTop,acc] ⊆ support by simp [hrc,hrt,ha])
  have hl := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label leftTop leftControl acc)).trans
    (show [leftControl,leftTop,acc] ⊆ support by simp [hlc,hlt,ha])
  have hb := rippleFirstProgram_support n start mode acc target addend carry scratch support ha ht had hc hs
  simp only [intervalFirstProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hr,hb,hl⟩

theorem intervalSecondProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (ht : target ∈ support) (had : addend ∈ support) (hc : carry ∈ support)
    (hs : scratch ∈ support) (hrc : rightControl ∈ support) (hlc : leftControl ∈ support) :
    straightWires (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 ⊆ support := by
  have hr := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl acc)).trans
    (show [rightControl,rightTop,acc] ⊆ support by simp [hrc,hrt,ha])
  have hl := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label leftTop leftControl acc)).trans
    (show [leftControl,leftTop,acc] ⊆ support by simp [hlc,hlt,ha])
  have hb := rippleSecondProgram_support n start mode acc target addend carry scratch support ha ht had hc hs
  simp only [intervalSecondProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hl,hb,hr⟩


theorem zeroEraseProgram_support (n start : Nat) (a b w : Wire) (support : List Wire)
    (ha : a ∈ support) (hb : b ∈ support) (hw : w ∈ support) :
    straightWires (zeroEraseProgram n start a b w).2 ⊆ support := by
  have he := andEraseProgram_support n start a b w support ha hb hw
  have hx : circuitWires [.X b] ⊆ support := by simp [circuitWires,gateWires,hb]
  simp only [zeroEraseProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,he,hx⟩

theorem dualEraseProgram_support (n start : Nat) (a i x b j y : Wire) (support : List Wire)
    (ha : a ∈ support) (hi : i ∈ support) (hx : x ∈ support)
    (hb : b ∈ support) (hj : j ∈ support) (hy : y ∈ support) :
    straightWires (dualEraseProgram n start a i x b j y).2 ⊆ support := by
  simp only [dualEraseProgram,appendCompiled_support,List.append_subset]
  exact ⟨zeroEraseProgram_support n _ b j y support hb hj hy,
    zeroEraseProgram_support n _ a i x support ha hi hx⟩

private theorem compiledSupportIf {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    straightWires (if b then p else q).2 = if b then straightWires p.2 else straightWires q.2 := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

theorem dualProgram_support (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) (support : List Wire)
    (hleaf : ∀ label ∈ tree.labels, ∀ a b start, a ∈ support → b ∈ support →
      straightWires (leaf label a b start).2 ⊆ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (ha : a ∈ support) (hb : b ∈ support) (hx : xs ⊆ support) (hy : ys ⊆ support) :
    straightWires (dualProgram n order leaf tree a b xs ys start).2 ⊆ support := by
  induction tree generalizing a b xs ys start with
  | leaf label =>
    rw [dualProgram]
    exact hleaf label (by simp [DualUnaryActionTree.labels]) a b start ha hb
  | node i j zero one ihz iho =>
    cases xs with
    | nil => rw [dualProgram] <;> simp [straightWires]
    | cons x xs =>
      cases ys with
      | nil => rw [dualProgram] <;> simp [straightWires]
      | cons y ys =>
        have hix : i ∈ support := hi List.mem_cons_self
        have hjy : j ∈ support := hj List.mem_cons_self
        have hxx : x ∈ support := hx List.mem_cons_self
        have hyy : y ∈ support := hy List.mem_cons_self
        have hz cursor := ihz x y xs ys cursor
          (fun l hl => hleaf l (List.mem_append_left _ hl))
          (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
          (fun _ h => hj (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
          hxx hyy (fun _ h => hx (List.mem_cons_of_mem _ h)) (fun _ h => hy (List.mem_cons_of_mem _ h))
        have ho cursor := iho x y xs ys cursor
          (fun l hl => hleaf l (List.mem_append_right _ hl))
          (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
          (fun _ h => hj (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
          hxx hyy (fun _ h => hx (List.mem_cons_of_mem _ h)) (fun _ h => hy (List.mem_cons_of_mem _ h))
        have he cursor := dualEraseProgram_support n cursor a i x b j y support ha hix hxx hb hjy hyy
        have hca : circuitWires (computeZeroAnd a i x) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,ha,hix,hxx]
        have hcb : circuitWires (computeZeroAnd b j y) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,hb,hjy,hyy]
        have hab : circuitWires [.CX a x,.CX b y] ⊆ support := by simp [circuitWires,gateWires,ha,hb,hxx,hyy]
        have hba : circuitWires [.CX b y,.CX a x] ⊆ support := by simp [circuitWires,gateWires,ha,hb,hxx,hyy]
        rw [dualProgram]
        rw [compiledSupportIf]
        cases order <;> simp only [ite_true,ite_false,reduceCtorEq,prependCompiled_support,appendCompiled_support,List.append_subset]
        · exact ⟨hca,hcb,hz _,hab,ho _,hba,he _⟩
        · exact ⟨hca,hcb,hab,ho _,hba,hz _,he _⟩


theorem topFirstProgram_support (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) (support : List Wire)
    (hr : rightRegister ⊆ support) (hl : leftRegister ⊆ support)
    (ha : acc ∈ support) (ht : target ∈ support) (had : addend ∈ support)
    (hc : carry ∈ support) (hw : work ∈ support) (hf : flag ∈ support)
    (hs : scratch ⊆ support) (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support) :
    straightWires (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 ⊆ support := by
  have hright cursor := toggleEqualityProgram_support n cursor rightRoot rightRegister value acc flag scratch support hrr hr ha hf hs
  have hleft cursor := toggleEqualityProgram_support n cursor leftRoot leftRegister value acc flag scratch support hlr hl ha hf hs
  have hb cursor := rippleFirstProgram_support n cursor mode acc target addend carry work support ha ht had hc hw
  simp only [topFirstProgram,appendCompiled_support,List.append_subset]
  exact ⟨hright _,hb _,hleft _⟩

theorem topSecondProgram_support (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) (support : List Wire)
    (hr : rightRegister ⊆ support) (hl : leftRegister ⊆ support)
    (ha : acc ∈ support) (ht : target ∈ support) (had : addend ∈ support)
    (hc : carry ∈ support) (hw : work ∈ support) (hf : flag ∈ support)
    (hs : scratch ⊆ support) (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support) :
    straightWires (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 ⊆ support := by
  have hright cursor := toggleEqualityProgram_support n cursor rightRoot rightRegister value acc flag scratch support hrr hr ha hf hs
  have hleft cursor := toggleEqualityProgram_support n cursor leftRoot leftRegister value acc flag scratch support hlr hl ha hf hs
  have hb cursor := rippleSecondProgram_support n cursor mode acc target addend carry work support ha ht had hc hw
  simp only [topSecondProgram,appendCompiled_support,List.append_subset]
  exact ⟨hleft _,hb _,hright _⟩

theorem traversalFirstProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (hc : carry ∈ support) (hs : scratch ∈ support)
    (htarget : ∀ l ∈ tree.labels, targetAt l ∈ support)
    (haddend : ∀ l ∈ tree.labels, addendAt l ∈ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support)
    (hrp : rightPaths ⊆ support) (hlp : leftPaths ⊆ support) :
    straightWires (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 ⊆ support := by
  unfold traversalFirstProgram
  apply dualProgram_support n .dec _ tree rightRoot leftRoot rightPaths leftPaths start support
  · intro l hl a b cursor hsa hsb
    exact intervalFirstProgram_support n cursor mode topSpecial rightTop leftTop acc (targetAt l) (addendAt l) carry scratch l a b support hrt hlt ha (htarget l hl) (haddend l hl) hc hs hsa hsb
  · exact hi
  · exact hj
  · exact hrr
  · exact hlr
  · exact hrp
  · exact hlp

theorem traversalSecondProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (hc : carry ∈ support) (hs : scratch ∈ support)
    (htarget : ∀ l ∈ tree.labels, targetAt l ∈ support)
    (haddend : ∀ l ∈ tree.labels, addendAt l ∈ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support)
    (hrp : rightPaths ⊆ support) (hlp : leftPaths ⊆ support) :
    straightWires (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 ⊆ support := by
  unfold traversalSecondProgram
  apply dualProgram_support n .inc _ tree rightRoot leftRoot rightPaths leftPaths start support
  · intro l hl a b cursor hsa hsb
    exact intervalSecondProgram_support n cursor mode topSpecial rightTop leftTop acc (targetAt l) (addendAt l) carry scratch l a b support hrt hlt ha (htarget l hl) (haddend l hl) hc hs hsa hsb
  · exact hi
  · exact hj
  · exact hrr
  · exact hlr
  · exact hrp
  · exact hlp


theorem unaryProgram_support (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat) (support : List Wire)
    (hleaf : ∀ label ∈ tree.labels, ∀ control start, control ∈ support →
      straightWires (leaf label control start).2 ⊆ support)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hp : paths ⊆ support) :
    straightWires (unaryProgram n order leaf tree control paths start).2 ⊆ support := by
  induction tree generalizing control paths start with
  | leaf label =>
    rw [unaryProgram]
    exact hleaf label (by simp [UnaryActionTree.labels]) control start hc
  | node bit zero one ihz iho =>
    cases paths with
    | nil => rw [unaryProgram]; exact List.nil_subset _
    | cons path rest =>
      have hib : bit ∈ support := hi List.mem_cons_self
      have hpath : path ∈ support := hp List.mem_cons_self
      have hz cursor := ihz path rest cursor
        (fun l hl => hleaf l (List.mem_append_left _ hl))
        (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
        hpath (fun _ h => hp (List.mem_cons_of_mem _ h))
      have ho cursor := iho path rest cursor
        (fun l hl => hleaf l (List.mem_append_right _ hl))
        (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
        hpath (fun _ h => hp (List.mem_cons_of_mem _ h))
      have he cursor := zeroEraseProgram_support n cursor control bit path support hc hib hpath
      have hca : circuitWires (computeZeroAnd control bit path) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,hc,hib,hpath]
      have hcx : circuitWires [.CX control path] ⊆ support := by simp [circuitWires,gateWires,hc,hpath]
      rw [unaryProgram,compiledSupportIf]
      cases order <;> simp only [ite_true,ite_false,reduceCtorEq,prependCompiled_support,appendCompiled_support,List.append_subset]
      · exact ⟨hca,hz _,hcx,ho _,hcx,he _⟩
      · exact ⟨hca,hcx,ho _,hcx,hz _,he _⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration
