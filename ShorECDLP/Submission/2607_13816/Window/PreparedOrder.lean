import ShorECDLP.Submission.«2607_13816».Window.PreparedSchedule
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
theorem preparedWindowCallState_pair_commute (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (i j : Nat) (s : BasisState) (hs : WindowPointValid s) :
    preparedWindowCallState x y hc j (preparedWindowCallState x y hc i s)=
      preparedWindowCallState x y hc i (preparedWindowCallState x y hc j s) := by
  obtain ⟨hv,P,hp⟩ := hs
  have hi := preparedWindowCallState_correct x y hc i P s hv hp
  have hj := preparedWindowCallState_correct x y hc j P s hv hp
  have hvi := (preparedWindowCallState_ready x y hc i s ⟨hv,P,hp⟩).1
  have hvj := (preparedWindowCallState_ready x y hc j s ⟨hv,P,hp⟩).1
  have hpi : pointStateCoordinates (preparedWindowCallState x y hc i s)=
      fig14PointEncoding (P+preparedWindowDelta x y hc i s) := by
    rw [hi,pointWrite_coordinates]; rfl
  have hpj : pointStateCoordinates (preparedWindowCallState x y hc j s)=
      fig14PointEncoding (P+preparedWindowDelta x y hc j s) := by
    rw [hj,pointWrite_coordinates]; rfl
  rw [preparedWindowCallState_correct x y hc j _ _ hvi hpi,
    preparedWindowCallState_correct x y hc i _ _ hvj hpj]
  change pointWrite (P+preparedWindowDelta x y hc i s+
      preparedWindowDelta x y hc j (preparedWindowCallState x y hc i s))
      (preparedWindowCallState x y hc i s)=
    pointWrite (P+preparedWindowDelta x y hc j s+
      preparedWindowDelta x y hc i (preparedWindowCallState x y hc j s))
      (preparedWindowCallState x y hc j s)
  rw [hi,hj,preparedWindowDelta_pointWrite,preparedWindowDelta_pointWrite,pointWrite_overwrite,pointWrite_overwrite]
  congr 1
  abel
def preparedWindowListState (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) :
    List Nat → BasisState → BasisState
  | [],s => s
  | j::js,s => preparedWindowListState x y hc js (preparedWindowCallState x y hc j s)
theorem preparedWindowListState_correct (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) (P : ShorECDLP.Secp256k1.Point) (s : BasisState)
    (hv : PointLookupValid s) (hp : pointStateCoordinates s=fig14PointEncoding P) :
    preparedWindowListState x y hc js s=
      pointWrite (P+(js.map (fun j => preparedWindowDelta x y hc j s)).sum) s := by
  induction js generalizing P s with
  | nil =>
    simpa [preparedWindowListState,preparedWindowScheduleState,preparedWindowSum] using
      preparedWindowScheduleState_correct x y hc 0 0 P s hv hp
  | cons j js ih =>
    have he := preparedWindowCallState_correct x y hc j P s hv hp
    have hv' := (preparedWindowCallState_ready x y hc j s ⟨hv,P,hp⟩).1
    have hp' : pointStateCoordinates (preparedWindowCallState x y hc j s)=
        fig14PointEncoding (P+preparedWindowDelta x y hc j s) := by
      rw [he,pointWrite_coordinates]; rfl
    rw [preparedWindowListState,ih _ _ hv' hp',he]
    have hm (Q : ShorECDLP.Secp256k1.Point) :
        js.map (fun k => preparedWindowDelta x y hc k (pointWrite Q s))=
          js.map (fun k => preparedWindowDelta x y hc k s) := by
      apply List.map_congr_left
      intro k hk
      exact preparedWindowDelta_pointWrite x y hc k Q s
    rw [hm,pointWrite_overwrite]
    simp [List.map_cons,List.sum_cons,add_assoc]
theorem preparedWindowListState_reverse (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) (s : BasisState) (hs : WindowPointValid s) :
    preparedWindowListState x y hc js.reverse s=preparedWindowListState x y hc js s := by
  obtain ⟨hv,P,hp⟩ := hs
  rw [preparedWindowListState_correct x y hc js.reverse P s hv hp,
    preparedWindowListState_correct x y hc js P s hv hp]
  simp [List.map_reverse,List.sum_reverse]
def preparedWindowListProgram (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) :
    List Nat → AdaptiveCircuit
  | [] => .done
  | j::js => (preparedWindowCall x y hc j).seq (preparedWindowListProgram x y hc js)
theorem preparedWindowListState_ready (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) (s : BasisState) (hs : WindowPointValid s) :
    WindowPointValid (preparedWindowListState x y hc js s) := by
  induction js generalizing s with
  | nil => exact hs
  | cons j js ih => exact ih _ (preparedWindowCallState_ready x y hc j s hs)
theorem preparedWindowList_coherent (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) : CoherentlyImplementsOn (preparedWindowListProgram x y hc js)
      (Finsupp.lmapDomain ℂ ℂ (preparedWindowListState x y hc js)) WindowPointValid := by
  induction js with
  | nil =>
    refine ⟨[1],?_,by simp⟩
    simp only [preparedWindowListProgram,AdaptiveCircuit.run]
    apply List.Forall₂.cons
    · intro s hs; simp [preparedWindowListState,ket]
    · exact .nil
  | cons j js ih =>
    have h := (preparedWindowCall_coherent x y hc j).seq ih (by
      intro s hs
      simpa [ket] using supportedOn_ket _ _ (preparedWindowCallState_ready x y hc j s hs))
    apply h.congrIdeal
    intro s hs
    simp [LinearMap.comp_apply,ket,preparedWindowListState]
theorem preparedWindowList_reverse_coherent (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) : CoherentlyImplementsOn (preparedWindowListProgram x y hc js.reverse)
      (Finsupp.lmapDomain ℂ ℂ (preparedWindowListState x y hc js)) WindowPointValid := by
  apply (preparedWindowList_coherent x y hc js.reverse).congrIdeal
  intro s hs
  simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket]
  rw [preparedWindowListState_reverse x y hc js s hs]
end
end ShorECDLP.Paper2607_13816
