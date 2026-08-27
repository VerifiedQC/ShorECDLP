import ShorECDLP.Submission.Arithmetic.PointAdd

namespace ShorECDLP
namespace Secp256k1

open Classical
open Arithmetic
open scoped ArithmeticNotation

variable [Fact (Nat.Prime p)]

def controlledPointResult
    (control : Bool)
    (R C : Point) : Point :=
  if control then R + C else R

def controlledPointAddChoice
    (workStart : Wire) : List Wire :=
  List.range' workStart pointWidth

def controlledPointAddPointWorkStart
    (workStart : Wire) : Wire :=
  workStart + pointWidth

def controlledPointAddOutWork
    (workStart : Wire) : List Wire :=
  controlledPointAddChoice workStart ++
    pointAddWork (controlledPointAddPointWorkStart workStart)

def controlledPointAddOut
    (control : Wire)
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C : Point) : Circuit :=
  match C with
  | .zero =>
      Arithmetic.copyReg pointReg outReg
  | @WeierstrassCurve.Affine.Point.some _ _ _ _xC _yC hC =>
      let choice := controlledPointAddChoice workStart
      let pointWorkStart := controlledPointAddPointWorkStart workStart
      let computePoint :=
        pointAddFiniteCompute pointReg pointWorkStart hC
      let choose :=
        selectPoint
          control
          pointReg
          (pointAddSelected pointWorkStart)
          choice
      let compute := computePoint ++ choose
      circuit! {
        compute;
        Arithmetic.copyReg choice outReg;
        compute.reverse
      }

def pointSwapReg :
    List Wire → List Wire → Circuit
  | a :: as, b :: bs =>
      circuit! {
        gate! Gate.CX a b;
        gate! Gate.CX b a;
        gate! Gate.CX a b;
        pointSwapReg as bs
      }
  | _, _ =>
      circuit! {}

def controlledPointAddTemp
    (workStart : Wire) : List Wire :=
  List.range' workStart pointWidth

def controlledPointAddAuxStart
    (workStart : Wire) : Wire :=
  workStart + pointWidth

def controlledPointAddWork
    (workStart : Wire) : List Wire :=
  controlledPointAddTemp workStart ++
    controlledPointAddOutWork
      (controlledPointAddAuxStart workStart)

def controlledPointAdd
    (control : Wire)
    (pointReg : List Wire)
    (workStart : Wire)
    (C : Point) : Circuit :=
  let temp :=
    controlledPointAddTemp workStart
  let auxStart :=
    controlledPointAddAuxStart workStart

  let forward :=
    controlledPointAddOut
      control
      pointReg
      temp
      auxStart
      C

  let backward :=
    controlledPointAddOut
      control
      pointReg
      temp
      auxStart
      (-C)

  circuit! {
    forward;
    pointSwapReg pointReg temp;
    backward.reverse
  }

theorem pointAddFiniteCompute_agrees_pointReg
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean : Clean (pointAddWork workStart) st) :
      AgreesOn pointReg st
        (Classical.run
          (pointAddFiniteCompute pointReg workStart hC) st) := by
  exact
    pointAddFiniteCompute_agrees_pointReg_core
      pointReg outReg workStart hC st
      hpointLength hnodup hclean


  theorem controlledPointAddOut_correct
    (control : Wire)
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (houtLength : outReg.length = pointWidth)
    (hnodup :
      ([control] ++ pointReg ++ outReg ++
        controlledPointAddOutWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean :
      Clean
        (outReg ++ controlledPointAddOutWork workStart)
        st) :
      Classical.run
          (controlledPointAddOut
            control pointReg outReg workStart C)
          st =
        writeReg
          outReg
          (encode
            (controlledPointResult (st control) R C)).val
          st :=
by
  cases C with
  | zero =>
      have hnd :
          (pointReg ++ outReg ++
            controlledPointAddOutWork workStart).Nodup := by
        have h0 :
            (control ::
              (pointReg ++ outReg ++
                controlledPointAddOutWork workStart)).Nodup := by
          simpa only [List.singleton_append, List.append_assoc] using hnodup
        exact (List.nodup_cons.mp h0).2

      have hlen : outReg.length = pointReg.length := by
        rw [houtLength, hpointLength]

      have hcleanOut : Clean outReg st := by
        apply Arithmetic.Clean.mono hclean
        intro w hw
        exact List.mem_append_left _ hw

      have hbound :
          encodeNat R < 2 ^ outReg.length := by
        rw [houtLength]
        exact encodeNat_lt R

      have hcopy :=
        copyReg_eq_writeReg_of_value
          pointReg
          outReg
          (controlledPointAddOutWork workStart)
          st
          (encodeNat R)
          hlen
          hnd
          hcleanOut
          hpoint
          hbound

      change
        Classical.run
            (Arithmetic.copyReg pointReg outReg) st =
          writeReg outReg
            (encode
              (controlledPointResult
                (st control) R 0)).val st

      have hresult :
          controlledPointResult (st control) R 0 = R := by
        cases hc : st control <;>
          simp [controlledPointResult]

      rw [hresult, encode_val]
      exact hcopy

  | some hC =>
      rename_i xC yC

      let choice :=
        controlledPointAddChoice workStart
      let pointWorkStart :=
        controlledPointAddPointWorkStart workStart
      let work :=
        pointAddWork pointWorkStart
      let selected :=
        pointAddSelected pointWorkStart
      let computePoint :=
        pointAddFiniteCompute pointReg pointWorkStart hC
      let choose :=
        selectPoint control pointReg selected choice
      let compute :=
        computePoint ++ choose

      have hnd0 :
          (control ::
            (pointReg ++ outReg ++ choice ++ work)).Nodup := by
        simpa [
          choice,
          work,
          pointWorkStart,
          controlledPointAddOutWork,
          List.append_assoc
        ] using hnodup

      have hcontrolNot :
          control ∉ pointReg ++ outReg ++ choice ++ work :=
        (List.nodup_cons.mp hnd0).1

      have htail :
          (pointReg ++ outReg ++ choice ++ work).Nodup :=
        (List.nodup_cons.mp hnd0).2

      have htailRight :
          (pointReg ++ (outReg ++ (choice ++ work))).Nodup := by
        simpa only [List.append_assoc] using htail

      obtain ⟨hpointNd, hrestNd, hpointRestCross⟩ :=
        List.nodup_append.mp htailRight

      obtain ⟨houtNd, hchoiceWorkNd, houtChoiceWorkCross⟩ :=
        List.nodup_append.mp hrestNd

      obtain ⟨hchoiceNd, hworkNd, hchoiceWorkCross⟩ :=
        List.nodup_append.mp hchoiceWorkNd

      have hpointOutNd :
        (pointReg ++ outReg).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hpointNd, houtNd, ?_⟩
        intro a ha b hb
        exact
          hpointRestCross
            a ha b
            (List.mem_append_left (choice ++ work) hb)

      have hinnerNd :
          (pointReg ++ outReg ++ work).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hpointOutNd, hworkNd, ?_⟩
        intro a ha b hb
        rcases List.mem_append.mp ha with ha | ha
        · exact
            hpointRestCross
              a ha b
              (List.mem_append_right outReg
                (List.mem_append_right choice hb))
        · exact
            houtChoiceWorkCross
              a ha b
              (List.mem_append_right choice hb)

      have hcleanOut :
          Clean outReg st := by
        apply Arithmetic.Clean.mono hclean
        intro w hw
        exact List.mem_append_left _ hw

      have hcleanChoice :
          Clean choice st := by
        apply Arithmetic.Clean.mono hclean
        intro w hw
        exact
          List.mem_append_right outReg
            (List.mem_append_left work hw)

      have hcleanWork :
          Clean work st := by
        apply Arithmetic.Clean.mono hclean
        intro w hw
        exact
          List.mem_append_right outReg
            (List.mem_append_right choice hw)

      obtain ⟨hfreePoint, hwfPoint, husesPoint, hselected⟩ :=
        pointAddFiniteCompute_structural
          pointReg
          outReg
          pointWorkStart
          hC
          (by
            simpa [work] using hinnerNd)

      have hselectedValue :
          regValue selected
              (Classical.run computePoint st) =
            encodeNat (R + (.some hC : Point)) := by
        have h :=
          pointAddFiniteCompute_correct
            pointReg
            outReg
            pointWorkStart
            hC
            R
            st
            hpointLength
            (by
              simpa [work] using hinnerNd)
            hpoint
            (by
              simpa [work] using hcleanWork)

        rw [affineAdd_correct] at h
        simpa [selected, computePoint] using h

      have hpointAgree :=
        pointAddFiniteCompute_agrees_pointReg
          pointReg
          outReg
          pointWorkStart
          hC
          st
          hpointLength
          (by
            simpa [work] using hinnerNd)
          (by
            simpa [work] using hcleanWork)

      have regValue_eq_of_agrees :
          ∀ (ws : List Wire) (s₁ s₂ : BasisState),
            AgreesOn ws s₁ s₂ →
            regValue ws s₂ = regValue ws s₁ := by
        intro ws
        induction ws with
        | nil =>
            intro s₁ s₂ h
            rfl
        | cons w ws ih =>
            intro s₁ s₂ h
            rw [regValue_cons, regValue_cons]

            have hw : s₂ w = s₁ w := by
              exact h w (List.mem_cons_self)

            have htail : AgreesOn ws s₁ s₂ := by
              intro u hu
              exact h u (List.mem_cons_of_mem w hu)

            rw [hw, ih s₁ s₂ htail]

      have hpointAgree' :
          AgreesOn pointReg st
            (Classical.run computePoint st) := by
        simpa [computePoint] using hpointAgree

      have hpointAfter :
          regValue pointReg
              (Classical.run computePoint st) =
            encodeNat R := by
        calc
          regValue pointReg
              (Classical.run computePoint st) =
              regValue pointReg st := by
            exact
              regValue_eq_of_agrees
                pointReg
                st
                (Classical.run computePoint st)
                hpointAgree'
          _ = encodeNat R := hpoint
      have hcontrolOutside :
          control ∉ pointReg ++ work := by
        intro hc
        apply hcontrolNot
        rcases List.mem_append.mp hc with hp | hw
        · simpa only [List.append_assoc] using
            List.mem_append_left
              (outReg ++ choice ++ work) hp
        · simpa only [List.append_assoc] using
            List.mem_append_right pointReg
              (List.mem_append_right outReg
                (List.mem_append_right choice hw))

      have hpresPoint :
          PreservesOutside
            (pointReg ++ work)
            computePoint := by
        simpa [computePoint, work] using
          CircuitUsesOnly.preservesOutside husesPoint

      have hcontrolAfter :
          Classical.run computePoint st control =
            st control := by
        exact
          hpresPoint st control hcontrolOutside

      have hchoiceOutside :
          ∀ w ∈ choice,
            w ∉ pointReg ++ work := by
        intro w hw hc
        rcases List.mem_append.mp hc with hp | hwork
        · exact
            (hpointRestCross
              w hp w
              (List.mem_append_right outReg
                (List.mem_append_left work hw))) rfl
        · exact
            (hchoiceWorkCross
              w hw w hwork) rfl

      have hcleanChoiceAfter :
          Clean choice
            (Classical.run computePoint st) := by
        intro w hw
        rw [hpresPoint st w (hchoiceOutside w hw)]
        exact hcleanChoice w hw

      have hselectedNd :
          selected.Nodup := by
        dsimp [selected, pointAddSelected]
        exact List.nodup_range'

      have hselectedChoiceNd :
          (selected ++ choice).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hselectedNd, hchoiceNd, ?_⟩
        intro a ha b hb

        have haWork : a ∈ work := by
          dsimp [work]
          apply hselected a
          simpa [selected] using ha

        exact
          (hchoiceWorkCross b hb a haWork).symm

      have hpointSelectedNd :
          (pointReg ++ selected).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hpointNd, hselectedNd, ?_⟩
        intro a ha b hb

        have hbWork : b ∈ work := by
          dsimp [work]
          apply hselected b
          simpa [selected] using hb

        exact
          hpointRestCross
            a ha b
            (List.mem_append_right outReg
              (List.mem_append_right choice hbWork))

      have hpointSelectedChoiceNd :
          (pointReg ++ selected ++ choice).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hpointSelectedNd, hchoiceNd, ?_⟩
        intro a ha b hb

        rcases List.mem_append.mp ha with ha | ha
        · exact
            hpointRestCross
              a ha b
              (List.mem_append_right outReg
                (List.mem_append_left work hb))

        · have haWork : a ∈ work := by
            dsimp [work]
            apply hselected a
            simpa [selected] using ha

          exact
            (hchoiceWorkCross
              b hb a haWork).symm

      have hselectNd :
          (control :: (pointReg ++ selected ++ choice)).Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_, hpointSelectedChoiceNd⟩
        intro hc
        apply hcontrolNot

        simp only [List.mem_append] at hc ⊢

        rcases hc with (hp | hs) | hc
        · exact Or.inl (Or.inl (Or.inl hp))

        · have hsWork : control ∈ work := by
            dsimp [work]
            apply hselected control
            simpa [selected] using hs

          exact Or.inr hsWork

        · exact Or.inl (Or.inr hc)

      have hselectedLength :
          selected.length = pointWidth := by
        simp [selected, pointAddSelected]

      have hchoiceLength :
          choice.length = pointWidth := by
        simp [choice, controlledPointAddChoice]

      have hselectOK :
          selectOK control pointReg selected choice := by
        have aux :
            ∀ (xs ys outs : List Wire),
              xs.length = ys.length →
              xs.length = outs.length →
              (control :: (xs ++ ys ++ outs)).Nodup →
              selectOK control xs ys outs := by
          intro xs
          induction xs with
          | nil =>
              intro ys outs hxy hxo _
              cases ys <;> cases outs <;> simp [selectOK] at hxy hxo ⊢

          | cons x xs ih =>
              intro ys outs hxy hxo hnd

              cases ys with
              | nil =>
                  simp at hxy

              | cons y ys =>
                  cases outs with
                  | nil =>
                      simp at hxo

                  | cons o outs =>
                      have hxy' :
                          xs.length = ys.length := by
                        simpa using hxy

                      have hxo' :
                          xs.length = outs.length := by
                        simpa using hxo

                      have hcontrolTail :=
                        (List.nodup_cons.mp hnd).1

                      have htail :=
                        (List.nodup_cons.mp hnd).2

                      have htail' :
                          ((x :: xs) ++ ((y :: ys) ++ (o :: outs))).Nodup := by
                        simpa [List.append_assoc] using htail

                      obtain ⟨hxsNd, hrestNd, hxsRestCross⟩ :=
                        List.nodup_append.mp htail'

                      obtain ⟨hysNd, houtsNd, hysOutCross⟩ :=
                        List.nodup_append.mp hrestNd

                      have hoTail :
                          o ∉ outs :=
                        (List.nodup_cons.mp houtsNd).1

                      have htailNd :
                          (control :: xs ++ ys ++ outs).Nodup := by
                        apply List.Nodup.sublist _ hnd
                        apply List.Sublist.cons₂
                        have hxs : xs.Sublist (x :: xs) :=
                          List.Sublist.cons x (List.Sublist.refl xs)
                        have hys : ys.Sublist (y :: ys) :=
                          List.Sublist.cons y (List.Sublist.refl ys)
                        have houts : outs.Sublist (o :: outs) :=
                          List.Sublist.cons o (List.Sublist.refl outs)
                        exact (hxs.append hys).append houts

                      simp only [selectOK]

                      refine
                        ⟨
                          hxsRestCross
                            x
                            (List.mem_cons_self)
                            y
                            (List.mem_append_left _
                              (List.mem_cons_self)),
                          hxsRestCross
                            x
                            (List.mem_cons_self)
                            o
                            (List.mem_append_right (y :: ys)
                              (List.mem_cons_self)),
                          hysOutCross
                            y
                            (List.mem_cons_self)
                            o
                            (List.mem_cons_self),
                          ?_,
                          ?_,
                          ?_,
                          hoTail,
                          ?_,
                          ?_,
                          ?_,
                          ?_,
                          ih ys outs hxy' hxo' htailNd
                        ⟩

                      · intro h
                        subst x
                        apply hcontrolTail
                        simp

                      · intro h
                        subst y
                        apply hcontrolTail
                        simp

                      · intro h
                        subst o
                        apply hcontrolTail
                        simp

                      · intro hx
                        exact
                          (hxsRestCross
                            x
                            (List.mem_cons_self)
                            x
                            (List.mem_append_right (y :: ys)
                              (List.mem_cons_of_mem o hx))) rfl

                      · intro hy
                        exact
                          (hysOutCross
                            y
                            (List.mem_cons_self)
                            y
                            (List.mem_cons_of_mem o hy)) rfl

                      · intro x' hx' hEq
                        exact
                          hxsRestCross
                            x'
                            (List.mem_cons_of_mem x hx')
                            o
                            (List.mem_append_right (y :: ys)
                              (List.mem_cons_self))
                            hEq

                      · intro y' hy' hEq
                        exact
                          hysOutCross
                            y'
                            (List.mem_cons_of_mem y hy')
                            o
                            (List.mem_cons_self)
                            hEq

        exact
          aux
            pointReg
            selected
            choice
            (by
              rw [hpointLength, hselectedLength])
            (by
              rw [hpointLength, hchoiceLength])
            hselectNd

      have hchoiceValue :
          regValue choice
              (Classical.run compute st) =
            encodeNat
              (controlledPointResult
                (st control) R (.some hC)) := by
        have hrun :
            Classical.run compute st =
              Classical.run choose
                (Classical.run computePoint st) := by
          simp [compute, Classical.run_append]

        rw [hrun]

        have hsel :=
          selectPoint_correct
            control
            pointReg
            selected
            choice
            (Classical.run computePoint st)
            hselectOK
            hcleanChoiceAfter

        rw [
          hcontrolAfter,
          hselectedValue,
          hpointAfter
        ] at hsel

        cases hc : st control <;>
          simp [choose, controlledPointResult, hc] at hsel ⊢ <;>
          exact hsel

      have hfreeCompute :
          Classical.HPFree compute := by
        rw [
          show compute = computePoint ++ choose by rfl,
          Classical.hpFree_append
        ]
        exact
          ⟨hfreePoint,
            selectPoint_HPFree
              control pointReg selected choice⟩

      have hwfCompute :
          CircuitWellFormed compute := by
        rw [
          show compute = computePoint ++ choose by rfl,
          circuitWellFormed_append
        ]
        exact
          ⟨
            hwfPoint,
            selectPoint_wellFormed
              control
              pointReg
              selected
              choice
              hselectOK
          ⟩

      have husesPoint' :
          CircuitUsesOnly
            ((control :: pointReg) ++ choice ++ work)
            computePoint := by
        apply Arithmetic.usesOnly_mono husesPoint
        intro w hw
        rcases List.mem_append.mp hw with hp | hw
        · simp only [List.mem_cons, List.mem_append]
          exact Or.inl (Or.inl (Or.inr hp))
        · simp only [List.mem_cons, List.mem_append]
          exact Or.inr hw

      have husesChoose :
          CircuitUsesOnly
            ((control :: pointReg) ++ choice ++ work)
            choose := by
        apply Arithmetic.usesOnly_mono
          (selectPoint_usesOnly
            control pointReg selected choice)

        intro w hw

        simp only [
          selectFootprint,
          List.mem_cons,
          List.mem_append
        ] at hw

        rcases hw with ((rfl | hp) | hs) | hc
        · simp

        · simp [List.mem_append, hp]

        · have hsWork : w ∈ work := by
            dsimp [work]
            apply hselected w
            simpa [selected] using hs

          simp [List.mem_append, hsWork]

        · simp [List.mem_append, hc]

      have husesCompute :
          CircuitUsesOnly
            ((control :: pointReg) ++ choice ++ work)
            compute := by
        exact
          Arithmetic.usesOnly_append
            husesPoint'
            husesChoose

      have hlen :
          outReg.length = choice.length := by
        rw [houtLength, hchoiceLength]

      let value :=
        encodeNat
          (controlledPointResult
            (st control) R (.some hC))

      have hbound :
          value < 2 ^ outReg.length := by
        dsimp [value]
        rw [houtLength]
        exact encodeNat_lt _

      have hbennett :=
        bennett_copyReg_eq_writeReg
          compute
          (control :: pointReg)
          choice
          outReg
          (choice ++ work)
          st
          value
          hfreeCompute
          hwfCompute
          (by
            simpa [List.append_assoc] using husesCompute)
          (fun w hw =>
            List.mem_append_left work hw)
          (by
            simpa [List.append_assoc] using hnd0)
          hlen
          hcleanOut
          (by
            simpa [value] using hchoiceValue)
          hbound

      change
        Classical.run
          (circuit! {
            compute;
            Arithmetic.copyReg choice outReg;
            compute.reverse
          }) st =
        writeReg outReg
          (encode
            (controlledPointResult
              (st control) R (.some hC))).val st

      rw [encode_val]
      simpa [value] using hbennett

  omit [Fact (Nat.Prime p)] in
  theorem pointSwapReg_HPFree
    (xs ys : List Wire) :
    Classical.HPFree (pointSwapReg xs ys) := by
  induction xs generalizing ys with
  | nil =>
      simp [pointSwapReg]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [pointSwapReg]
      | cons y ys =>
          simp [pointSwapReg, ih]

omit [Fact (Nat.Prime p)] in
theorem pointSwapReg_wellFormed
    (xs ys : List Wire)
    (hnodup : (xs ++ ys).Nodup) :
    CircuitWellFormed (pointSwapReg xs ys) := by
  induction xs generalizing ys with
  | nil =>
      simp [pointSwapReg]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [pointSwapReg]
      | cons y ys =>
          have hxy : x ≠ y := by
            intro h
            subst y
            simp only [List.cons_append, List.nodup_cons] at hnodup
            exact hnodup.1 (by simp)
          have htail : (xs ++ ys).Nodup := by
            have h :=
              (List.nodup_append.mp
                ((List.nodup_cons.mp hnodup).2))
            exact List.nodup_append.mpr
              ⟨h.1, (List.nodup_cons.mp h.2.1).2,
                fun a ha b hb => h.2.2 a ha b
                  (List.mem_cons_of_mem y hb)⟩
          simp [pointSwapReg, Gate.WellFormed, hxy, ih ys htail]
          aesop

omit [Fact (Nat.Prime p)] in
theorem pointSwapReg_correct
    (xs ys rest : List Wire)
    (st : BasisState)
    (value : Nat)
    (hlen : xs.length = ys.length)
    (hnodup : (xs ++ ys ++ rest).Nodup) :
    Classical.run
        (pointSwapReg xs ys)
        (writeReg ys value st) =
      writeReg ys
        (regValue xs st)
        (writeReg xs value st) := by
  have writeReg_other_local :
      ∀ (ws : List Wire) (n : Nat) (s : BasisState) (i : Wire),
        i ∉ ws → writeReg ws n s i = s i := by
    intro ws
    induction ws with
    | nil =>
        intro n s i h
        rfl
    | cons w ws ih =>
        intro n s i h
        simp only [List.mem_cons, not_or] at h
        simp only [writeReg]
        rw [ih (n / 2) (s[w ↦ n.testBit 0]) i h.2]
        exact upd_other s w (n.testBit 0) h.1

  have writeReg_upd_not_mem_local :
      ∀ (ws : List Wire) (n : Nat) (s : BasisState)
        (i : Wire) (b : Bool),
        i ∉ ws →
        writeReg ws n (s[i ↦ b]) =
          (writeReg ws n s)[i ↦ b] := by
    intro ws
    induction ws with
    | nil =>
        intro n s i b h
        rfl
    | cons w ws ih =>
        intro n s i b h
        simp only [List.mem_cons, not_or] at h
        simp only [writeReg]
        have hcomm :
            (s[i ↦ b])[w ↦ n.testBit 0] =
              (s[w ↦ n.testBit 0])[i ↦ b] := by
          funext j
          by_cases hji : j = i <;>
            by_cases hjw : j = w <;>
              simp [upd, hji, hjw, h.1, Ne.symm h.1]
        rw [hcomm]
        exact ih (n / 2) (s[w ↦ n.testBit 0]) i b h.2

  have run_swap_local
      (a b : Wire) (s : BasisState) (hab : a ≠ b) :
      Classical.run
          [Gate.CX a b, Gate.CX b a, Gate.CX a b]
          s =
        (s[a ↦ s b])[b ↦ s a] := by
    funext w
    by_cases hwa : w = a
    · subst w
      cases ha : s a <;>
        cases hb : s b <;>
          simp [Classical.run_cons, Classical.run_nil,
            Classical.applyGate, upd, hab, Ne.symm hab, ha, hb]
    · by_cases hwb : w = b
      · subst w
        cases ha : s a <;>
          cases hb : s b <;>
            simp [Classical.run_cons, Classical.run_nil,
              Classical.applyGate, upd, hab, Ne.symm hab, ha, hb]
      · simp [Classical.run_cons, Classical.run_nil,
          Classical.applyGate, upd, hwa, hwb, hab, Ne.symm hab]

  induction xs generalizing ys st value with
  | nil =>
      have hys : ys = [] := by
        exact List.length_eq_zero_iff.mp hlen.symm
      subst ys
      simp [pointSwapReg, writeReg]

  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hlen

      | cons y ys =>
          have hlen' : xs.length = ys.length := by
            simpa using hlen

          obtain ⟨hxynd, hrestnd, hcrossRest⟩ :=
            List.nodup_append.mp hnodup
          obtain ⟨hxsnd, hysnd, hcross⟩ :=
            List.nodup_append.mp hxynd

          have hxxs : x ∉ xs :=
            (List.nodup_cons.mp hxsnd).1

          have hyys : y ∉ ys :=
            (List.nodup_cons.mp hysnd).1

          have hxy : x ≠ y :=
            hcross x (List.mem_cons_self ..)
              y (List.mem_cons_self ..)

          have hxys : x ∉ ys := by
            intro hx
            exact
              (hcross x (List.mem_cons_self ..)
                x (List.mem_cons_of_mem y hx)) rfl

          have hyxs : y ∉ xs := by
            intro hy
            exact
              (hcross y (List.mem_cons_of_mem x hy)
                y (List.mem_cons_self ..)) rfl

          have htailXY : (xs ++ ys).Nodup := by
            apply List.nodup_append.mpr
            refine ⟨
              (List.nodup_cons.mp hxsnd).2,
              (List.nodup_cons.mp hysnd).2,
              ?_⟩
            intro a ha b hb
            exact
              hcross a (List.mem_cons_of_mem x ha)
                b (List.mem_cons_of_mem y hb)

          have htail : (xs ++ ys ++ rest).Nodup := by
            apply List.nodup_append.mpr
            refine ⟨htailXY, hrestnd, ?_⟩
            intro a ha b hb
            apply hcrossRest a
            · rcases List.mem_append.mp ha with ha | ha
              · exact List.mem_append.mpr
                  (Or.inl (List.mem_cons_of_mem x ha))
              · exact List.mem_append.mpr
                  (Or.inr (List.mem_cons_of_mem y ha))
            · exact hb

          let bit : Bool := value.testBit 0
          let base : BasisState :=
            writeReg ys (value / 2) st
          let st' : BasisState :=
            (st[x ↦ bit])[y ↦ st x]

          have hprep :
              writeReg (y :: ys) value st =
                base[y ↦ bit] := by
            simpa [base, bit, writeReg] using
              writeReg_upd_not_mem_local
                ys (value / 2) st y bit hyys

          have hxbase : base x = st x := by
            exact
              writeReg_other_local
                ys (value / 2) st x hxys

          have htarget :
              writeReg ys (value / 2) st' =
                (base[x ↦ bit])[y ↦ st x] := by
            dsimp [st', base]
            rw [writeReg_upd_not_mem_local
              ys (value / 2) (st[x ↦ bit]) y (st x) hyys]
            rw [writeReg_upd_not_mem_local
              ys (value / 2) st x bit hxys]

          have hswap :
              Classical.run
                  [Gate.CX x y, Gate.CX y x, Gate.CX x y]
                  (writeReg (y :: ys) value st) =
                writeReg ys (value / 2) st' := by
            rw [hprep, run_swap_local x y _ hxy, htarget]
            rw [upd_same, upd_other _ _ _ hxy, hxbase]
            funext w
            by_cases hwx : w = x <;>
              by_cases hwy : w = y <;>
                simp [upd, hwx, hwy, hxy]

          have hreg :
              regValue xs st' = regValue xs st := by
            dsimp [st']
            rw [regValue_upd_not_mem
              xs (st[x ↦ bit]) y (st x) hyxs]
            rw [regValue_upd_not_mem
              xs st x bit hxxs]

          have hih :=
            ih ys st' (value / 2) hlen' htail

          have hdiv :
              regValue (x :: xs) st / 2 =
                regValue xs st := by
            rw [regValue_cons]
            cases st x
            · simp
            · simp
              omega

          have hbit :
              (regValue (x :: xs) st).testBit 0 =
                st x := by
            rw [regValue_cons]
            cases hx : st x <;> simp

          rw [pointSwapReg]
          change
            Classical.run (pointSwapReg xs ys)
              (Classical.run
                [Gate.CX x y, Gate.CX y x, Gate.CX x y]
                (writeReg (y :: ys) value st)) =
              writeReg (y :: ys)
                (regValue (x :: xs) st)
                (writeReg (x :: xs) value st)
          rw [hswap, hih, hreg]
          simp only [writeReg]
          rw [hdiv, hbit]
          dsimp [st', bit]
          rw [writeReg_upd_not_mem_local
            xs (value / 2) (st[x ↦ value.testBit 0])
            y (st x) hyxs]

omit [Fact (Nat.Prime p)] in
theorem controlledPointAddOut_HPFree
    (control : Wire)
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C : Point) :
    Classical.HPFree
      (controlledPointAddOut
        control pointReg outReg workStart C) := by
  cases C with
  | zero =>
      simp [controlledPointAddOut, Arithmetic.copyReg_HPFree]
  | some hC =>
      rename_i xC yC
      simp only [controlledPointAddOut]
      let choice := controlledPointAddChoice workStart
      let pointWorkStart := controlledPointAddPointWorkStart workStart
      let computePoint := pointAddFiniteCompute pointReg pointWorkStart hC
      let choose :=
        selectPoint control pointReg
          (pointAddSelected pointWorkStart) choice
      let compute := computePoint ++ choose

      have hcomputePoint : Classical.HPFree computePoint := by
        exact pointAddFiniteCompute_HPFree pointReg pointWorkStart hC

      have hchoose : Classical.HPFree choose := by
        exact selectPoint_HPFree _ _ _ _

      simpa [compute, choice] using
        And.intro hcomputePoint
          (And.intro hchoose
            (And.intro
              (Arithmetic.hpFree_reverse hchoose)
              (Arithmetic.hpFree_reverse hcomputePoint)))

omit [Fact (Nat.Prime p)] in
theorem controlledPointAddOut_wellFormed
    (control : Wire)
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C : Point)
    (hpointLength :
      pointReg.length = pointWidth)
    (_houtLength :
      outReg.length = pointWidth)
    (hnodup :
      ([control] ++ pointReg ++ outReg ++
        controlledPointAddOutWork workStart).Nodup) :
    CircuitWellFormed
      (controlledPointAddOut
        control pointReg outReg workStart C) := by
  cases C with
  | zero =>
      have h0 :
          (control ::
            (pointReg ++ outReg ++ controlledPointAddOutWork workStart)).Nodup := by
        simpa [List.append_assoc] using hnodup

      have htail :=
        (List.nodup_cons.mp h0).2

      have hcopyNd : (pointReg ++ outReg).Nodup := by
        simpa [controlledPointAddOutWork, List.append_assoc] using
          (List.nodup_append.mp htail).1

      change CircuitWellFormed
        (Arithmetic.copyReg pointReg outReg)
      exact Arithmetic.copyReg_wellFormed pointReg outReg hcopyNd

  | some hC =>
      rename_i xC yC

      let choice := controlledPointAddChoice workStart
      let pointWorkStart :=
        controlledPointAddPointWorkStart workStart
      let work := pointAddWork pointWorkStart
      let selected := pointAddSelected pointWorkStart
      let computePoint :=
        pointAddFiniteCompute pointReg pointWorkStart hC
      let choose :=
        selectPoint control pointReg selected choice
      let compute := computePoint ++ choose

      have h0 :
          (control ::
            (pointReg ++ outReg ++ choice ++ work)).Nodup := by
        simpa [choice, pointWorkStart, work,
          controlledPointAddOutWork, List.append_assoc] using hnodup

      have hcontrolNot :
          control ∉ pointReg ++ outReg ++ choice ++ work :=
        (List.nodup_cons.mp h0).1

      have hrestNd :
          (pointReg ++ outReg ++ choice ++ work).Nodup :=
        (List.nodup_cons.mp h0).2

      obtain ⟨hprefixNd, hworkNd, hprefixWorkCross⟩ :=
        List.nodup_append.mp hrestNd
      obtain ⟨hpointOutNd, hchoiceNd, hpointOutChoiceCross⟩ :=
        List.nodup_append.mp hprefixNd
      obtain ⟨hpointNd, houtNd, hpointOutCross⟩ :=
        List.nodup_append.mp hpointOutNd

      have houtWorkNd : (outReg ++ work).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨houtNd, hworkNd, ?_⟩
        intro x hx y hy
        exact hprefixWorkCross x
          (List.mem_append_left choice
            (List.mem_append_right pointReg hx))
          y hy

      have hcomputeNd :
          (pointReg ++ outReg ++ work).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hpointOutNd, hworkNd, ?_⟩
        intro x hx y hy
        exact hprefixWorkCross x
          (List.mem_append_left choice hx)
          y hy

      obtain ⟨_, hwfComputePoint, _, hselected⟩ :=
        pointAddFiniteCompute_structural
          pointReg
          outReg
          pointWorkStart
          hC
          (by simpa [work] using hcomputeNd)

      have hcontrolPoint :
          ∀ x ∈ pointReg, control ≠ x := by
        intro x hx h
        apply hcontrolNot
        rw [h]
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl hx))

      have hcontrolChoice :
          ∀ x ∈ choice, control ≠ x := by
        intro x hx h
        apply hcontrolNot
        rw [h]
        simp only [List.mem_append]
        exact Or.inl (Or.inr hx)

      have hcontrolSelected :
          ∀ x ∈ selected, control ≠ x := by
        intro x hx h
        apply hcontrolNot
        rw [h]
        simp only [List.mem_append]
        exact Or.inr
          (by
            simpa [work] using
              hselected x (by simpa [selected] using hx))

      have hpointChoice :
          ∀ x ∈ pointReg, ∀ y ∈ choice, x ≠ y := by
        intro x hx y hy
        exact hpointOutChoiceCross x
          (List.mem_append_left outReg hx)
          y hy

      have hpointSelected :
          ∀ x ∈ pointReg, ∀ y ∈ selected, x ≠ y := by
        intro x hx y hy
        exact hprefixWorkCross x
          (List.mem_append_left choice
            (List.mem_append_left outReg hx))
          y
          (by
            simpa [work] using
              hselected y (by simpa [selected] using hy))

      have hselectedChoice :
          ∀ x ∈ selected, ∀ y ∈ choice, x ≠ y := by
        intro x hx y hy
        exact
          (hprefixWorkCross y
            (List.mem_append_right (pointReg ++ outReg) hy)
            x
            (by
              simpa [work] using
                hselected x (by simpa [selected] using hx))).symm

      have hselectOKAux :
          ∀ (xs ys outs : List Wire),
            xs.length = ys.length →
            xs.length = outs.length →
            (∀ w ∈ xs, w ∈ pointReg) →
            (∀ w ∈ ys, w ∈ selected) →
            (∀ w ∈ outs, w ∈ choice) →
            outs.Nodup →
            selectOK control xs ys outs := by
        intro xs
        induction xs with
        | nil =>
            intro ys outs hxy hxo _ _ _ _
            cases ys with
            | nil =>
                cases outs with
                | nil => simp [selectOK]
                | cons o outs => simp at hxo
            | cons y ys =>
                simp at hxy

        | cons x xs ih =>
            intro ys outs hxy hxo hxs hys houts houtsNd
            cases ys with
            | nil =>
                simp at hxy
            | cons y ys =>
                cases outs with
                | nil =>
                    simp at hxo
                | cons o outs =>
                    have hxy' : xs.length = ys.length := by
                      simpa using hxy
                    have hxo' : xs.length = outs.length := by
                      simpa using hxo

                    have hxPoint :
                        x ∈ pointReg :=
                      hxs x (List.mem_cons_self ..)
                    have hySelected :
                        y ∈ selected :=
                      hys y (List.mem_cons_self ..)
                    have hoChoice :
                        o ∈ choice :=
                      houts o (List.mem_cons_self ..)

                    obtain ⟨hoTail, houtsTailNd⟩ :=
                      List.nodup_cons.mp houtsNd

                    simp only [selectOK]
                    refine ⟨
                      hpointSelected x hxPoint y hySelected,
                      hpointChoice x hxPoint o hoChoice,
                      hselectedChoice y hySelected o hoChoice,
                      hcontrolPoint x hxPoint,
                      hcontrolSelected y hySelected,
                      hcontrolChoice o hoChoice,
                      hoTail,
                      ?_,
                      ?_,
                      ?_,
                      ?_,
                      ?_
                    ⟩

                    · intro hxout
                      exact
                        (hpointChoice x hxPoint x
                          (houts x
                            (List.mem_cons_of_mem o hxout))) rfl

                    · intro hyout
                      exact
                        (hselectedChoice y hySelected y
                          (houts y
                            (List.mem_cons_of_mem o hyout))) rfl

                    · intro x' hx' hEq
                      exact
                        hpointChoice
                          x'
                          (hxs x'
                            (List.mem_cons_of_mem x hx'))
                          o
                          hoChoice
                          hEq

                    · intro y' hy' hEq
                      exact
                        hselectedChoice
                          y'
                          (hys y'
                            (List.mem_cons_of_mem y hy'))
                          o
                          hoChoice
                          hEq

                    · exact ih ys outs hxy' hxo'
                        (fun w hw =>
                          hxs w (List.mem_cons_of_mem x hw))
                        (fun w hw =>
                          hys w (List.mem_cons_of_mem y hw))
                        (fun w hw =>
                          houts w (List.mem_cons_of_mem o hw))
                        houtsTailNd

      have hselectedLength :
          selected.length = pointWidth := by
        simp [selected, pointAddSelected]

      have hchoiceLength :
          choice.length = pointWidth := by
        simp [choice, controlledPointAddChoice]

      have hpointSelectedLength :
          pointReg.length = selected.length := by
        rw [hpointLength, hselectedLength]

      have hpointChoiceLength :
          pointReg.length = choice.length := by
        rw [hpointLength, hchoiceLength]

      have hselectOK :
          selectOK control pointReg selected choice := by
        exact hselectOKAux
          pointReg selected choice
          hpointSelectedLength
          hpointChoiceLength
          (fun w hw => hw)
          (fun w hw => hw)
          (fun w hw => hw)
          hchoiceNd

      have hwfChoose :
          CircuitWellFormed choose := by
        exact selectPoint_wellFormed
          control pointReg selected choice hselectOK

      have hwfCompute :
          CircuitWellFormed compute := by
        dsimp [compute]
        rw [circuitWellFormed_append]
        exact ⟨hwfComputePoint, hwfChoose⟩

      have hcopyNd : (choice ++ outReg).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hchoiceNd, houtNd, ?_⟩
        intro x hx y hy
        exact
          (hpointOutChoiceCross y
            (List.mem_append_right pointReg hy)
            x hx).symm

      have hwfCopy :
          CircuitWellFormed
            (Arithmetic.copyReg choice outReg) :=
        Arithmetic.copyReg_wellFormed choice outReg hcopyNd

      have hwfReverse :
          CircuitWellFormed compute.reverse :=
        Arithmetic.wellFormed_reverse hwfCompute

      change
        CircuitWellFormed
          ((compute ++ Arithmetic.copyReg choice outReg) ++
            compute.reverse)

      rw [circuitWellFormed_append, circuitWellFormed_append]
      exact ⟨⟨hwfCompute, hwfCopy⟩, hwfReverse⟩

theorem controlledPointAddOut_reverse_correct
    (control : Wire)
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C R : Point)
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (houtLength :
      outReg.length = pointWidth)
    (hnodup :
      ([control] ++ pointReg ++ outReg ++
        controlledPointAddOutWork workStart).Nodup)
    (_hpoint : regValue pointReg st = encodeNat R)
    (hclean :
      Clean
        (outReg ++ controlledPointAddOutWork workStart)
        st) :
    let result :=
      controlledPointResult (st control) R C
    Classical.run
        (controlledPointAddOut
          control pointReg outReg workStart (-C)).reverse
        (writeReg outReg
          (encodeNat R)
          (writeReg pointReg (encode result).val st)) =
      writeReg pointReg (encode result).val st := by

  dsimp only

  have writeReg_other_local :
      ∀ (ws : List Wire) (n : Nat) (s : BasisState) (i : Wire),
        i ∉ ws → writeReg ws n s i = s i := by
    intro ws
    induction ws with
    | nil =>
        intro n s i h
        rfl
    | cons w ws ih =>
        intro n s i h
        simp only [List.mem_cons, not_or] at h
        simp only [writeReg]
        rw [ih (n / 2) (s[w ↦ n.testBit 0]) i h.2]
        exact upd_other s w (n.testBit 0) h.1

  have regValue_writeReg_local :
      ∀ (ws : List Wire) (n : Nat) (s : BasisState),
        ws.Nodup →
        n < 2 ^ ws.length →
        regValue ws (writeReg ws n s) = n := by
    intro ws
    induction ws with
    | nil =>
        intro n s hnd hn
        simp at hn
        subst n
        rfl
    | cons w ws ih =>
        intro n s hnd hn
        have hw : w ∉ ws :=
          (List.nodup_cons.mp hnd).1
        have hnd' : ws.Nodup :=
          (List.nodup_cons.mp hnd).2

        have hn2 : n < 2 ^ ws.length * 2 := by
          simpa [pow_succ] using hn

        have hn' : n / 2 < 2 ^ ws.length := by
          omega

        simp only [writeReg, regValue_cons]

        rw [writeReg_other_local
          ws (n / 2) (s[w ↦ n.testBit 0]) w hw]
        rw [upd_same]
        rw [ih (n / 2) (s[w ↦ n.testBit 0]) hnd' hn']

        have hbit :
            (if n.testBit 0 then 1 else 0) = n % 2 := by
          cases hb : n.testBit 0 with
          | false =>
              have hm : n % 2 = 0 :=
                (Nat.mod_two_eq_zero_iff_testBit_zero).2 hb
              simp [hm]
          | true =>
              have hm : n % 2 = 1 :=
                (Nat.mod_two_eq_one_iff_testBit_zero).2 hb
              simp [hm]

        rw [hbit]
        have hsplit := Nat.mod_add_div n 2
        omega

  let result :=
    controlledPointResult (st control) R C

  let base :=
    writeReg pointReg (encode result).val st

  let work :=
    controlledPointAddOutWork workStart

  let program :=
    controlledPointAddOut
      control pointReg outReg workStart (-C)

  change
    Classical.run program.reverse
        (writeReg outReg (encodeNat R) base) =
      base

  have hnd0 :
      (control :: (pointReg ++ outReg ++ work)).Nodup := by
    simpa [work, List.append_assoc] using hnodup

  have hcontrolOutside :
      control ∉ pointReg ++ outReg ++ work :=
    (List.nodup_cons.mp hnd0).1

  have htail :
      (pointReg ++ outReg ++ work).Nodup :=
    (List.nodup_cons.mp hnd0).2

  obtain ⟨hpointOutNd, hworkNd, hpointOutWorkCross⟩ :=
    List.nodup_append.mp htail

  obtain ⟨hpointNd, houtNd, hpointOutCross⟩ :=
    List.nodup_append.mp hpointOutNd

  have hcontrolPoint :
      control ∉ pointReg := by
    intro h
    apply hcontrolOutside
    exact
      List.mem_append_left work
        (List.mem_append_left outReg h)

  have hpointOutside :
      ∀ w ∈ outReg ++ work, w ∉ pointReg := by
    intro w hw hp
    rcases List.mem_append.mp hw with hout | hwork
    · exact
        (hpointOutCross
          w hp
          w hout) rfl
    · exact
        (hpointOutWorkCross
          w
          (List.mem_append_left outReg hp)
          w
          hwork) rfl

  have hcontrolBase :
      base control = st control := by
    change
      writeReg pointReg (encodeNat result) st control =
        st control
    exact
      writeReg_other_local
        pointReg
        (encodeNat result)
        st
        control
        hcontrolPoint

  have hcleanBase :
      Clean (outReg ++ work) base := by
    intro w hw

    have hwPoint :
        w ∉ pointReg :=
      hpointOutside w hw

    have hwrite :
        writeReg pointReg (encodeNat result) st w =
          st w := by
      exact
        writeReg_other_local
          pointReg
          (encodeNat result)
          st
          w
          hwPoint

    change
      writeReg pointReg (encodeNat result) st w = false

    rw [hwrite]

    exact hclean w (by
      simpa [work] using hw)

  have hencBound :
      encodeNat result < 2 ^ pointReg.length := by
    rw [hpointLength]
    exact encodeNat_lt result

  have hpointBase :
      regValue pointReg base = encodeNat result := by
    change
      regValue pointReg
          (writeReg pointReg (encodeNat result) st) =
        encodeNat result
    exact
      regValue_writeReg_local
        pointReg
        (encodeNat result)
        st
        hpointNd
        hencBound

  have hcancelPoint :
      controlledPointResult
          (base control) result (-C) =
        R := by
    rw [hcontrolBase]
    cases hc : st control <;>
      simp [result, controlledPointResult, hc, add_assoc]

  have hforward :
      Classical.run program base =
        writeReg outReg (encodeNat R) base := by
    have h :=
      controlledPointAddOut_correct
        control
        pointReg
        outReg
        workStart
        (-C)
        result
        base
        hpointLength
        houtLength
        hnodup
        hpointBase
        (by exact hcleanBase)

    rw [hcancelPoint] at h

    change
      Classical.run
          (controlledPointAddOut
            control pointReg outReg workStart (-C))
          base =
        writeReg outReg (encodeNat R) base
      at h

    change
      Classical.run program base =
        writeReg outReg (encodeNat R) base

    exact h

  have hfree :
      Classical.HPFree program := by
    exact controlledPointAddOut_HPFree
      control pointReg outReg workStart (-C)

  have hwf :
      CircuitWellFormed program := by
    exact controlledPointAddOut_wellFormed
      control
      pointReg
      outReg
      workStart
      (-C)
      hpointLength
      houtLength
      hnodup

  rw [← hforward]

  exact Arithmetic.run_reverse_cancel
    program base hfree hwf

theorem controlledPointAdd_correct
    (control : Wire)
    (pointReg : List Wire)
    (workStart : Wire)
    (C R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup : ([control] ++ pointReg ++ controlledPointAddWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean : Clean (controlledPointAddWork workStart) st) :
    Classical.run (controlledPointAdd control pointReg workStart C) st
    =
    writeReg pointReg (encode (controlledPointResult (st control) R C)).val  st := by
  let temp := controlledPointAddTemp workStart
  let auxStart := controlledPointAddAuxStart workStart
  let work := controlledPointAddOutWork auxStart
  let result := controlledPointResult (st control) R C

  have htempLength : temp.length = pointWidth := by
    simp [temp, controlledPointAddTemp]

  have houtNodup :
      ([control] ++ pointReg ++ temp ++ work).Nodup := by
    simpa [temp, auxStart, work, controlledPointAddWork,
      controlledPointAddTemp, controlledPointAddAuxStart,
      List.append_assoc] using hnodup

  have hcleanOut :
      Clean (temp ++ work) st := by
    simpa [temp, auxStart, work, controlledPointAddWork,
      controlledPointAddTemp, controlledPointAddAuxStart] using hclean

  have hswapNodup :
      (pointReg ++ temp ++ work).Nodup := by
    have h :
        (control :: (pointReg ++ temp ++ work)).Nodup := by
      simpa [List.append_assoc] using houtNodup
    exact (List.nodup_cons.mp h).2

  have hswapLength :
      pointReg.length = temp.length := by
    rw [hpointLength, htempLength]

  have hforward :
      Classical.run
          (controlledPointAddOut
            control pointReg temp auxStart C)
          st =
        writeReg temp (encode result).val st := by
    change
      Classical.run
          (controlledPointAddOut
            control pointReg temp auxStart C)
          st =
        writeReg temp
          (encode
            (controlledPointResult (st control) R C)).val
          st
    exact
      controlledPointAddOut_correct
        control pointReg temp auxStart C R st
        hpointLength htempLength houtNodup
        hpoint hcleanOut

  have hswap :
      Classical.run
          (pointSwapReg pointReg temp)
          (writeReg temp (encode result).val st) =
        writeReg temp
          (encodeNat R)
          (writeReg pointReg (encode result).val st) := by
    have h :=
      pointSwapReg_correct
        pointReg
        temp
        work
        st
        (encode result).val
        hswapLength
        hswapNodup
    rw [hpoint] at h
    exact h

  have huncompute :
      Classical.run
          (controlledPointAddOut
            control pointReg temp auxStart (-C)).reverse
          (writeReg temp
            (encodeNat R)
            (writeReg pointReg (encode result).val st)) =
        writeReg pointReg (encode result).val st := by
    change
      Classical.run
          (controlledPointAddOut
            control pointReg temp auxStart (-C)).reverse
          (writeReg temp
            (encodeNat R)
            (writeReg pointReg
              (encode
                (controlledPointResult (st control) R C)).val
              st)) =
        writeReg pointReg
          (encode
            (controlledPointResult (st control) R C)).val
          st
    exact
      controlledPointAddOut_reverse_correct
        control pointReg temp auxStart C R st
        hpointLength htempLength houtNodup
        hpoint hcleanOut

  simp only [controlledPointAdd, Classical.run_append]
  change
    Classical.run
        (controlledPointAddOut
          control pointReg temp auxStart (-C)).reverse
        (Classical.run
          (pointSwapReg pointReg temp)
          (Classical.run
            (controlledPointAddOut
              control pointReg temp auxStart C)
            st)) =
      writeReg pointReg (encode result).val st

  rw [hforward, hswap]
  exact huncompute

end Secp256k1
end ShorECDLP
