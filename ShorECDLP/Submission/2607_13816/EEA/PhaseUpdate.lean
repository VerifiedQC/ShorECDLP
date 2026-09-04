import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
import Lean.Elab.Tactic.Omega

/-!
# Algorithm-3 phase update

This module implements the literal `phase_update_gate` from the pinned supplement.  The three
truth-minus-one length words are tested for encoded zero with clean v-chains, the two phase bits
and sign bit are updated in the source order, and every flag and v-chain scratch wire is restored.
The generic block takes the exact list of wires used by each zero test.  The production wrapper
appends the borrowed shift-epoch discriminator to the low shift word and conjugates that test by
the two source `X` gates, so terminal-padding wrap cannot look like encoded zero.

The coherent circuit and its measurement-uncomputed realization use the same source block order.  In
the adaptive term only the internal cleanup of each multi-controlled equality test is replaced by
the global measurement-uncomputation choice; the phase/sign core stays unitary.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-- Physical roles of the source `phase_update_gate`.  `lengthS` is the complete control list for
the third zero test; the production wrapper below appends the borrowed epoch wire. -/
structure PhaseUpdateRegisters where
  phase1 : Wire
  phase2 : Wire
  sign : Wire
  lengthQ : List Wire
  lengthRPrime : List Wire
  lengthS : List Wire
  zeroQ : Wire
  zeroRPrime : Wire
  zeroS : Wire
  condition : Wire
  temporary : Wire
  equalityScratch : List Wire
deriving Repr

/-- Shared scratch in the exact source order. -/
def PhaseUpdateRegisters.scratch (registers : PhaseUpdateRegisters) : List Wire :=
  [registers.zeroQ, registers.zeroRPrime, registers.zeroS,
    registers.condition, registers.temporary] ++ registers.equalityScratch

/-- Complete physical support of the phase-update block. -/
def PhaseUpdateRegisters.allWires (registers : PhaseUpdateRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.sign] ++
    registers.lengthQ ++ registers.lengthRPrime ++ registers.lengthS ++ registers.scratch

private def PhaseUpdateRegisters.lengthWires
    (registers : PhaseUpdateRegisters) : List Wire :=
  registers.lengthQ ++ registers.lengthRPrime ++ registers.lengthS

private def PhaseUpdateRegisters.scalarWires
    (registers : PhaseUpdateRegisters) : List Wire :=
  [registers.phase1, registers.phase2, registers.sign]

/-- The source uses equal-width quotient and remainder-length words.  The shift word may include
an independently chosen low-word width; each clean v-chain must fit in the shared suffix. -/
structure PhaseUpdateLayout (registers : PhaseUpdateRegisters) : Prop where
  lengthQ_eq_lengthRPrime : registers.lengthQ.length = registers.lengthRPrime.length
  q_capacity : registers.lengthQ.length - 2 ≤ registers.equalityScratch.length
  rPrime_capacity : registers.lengthRPrime.length - 2 ≤ registers.equalityScratch.length
  s_capacity : registers.lengthS.length - 2 ≤ registers.equalityScratch.length
  physical : registers.allWires.Nodup

/-- All five named temporary bits and the shared equality chain start clean. -/
def PhaseUpdateReady (registers : PhaseUpdateRegisters) (state : BasisState) : Prop :=
  Clean registers.scratch state

private theorem phaseUpdate_q_sublist (registers : PhaseUpdateRegisters) :
    (registers.lengthQ ++ registers.zeroQ :: registers.equalityScratch).Sublist
      registers.allWires := by
  have hflags :
      (registers.zeroQ :: registers.equalityScratch).Sublist
        (registers.zeroQ :: registers.zeroRPrime :: registers.zeroS ::
          registers.condition :: registers.temporary :: registers.equalityScratch) := by
    apply List.Sublist.cons₂
    exact (((List.Sublist.refl registers.equalityScratch).cons
      registers.temporary).cons registers.condition).cons registers.zeroS |>.cons
        registers.zeroRPrime
  have htail :
      (registers.zeroQ :: registers.equalityScratch).Sublist
        (registers.lengthRPrime ++ registers.lengthS ++
          registers.zeroQ :: registers.zeroRPrime :: registers.zeroS ::
            registers.condition :: registers.temporary :: registers.equalityScratch) :=
    hflags.trans (List.sublist_append_right
      (registers.lengthRPrime ++ registers.lengthS) _)
  have hbody := (List.Sublist.refl registers.lengthQ).append htail
  exact hbody.trans (by
    simpa [PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scratch,
      List.append_assoc] using
      (List.sublist_append_right
        [registers.phase1, registers.phase2, registers.sign]
        (registers.lengthQ ++ registers.lengthRPrime ++ registers.lengthS ++
          registers.zeroQ :: registers.zeroRPrime :: registers.zeroS ::
            registers.condition :: registers.temporary :: registers.equalityScratch)))

private theorem phaseUpdate_rPrime_sublist (registers : PhaseUpdateRegisters) :
    (registers.lengthRPrime ++ registers.zeroRPrime :: registers.equalityScratch).Sublist
      registers.allWires := by
  have hflags :
      (registers.zeroRPrime :: registers.equalityScratch).Sublist
        (registers.zeroQ :: registers.zeroRPrime :: registers.zeroS ::
          registers.condition :: registers.temporary :: registers.equalityScratch) := by
    apply List.Sublist.cons
    apply List.Sublist.cons₂
    exact (((List.Sublist.refl registers.equalityScratch).cons
      registers.temporary).cons registers.condition).cons registers.zeroS
  have htail :
      (registers.zeroRPrime :: registers.equalityScratch).Sublist
        (registers.lengthS ++ registers.zeroQ :: registers.zeroRPrime ::
          registers.zeroS :: registers.condition :: registers.temporary ::
            registers.equalityScratch) :=
    hflags.trans (List.sublist_append_right registers.lengthS _)
  have hbody := (List.Sublist.refl registers.lengthRPrime).append htail
  have hskipQ := hbody.trans (List.sublist_append_right registers.lengthQ _)
  exact hskipQ.trans (by
    simpa [PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scratch,
      List.append_assoc] using
      (List.sublist_append_right
        [registers.phase1, registers.phase2, registers.sign]
        (registers.lengthQ ++ registers.lengthRPrime ++ registers.lengthS ++
          registers.zeroQ :: registers.zeroRPrime :: registers.zeroS ::
            registers.condition :: registers.temporary :: registers.equalityScratch)))

private theorem phaseUpdate_s_sublist (registers : PhaseUpdateRegisters) :
    (registers.lengthS ++ registers.zeroS :: registers.equalityScratch).Sublist
      registers.allWires := by
  have hflags :
      (registers.zeroS :: registers.equalityScratch).Sublist
        (registers.zeroQ :: registers.zeroRPrime :: registers.zeroS ::
          registers.condition :: registers.temporary :: registers.equalityScratch) := by
    apply List.Sublist.cons
    apply List.Sublist.cons
    apply List.Sublist.cons₂
    exact ((List.Sublist.refl registers.equalityScratch).cons
      registers.temporary).cons registers.condition
  have hbody := (List.Sublist.refl registers.lengthS).append hflags
  have hskipLengths := hbody.trans
    (List.sublist_append_right (registers.lengthQ ++ registers.lengthRPrime) _)
  exact hskipLengths.trans (by
    simpa [PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scratch,
      List.append_assoc] using
      (List.sublist_append_right
        [registers.phase1, registers.phase2, registers.sign]
        (registers.lengthQ ++ registers.lengthRPrime ++ registers.lengthS ++
          registers.zeroQ :: registers.zeroRPrime :: registers.zeroS ::
            registers.condition :: registers.temporary :: registers.equalityScratch)))

private theorem PhaseUpdateLayout.qChain
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers) :
    McxVChainLayout registers.lengthQ registers.zeroQ registers.equalityScratch := by
  exact (phaseUpdate_q_sublist registers).nodup hlayout.physical

private theorem PhaseUpdateLayout.rPrimeChain
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers) :
    McxVChainLayout registers.lengthRPrime registers.zeroRPrime
      registers.equalityScratch := by
  exact (phaseUpdate_rPrime_sublist registers).nodup hlayout.physical

private theorem PhaseUpdateLayout.sChain
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers) :
    McxVChainLayout registers.lengthS registers.zeroS registers.equalityScratch := by
  exact (phaseUpdate_s_sublist registers).nodup hlayout.physical

private theorem PhaseUpdateLayout.coreNodup
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers) :
    [registers.phase1, registers.phase2, registers.sign,
      registers.zeroQ, registers.zeroRPrime, registers.zeroS,
      registers.condition, registers.temporary].Nodup := by
  have hflags :
      [registers.zeroQ, registers.zeroRPrime, registers.zeroS,
        registers.condition, registers.temporary].Sublist
        (registers.lengthQ ++ registers.lengthRPrime ++ registers.lengthS ++
          registers.scratch) := by
    have hscratch :
        [registers.zeroQ, registers.zeroRPrime, registers.zeroS,
          registers.condition, registers.temporary].Sublist registers.scratch := by
      simp [PhaseUpdateRegisters.scratch]
    exact hscratch.trans
      (List.sublist_append_right
        (registers.lengthQ ++ registers.lengthRPrime ++ registers.lengthS) _)
  have hall := (List.Sublist.refl
    [registers.phase1, registers.phase2, registers.sign]).append hflags
  exact (by
    simpa [PhaseUpdateRegisters.allWires, List.append_assoc] using hall.nodup hlayout.physical)

private theorem PhaseUpdateLayout.scalarTailNe
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers)
    {scalar wire : Wire}
    (hscalar : scalar ∈ registers.scalarWires)
    (hwire : wire ∈ registers.lengthWires ++ registers.scratch) :
    scalar ≠ wire := by
  have hsplit :
      (registers.scalarWires ++
        (registers.lengthWires ++ registers.scratch)).Nodup := by
    simpa [PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scalarWires,
      PhaseUpdateRegisters.lengthWires, List.append_assoc] using hlayout.physical
  exact (List.nodup_append.mp hsplit).2.2 scalar hscalar wire hwire

private theorem PhaseUpdateLayout.lengthScratchNe
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers)
    {lengthWire scratchWire : Wire}
    (hlength : lengthWire ∈ registers.lengthWires)
    (hscratch : scratchWire ∈ registers.scratch) :
    lengthWire ≠ scratchWire := by
  have htail :
      (registers.lengthWires ++ registers.scratch).Nodup := by
    have hsub :
        (registers.lengthWires ++ registers.scratch).Sublist registers.allWires := by
      simpa [PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scalarWires,
        PhaseUpdateRegisters.lengthWires, List.append_assoc] using
        (List.sublist_append_right registers.scalarWires
          (registers.lengthWires ++ registers.scratch))
    exact hsub.nodup hlayout.physical
  exact (List.nodup_append.mp htail).2.2
    lengthWire hlength scratchWire hscratch

private theorem PhaseUpdateLayout.scratchNodup
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers) :
    registers.scratch.Nodup := by
  have hsub : registers.scratch.Sublist registers.allWires := by
    simpa [PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scalarWires,
      PhaseUpdateRegisters.lengthWires, List.append_assoc] using
      (List.sublist_append_right
        (registers.scalarWires ++ registers.lengthWires) registers.scratch)
  exact hsub.nodup hlayout.physical

private def phaseUpdateCore (registers : PhaseUpdateRegisters) : Circuit :=
  [.X registers.zeroRPrime,
    .CCX registers.zeroQ registers.zeroRPrime registers.condition,
    .X registers.zeroRPrime,
    .CX registers.sign registers.temporary,
    .CX registers.phase1 registers.temporary,
    .CCX registers.condition registers.temporary registers.phase2,
    .CX registers.phase1 registers.temporary,
    .CX registers.sign registers.temporary,
    .CCX registers.condition registers.phase2 registers.sign,
    .X registers.zeroRPrime,
    .CCX registers.zeroQ registers.zeroRPrime registers.condition,
    .X registers.zeroRPrime,
    .CX registers.zeroS registers.phase1,
    .CX registers.zeroS registers.phase2]

private def phaseUpdateCoreState (registers : PhaseUpdateRegisters)
    (state : BasisState) : BasisState :=
  let condition := state registers.zeroQ && !state registers.zeroRPrime
  let phase2 := Bool.xor (state registers.phase2)
    (condition && Bool.xor (state registers.sign) (state registers.phase1))
  let sign := Bool.xor (state registers.sign) (condition && phase2)
  state
    [registers.phase1 ↦ Bool.xor (state registers.phase1) (state registers.zeroS)]
    [registers.phase2 ↦ Bool.xor phase2 (state registers.zeroS)]
    [registers.sign ↦ sign]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
private theorem run_phaseUpdateCore
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hnd : [registers.phase1, registers.phase2, registers.sign,
      registers.zeroQ, registers.zeroRPrime, registers.zeroS,
      registers.condition, registers.temporary].Nodup)
    (hcondition : state registers.condition = false)
    (htemporary : state registers.temporary = false) :
    run (phaseUpdateCore registers) state = phaseUpdateCoreState registers state := by
  obtain ⟨hp1Not, hnd⟩ := List.nodup_cons.mp hnd
  obtain ⟨hp2Not, hnd⟩ := List.nodup_cons.mp hnd
  obtain ⟨hsignNot, hnd⟩ := List.nodup_cons.mp hnd
  obtain ⟨hzqNot, hnd⟩ := List.nodup_cons.mp hnd
  obtain ⟨hzrNot, hnd⟩ := List.nodup_cons.mp hnd
  obtain ⟨hzsNot, hnd⟩ := List.nodup_cons.mp hnd
  obtain ⟨hconditionNot, _⟩ := List.nodup_cons.mp hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp1Not hp2Not hsignNot hzqNot hzrNot hzsNot hconditionNot
  rcases hp1Not with
    ⟨hp1p2, hp1sign, hp1zq, hp1zr, hp1zs, hp1condition, hp1temporary⟩
  rcases hp2Not with
    ⟨hp2sign, hp2zq, hp2zr, hp2zs, hp2condition, hp2temporary⟩
  rcases hsignNot with
    ⟨hsignzq, hsignzr, hsignzs, hsigncondition, hsigntemporary⟩
  rcases hzqNot with ⟨hzqzr, hzqzs, hzqcondition, hzqtemporary⟩
  rcases hzrNot with ⟨hzrzs, hzrcondition, hzrtemporary⟩
  rcases hzsNot with ⟨hzscondition, hzstemporary⟩
  have hconditiontemporary := hconditionNot
  have hp2p1 := Ne.symm hp1p2
  have hsignp1 := Ne.symm hp1sign
  have hzqp1 := Ne.symm hp1zq
  have hzrp1 := Ne.symm hp1zr
  have hzsp1 := Ne.symm hp1zs
  have hconditionp1 := Ne.symm hp1condition
  have htemporaryp1 := Ne.symm hp1temporary
  have hsignp2 := Ne.symm hp2sign
  have hzqp2 := Ne.symm hp2zq
  have hzrp2 := Ne.symm hp2zr
  have hzsp2 := Ne.symm hp2zs
  have hconditionp2 := Ne.symm hp2condition
  have htemporaryp2 := Ne.symm hp2temporary
  have hzqsign := Ne.symm hsignzq
  have hzrsign := Ne.symm hsignzr
  have hzssign := Ne.symm hsignzs
  have hconditionsign := Ne.symm hsigncondition
  have htemporarysign := Ne.symm hsigntemporary
  have hzrzq := Ne.symm hzqzr
  have hzszq := Ne.symm hzqzs
  have hconditionzq := Ne.symm hzqcondition
  have htemporaryzq := Ne.symm hzqtemporary
  have hzszzr := Ne.symm hzrzs
  have hconditionzr := Ne.symm hzrcondition
  have htemporaryzr := Ne.symm hzrtemporary
  have hconditionzs := Ne.symm hzscondition
  have htemporaryzs := Ne.symm hzstemporary
  have htemporarycondition := Ne.symm hconditiontemporary
  funext wire
  by_cases hp1 : wire = registers.phase1
  · subst wire
    cases hq : state registers.zeroQ <;>
      cases hr : state registers.zeroRPrime <;>
      cases hs : state registers.zeroS <;>
      cases hp : state registers.phase1 <;>
      cases hp2 : state registers.phase2 <;>
      cases hsign : state registers.sign <;>
      simp [phaseUpdateCore, phaseUpdateCoreState, Classical.run,
        Classical.applyGate, upd, hcondition, htemporary, hq, hr, hs, hp, hp2,
        hsign, hp1p2, hp1sign, hp1zq, hp1zr, hp1zs, hp1condition,
        hp1temporary, hp2sign, hp2zq, hp2zr, hp2zs, hp2condition,
        hp2temporary, hsignzq, hsignzr, hsignzs, hsigncondition,
        hsigntemporary, hzqzr, hzqzs, hzqcondition, hzqtemporary, hzrzs,
        hzrcondition, hzrtemporary, hzscondition, hzstemporary,
        hconditiontemporary, hp2p1, hsignp1, hzqp1, hzrp1, hzsp1,
        hconditionp1, htemporaryp1, hsignp2, hzqp2, hzrp2, hzsp2,
        hconditionp2, htemporaryp2, hzqsign, hzrsign, hzssign,
        hconditionsign, htemporarysign, hzrzq, hzszq, hconditionzq,
        htemporaryzq, hzszzr, hconditionzr, htemporaryzr, hconditionzs,
        htemporaryzs, htemporarycondition]
  · by_cases hp2wire : wire = registers.phase2
    · subst wire
      cases hq : state registers.zeroQ <;>
        cases hr : state registers.zeroRPrime <;>
        cases hs : state registers.zeroS <;>
        cases hp : state registers.phase1 <;>
        cases hp2 : state registers.phase2 <;>
        cases hsign : state registers.sign <;>
        simp [phaseUpdateCore, phaseUpdateCoreState, Classical.run,
          Classical.applyGate, upd, hcondition, htemporary, hq, hr, hs, hp, hp2,
          hsign, hp1p2, hp1sign, hp1zq, hp1zr, hp1zs, hp1condition,
          hp1temporary, hp2sign, hp2zq, hp2zr, hp2zs, hp2condition,
          hp2temporary, hsignzq, hsignzr, hsignzs, hsigncondition,
          hsigntemporary, hzqzr, hzqzs, hzqcondition, hzqtemporary, hzrzs,
          hzrcondition, hzrtemporary, hzscondition, hzstemporary,
          hconditiontemporary, hp2p1, hsignp1, hzqp1, hzrp1, hzsp1,
          hconditionp1, htemporaryp1, hsignp2, hzqp2, hzrp2, hzsp2,
          hconditionp2, htemporaryp2, hzqsign, hzrsign, hzssign,
          hconditionsign, htemporarysign, hzrzq, hzszq, hconditionzq,
          htemporaryzq, hzszzr, hconditionzr, htemporaryzr, hconditionzs,
          htemporaryzs, htemporarycondition]
    · by_cases hsignWire : wire = registers.sign
      · subst wire
        cases hq : state registers.zeroQ <;>
          cases hr : state registers.zeroRPrime <;>
          cases hs : state registers.zeroS <;>
          cases hp : state registers.phase1 <;>
          cases hp2 : state registers.phase2 <;>
          cases hsign : state registers.sign <;>
          simp [phaseUpdateCore, phaseUpdateCoreState, Classical.run,
            Classical.applyGate, upd, hcondition, htemporary, hq, hr, hs, hp,
            hp2, hsign, hp1p2, hp1sign, hp1zq, hp1zr, hp1zs, hp1condition,
            hp1temporary, hp2sign, hp2zq, hp2zr, hp2zs, hp2condition,
            hp2temporary, hsignzq, hsignzr, hsignzs, hsigncondition,
            hsigntemporary, hzqzr, hzqzs, hzqcondition, hzqtemporary, hzrzs,
            hzrcondition, hzrtemporary, hzscondition, hzstemporary,
            hconditiontemporary, hp2p1, hsignp1, hzqp1, hzrp1, hzsp1,
            hconditionp1, htemporaryp1, hsignp2, hzqp2, hzrp2, hzsp2,
            hconditionp2, htemporaryp2, hzqsign, hzrsign, hzssign,
            hconditionsign, htemporarysign, hzrzq, hzszq, hconditionzq,
            htemporaryzq, hzszzr, hconditionzr, htemporaryzr, hconditionzs,
            htemporaryzs, htemporarycondition]
      · by_cases hconditionWire : wire = registers.condition
        · subst wire
          cases hq : state registers.zeroQ <;>
            cases hr : state registers.zeroRPrime <;>
            cases hs : state registers.zeroS <;>
            cases hp : state registers.phase1 <;>
            cases hp2 : state registers.phase2 <;>
            cases hsign : state registers.sign <;>
            simp [phaseUpdateCore, phaseUpdateCoreState, Classical.run,
              Classical.applyGate, upd, hcondition, htemporary, hq, hr, hs, hp,
              hp2, hsign, hp1p2, hp1sign, hp1zq, hp1zr, hp1zs, hp1condition,
              hp1temporary, hp2sign, hp2zq, hp2zr, hp2zs, hp2condition,
              hp2temporary, hsignzq, hsignzr, hsignzs, hsigncondition,
              hsigntemporary, hzqzr, hzqzs, hzqcondition, hzqtemporary, hzrzs,
              hzrcondition, hzrtemporary, hzscondition, hzstemporary,
              hconditiontemporary, hp2p1, hsignp1, hzqp1, hzrp1, hzsp1,
              hconditionp1, htemporaryp1, hsignp2, hzqp2, hzrp2, hzsp2,
              hconditionp2, htemporaryp2, hzqsign, hzrsign, hzssign,
              hconditionsign, htemporarysign, hzrzq, hzszq, hconditionzq,
              htemporaryzq, hzszzr, hconditionzr, htemporaryzr, hconditionzs,
              htemporaryzs, htemporarycondition]
        · by_cases htemporaryWire : wire = registers.temporary
          · subst wire
            cases hq : state registers.zeroQ <;>
              cases hr : state registers.zeroRPrime <;>
              cases hs : state registers.zeroS <;>
              cases hp : state registers.phase1 <;>
              cases hp2 : state registers.phase2 <;>
              cases hsign : state registers.sign <;>
              simp [phaseUpdateCore, phaseUpdateCoreState, Classical.run,
                Classical.applyGate, upd, hcondition, htemporary, hq, hr, hs,
                hp, hp2, hsign, hp1p2, hp1sign, hp1zq, hp1zr, hp1zs,
                hp1condition, hp1temporary, hp2sign, hp2zq, hp2zr, hp2zs,
                hp2condition, hp2temporary, hsignzq, hsignzr, hsignzs,
                hsigncondition, hsigntemporary, hzqzr, hzqzs, hzqcondition,
                hzqtemporary, hzrzs, hzrcondition, hzrtemporary, hzscondition,
                hzstemporary, hconditiontemporary, hp2p1, hsignp1, hzqp1,
                hzrp1, hzsp1, hconditionp1, htemporaryp1, hsignp2, hzqp2,
                hzrp2, hzsp2, hconditionp2, htemporaryp2, hzqsign, hzrsign,
                hzssign, hconditionsign, htemporarysign, hzrzq, hzszq,
                hconditionzq, htemporaryzq, hzszzr, hconditionzr,
                htemporaryzr, hconditionzs, htemporaryzs,
                htemporarycondition]
          · by_cases hzrWire : wire = registers.zeroRPrime
            · subst wire
              simp [phaseUpdateCore, phaseUpdateCoreState, Classical.run,
                Classical.applyGate, upd, hcondition, htemporary, hp1p2,
                hp1sign, hp1zq, hp1zr, hp1zs, hp1condition, hp1temporary,
                hp2sign, hp2zq, hp2zr, hp2zs, hp2condition, hp2temporary,
                hsignzq, hsignzr, hsignzs, hsigncondition, hsigntemporary,
                hzqzr, hzqzs, hzqcondition, hzqtemporary, hzrzs,
                hzrcondition, hzrtemporary, hzscondition, hzstemporary,
                hconditiontemporary, hp2p1, hsignp1, hzqp1, hzrp1,
                hzsp1, hconditionp1, htemporaryp1, hsignp2, hzqp2,
                hzrp2, hzsp2, hconditionp2, htemporaryp2, hzqsign,
                hzrsign, hzssign, hconditionsign, htemporarysign, hzrzq,
                hzszq, hconditionzq, htemporaryzq, hzszzr, hconditionzr,
                htemporaryzr, hconditionzs, htemporaryzs,
                htemporarycondition]
            · simp [phaseUpdateCore, phaseUpdateCoreState, Classical.run,
                Classical.applyGate, upd, hcondition, htemporary, hp1,
                hp2wire, hsignWire, hconditionWire, htemporaryWire, hzrWire]

private def phaseUpdateForwardTests (registers : PhaseUpdateRegisters) : Circuit :=
  mcxVChain registers.lengthQ registers.zeroQ registers.equalityScratch ++
    mcxVChain registers.lengthRPrime registers.zeroRPrime registers.equalityScratch ++
    mcxVChain registers.lengthS registers.zeroS registers.equalityScratch

private def phaseUpdateCleanupTests (registers : PhaseUpdateRegisters) : Circuit :=
  mcxVChain registers.lengthS registers.zeroS registers.equalityScratch ++
    mcxVChain registers.lengthRPrime registers.zeroRPrime registers.equalityScratch ++
    mcxVChain registers.lengthQ registers.zeroQ registers.equalityScratch

/-- Literal coherent source circuit. -/
private def phaseUpdateUnitary (registers : PhaseUpdateRegisters) : Circuit :=
  phaseUpdateForwardTests registers ++ phaseUpdateCore registers ++
    phaseUpdateCleanupTests registers

/-- Gate-independent Boolean update performed on the three public state bits. -/
private def phaseUpdateState (registers : PhaseUpdateRegisters)
    (state : BasisState) : BasisState :=
  let zeroQ := wireAnd registers.lengthQ state
  let zeroRPrime := wireAnd registers.lengthRPrime state
  let zeroS := wireAnd registers.lengthS state
  let condition := zeroQ && !zeroRPrime
  let phase2 := Bool.xor (state registers.phase2)
    (condition && Bool.xor (state registers.sign) (state registers.phase1))
  let sign := Bool.xor (state registers.sign) (condition && phase2)
  state
    [registers.phase1 ↦ Bool.xor (state registers.phase1) zeroS]
    [registers.phase2 ↦ Bool.xor phase2 zeroS]
    [registers.sign ↦ sign]

private theorem clean_upd_not_mem
    (wires : List Wire) (state : BasisState) (target : Wire) (value : Bool)
    (hnot : target ∉ wires) (hclean : Clean wires state) :
    Clean wires state[target ↦ value] := by
  intro wire hwire
  rw [upd_other state target value (by
    intro equality
    subst wire
    exact hnot hwire)]
  exact hclean wire hwire

private theorem PhaseUpdateLayout.scratchWire_not_lengthWires
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers)
    {wire : Wire} (hwire : wire ∈ registers.scratch) :
    wire ∉ registers.lengthWires := by
  intro hlength
  exact (hlayout.lengthScratchNe hlength hwire) rfl

private theorem PhaseUpdateLayout.scalarWire_not_tail
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers)
    {wire : Wire} (hwire : wire ∈ registers.scalarWires) :
    wire ∉ registers.lengthWires ++ registers.scratch := by
  intro htail
  exact (hlayout.scalarTailNe hwire htail) rfl

private def phaseUpdateForwardFlags (registers : PhaseUpdateRegisters)
    (state : BasisState) : BasisState :=
  state
    [registers.zeroQ ↦ wireAnd registers.lengthQ state]
    [registers.zeroRPrime ↦ wireAnd registers.lengthRPrime state]
    [registers.zeroS ↦ wireAnd registers.lengthS state]

private def phaseUpdateFlaggedState (registers : PhaseUpdateRegisters)
    (state : BasisState) : BasisState :=
  (phaseUpdateState registers state)
    [registers.zeroQ ↦ wireAnd registers.lengthQ state]
    [registers.zeroRPrime ↦ wireAnd registers.lengthRPrime state]
    [registers.zeroS ↦ wireAnd registers.lengthS state]

private theorem run_phaseUpdateForwardTests
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hlayout : PhaseUpdateLayout registers)
    (hready : PhaseUpdateReady registers state) :
    Classical.run (phaseUpdateForwardTests registers) state =
      phaseUpdateForwardFlags registers state := by
  have hequalityClean : Clean registers.equalityScratch state := by
    intro wire hwire
    exact hready wire (by
      simp [PhaseUpdateRegisters.scratch, hwire])
  have hzeroQ : state registers.zeroQ = false :=
    hready registers.zeroQ (by simp [PhaseUpdateRegisters.scratch])
  have hzeroRPrime : state registers.zeroRPrime = false :=
    hready registers.zeroRPrime (by simp [PhaseUpdateRegisters.scratch])
  have hzeroS : state registers.zeroS = false :=
    hready registers.zeroS (by simp [PhaseUpdateRegisters.scratch])
  have hscratchNodup := hlayout.scratchNodup
  have hscratchParts :
      ([registers.zeroQ, registers.zeroRPrime, registers.zeroS,
          registers.condition, registers.temporary] ++
        registers.equalityScratch).Nodup := by
    simpa [PhaseUpdateRegisters.scratch] using hscratchNodup
  have hscratchCross := (List.nodup_append.mp hscratchParts).2.2
  have hzeroQNotEquality : registers.zeroQ ∉ registers.equalityScratch := by
    intro hmem
    exact hscratchCross registers.zeroQ (by simp) registers.zeroQ hmem rfl
  have hafterQClean : Clean registers.equalityScratch
      state[registers.zeroQ ↦ wireAnd registers.lengthQ state] :=
    clean_upd_not_mem _ _ _ _ hzeroQNotEquality hequalityClean
  have hzeroRPrimeNotEquality :
      registers.zeroRPrime ∉ registers.equalityScratch := by
    intro hmem
    exact hscratchCross registers.zeroRPrime (by simp) registers.zeroRPrime hmem rfl
  have hafterQRClean : Clean registers.equalityScratch
      state[registers.zeroQ ↦ wireAnd registers.lengthQ state]
        [registers.zeroRPrime ↦ wireAnd registers.lengthRPrime state] :=
    clean_upd_not_mem _ _ _ _ hzeroRPrimeNotEquality hafterQClean
  have hzeroSNotEquality : registers.zeroS ∉ registers.equalityScratch := by
    intro hmem
    exact hscratchCross registers.zeroS (by simp) registers.zeroS hmem rfl
  have hzeroQNotLengths := hlayout.scratchWire_not_lengthWires
    (wire := registers.zeroQ) (by simp [PhaseUpdateRegisters.scratch])
  have hzeroRPrimeNotLengths := hlayout.scratchWire_not_lengthWires
    (wire := registers.zeroRPrime) (by simp [PhaseUpdateRegisters.scratch])
  have hzeroSNotLengths := hlayout.scratchWire_not_lengthWires
    (wire := registers.zeroS) (by simp [PhaseUpdateRegisters.scratch])
  have hflagsNodup := hlayout.coreNodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hflagsNodup
  have hzeroRPrimeZeroQ : registers.zeroRPrime ≠ registers.zeroQ :=
    Ne.symm hflagsNodup.2.2.2.1.1
  have hzeroSZeroQ : registers.zeroS ≠ registers.zeroQ :=
    Ne.symm hflagsNodup.2.2.2.1.2.1
  have hzeroSZeroRPrime : registers.zeroS ≠ registers.zeroRPrime :=
    Ne.symm hflagsNodup.2.2.2.2.1.1
  have hzeroQNotLengthRPrime : registers.zeroQ ∉ registers.lengthRPrime := by
    intro hmem
    apply hzeroQNotLengths
    simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
    exact Or.inl (Or.inr hmem)
  have hzeroQNotLengthS : registers.zeroQ ∉ registers.lengthS := by
    intro hmem
    apply hzeroQNotLengths
    simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
    exact Or.inr hmem
  have hzeroRPrimeNotLengthS : registers.zeroRPrime ∉ registers.lengthS := by
    intro hmem
    apply hzeroRPrimeNotLengths
    simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
    exact Or.inr hmem
  have hzeroRPrimeAfterQ :
      state[registers.zeroQ ↦ wireAnd registers.lengthQ state]
          registers.zeroRPrime = false := by
    rw [upd_other state registers.zeroQ _ hzeroRPrimeZeroQ, hzeroRPrime]
  have hzeroSAfterQR :
      state[registers.zeroQ ↦ wireAnd registers.lengthQ state]
          [registers.zeroRPrime ↦ wireAnd registers.lengthRPrime state]
          registers.zeroS = false := by
    rw [upd_other _ registers.zeroRPrime _ hzeroSZeroRPrime,
      upd_other state registers.zeroQ _ hzeroSZeroQ, hzeroS]
  have hwireAndRPrimeAfterQ :
      wireAnd registers.lengthRPrime
          state[registers.zeroQ ↦ wireAnd registers.lengthQ state] =
        wireAnd registers.lengthRPrime state :=
    wireAnd_upd_not_mem _ _ _ _ hzeroQNotLengthRPrime
  have hwireAndSAfterQR :
      wireAnd registers.lengthS
          state[registers.zeroQ ↦ wireAnd registers.lengthQ state]
            [registers.zeroRPrime ↦ wireAnd registers.lengthRPrime state] =
        wireAnd registers.lengthS state := by
    rw [wireAnd_upd_not_mem _ _ _ _ hzeroRPrimeNotLengthS,
      wireAnd_upd_not_mem _ _ _ _ hzeroQNotLengthS]
  rw [phaseUpdateForwardTests, Classical.run_append, Classical.run_append,
    run_mcxVChain registers.lengthQ registers.zeroQ registers.equalityScratch
      state hlayout.q_capacity hlayout.qChain hequalityClean]
  simp only [hzeroQ, Bool.false_xor]
  rw [run_mcxVChain registers.lengthRPrime registers.zeroRPrime
      registers.equalityScratch _ hlayout.rPrime_capacity hlayout.rPrimeChain
      hafterQClean]
  rw [hzeroRPrimeAfterQ, hwireAndRPrimeAfterQ, Bool.false_xor]
  rw [run_mcxVChain registers.lengthS registers.zeroS registers.equalityScratch _
      hlayout.s_capacity hlayout.sChain hafterQRClean]
  rw [hzeroSAfterQR, hwireAndSAfterQR, Bool.false_xor]
  rfl

set_option linter.unusedSimpArgs false in
private theorem run_phaseUpdateCore_afterForward
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hlayout : PhaseUpdateLayout registers)
    (hready : PhaseUpdateReady registers state) :
    Classical.run (phaseUpdateCore registers)
        (phaseUpdateForwardFlags registers state) =
      phaseUpdateFlaggedState registers state := by
  have hnd := hlayout.coreNodup
  have hcondition :
      phaseUpdateForwardFlags registers state registers.condition = false := by
    have hclean := hready registers.condition (by
      simp [PhaseUpdateRegisters.scratch])
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hnd
    simp [phaseUpdateForwardFlags, upd, hclean,
      Ne.symm hnd.2.2.2.1.2.2.1, Ne.symm hnd.2.2.2.2.1.2.1,
      Ne.symm hnd.2.2.2.2.2.1.1]
  have htemporary :
      phaseUpdateForwardFlags registers state registers.temporary = false := by
    have hclean := hready registers.temporary (by
      simp [PhaseUpdateRegisters.scratch])
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hnd
    simp [phaseUpdateForwardFlags, upd, hclean,
      Ne.symm hnd.2.2.2.1.2.2.2, Ne.symm hnd.2.2.2.2.1.2.2,
      Ne.symm hnd.2.2.2.2.2.1.2]
  rw [run_phaseUpdateCore registers (phaseUpdateForwardFlags registers state)
    hlayout.coreNodup hcondition htemporary]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  funext wire
  by_cases hp1 : wire = registers.phase1
  · subst wire
    simp_all [phaseUpdateCoreState, phaseUpdateForwardFlags,
      phaseUpdateFlaggedState, phaseUpdateState, upd]
  · by_cases hp2 : wire = registers.phase2
    · subst wire
      simp_all [phaseUpdateCoreState, phaseUpdateForwardFlags,
        phaseUpdateFlaggedState, phaseUpdateState, upd]
    · by_cases hsign : wire = registers.sign
      · subst wire
        simp_all [phaseUpdateCoreState, phaseUpdateForwardFlags,
          phaseUpdateFlaggedState, phaseUpdateState, upd]
      · by_cases hzeroQ : wire = registers.zeroQ
        · subst wire
          simp_all [phaseUpdateCoreState, phaseUpdateForwardFlags,
            phaseUpdateFlaggedState, phaseUpdateState, upd]
        · by_cases hzeroRPrime : wire = registers.zeroRPrime
          · subst wire
            simp_all [phaseUpdateCoreState, phaseUpdateForwardFlags,
              phaseUpdateFlaggedState, phaseUpdateState, upd]
          · by_cases hzeroS : wire = registers.zeroS
            · subst wire
              simp_all [phaseUpdateCoreState, phaseUpdateForwardFlags,
                phaseUpdateFlaggedState, phaseUpdateState, upd]
            · simp_all [phaseUpdateCoreState, phaseUpdateForwardFlags,
                phaseUpdateFlaggedState, phaseUpdateState, upd]

private theorem PhaseUpdateLayout.scalarWire_not_lengthWires
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers)
    {wire : Wire} (hwire : wire ∈ registers.scalarWires) :
    wire ∉ registers.lengthWires := by
  intro hlength
  exact hlayout.scalarWire_not_tail hwire (by
    exact List.mem_append_left _ hlength)

private theorem PhaseUpdateLayout.namedScratch_not_equality
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers)
    {wire : Wire}
    (hwire : wire ∈ [registers.zeroQ, registers.zeroRPrime, registers.zeroS,
      registers.condition, registers.temporary]) :
    wire ∉ registers.equalityScratch := by
  have hparts :
      ([registers.zeroQ, registers.zeroRPrime, registers.zeroS,
          registers.condition, registers.temporary] ++
        registers.equalityScratch).Nodup := by
    simpa [PhaseUpdateRegisters.scratch] using hlayout.scratchNodup
  intro hmem
  exact (List.nodup_append.mp hparts).2.2 wire hwire wire hmem rfl

private theorem PhaseUpdateLayout.scalarWire_not_equality
    {registers : PhaseUpdateRegisters} (hlayout : PhaseUpdateLayout registers)
    {wire : Wire} (hwire : wire ∈ registers.scalarWires) :
    wire ∉ registers.equalityScratch := by
  intro hequality
  exact hlayout.scalarWire_not_tail hwire (by
    apply List.mem_append_right registers.lengthWires
    simp [PhaseUpdateRegisters.scratch, hequality])

private theorem phaseUpdateFlaggedState_equalityClean
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hlayout : PhaseUpdateLayout registers)
    (hclean : Clean registers.equalityScratch state) :
    Clean registers.equalityScratch (phaseUpdateFlaggedState registers state) := by
  have hp1 := hlayout.scalarWire_not_equality
    (wire := registers.phase1) (by simp [PhaseUpdateRegisters.scalarWires])
  have hp2 := hlayout.scalarWire_not_equality
    (wire := registers.phase2) (by simp [PhaseUpdateRegisters.scalarWires])
  have hsign := hlayout.scalarWire_not_equality
    (wire := registers.sign) (by simp [PhaseUpdateRegisters.scalarWires])
  have hzeroQ := hlayout.namedScratch_not_equality
    (wire := registers.zeroQ) (by simp)
  have hzeroRPrime := hlayout.namedScratch_not_equality
    (wire := registers.zeroRPrime) (by simp)
  have hzeroS := hlayout.namedScratch_not_equality
    (wire := registers.zeroS) (by simp)
  unfold phaseUpdateFlaggedState phaseUpdateState
  exact clean_upd_not_mem _ _ _ _ hzeroS
    (clean_upd_not_mem _ _ _ _ hzeroRPrime
      (clean_upd_not_mem _ _ _ _ hzeroQ
        (clean_upd_not_mem _ _ _ _ hsign
          (clean_upd_not_mem _ _ _ _ hp2
            (clean_upd_not_mem _ _ _ _ hp1 hclean)))))

private theorem phaseUpdateFlaggedState_wireAnd
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (wires : List Wire) (hlayout : PhaseUpdateLayout registers)
    (hsub : ∀ wire ∈ wires, wire ∈ registers.lengthWires) :
    wireAnd wires (phaseUpdateFlaggedState registers state) =
      wireAnd wires state := by
  have hp1 : registers.phase1 ∉ wires := by
    intro hmem
    exact hlayout.scalarWire_not_lengthWires
      (wire := registers.phase1) (by simp [PhaseUpdateRegisters.scalarWires])
        (hsub registers.phase1 hmem)
  have hp2 : registers.phase2 ∉ wires := by
    intro hmem
    exact hlayout.scalarWire_not_lengthWires
      (wire := registers.phase2) (by simp [PhaseUpdateRegisters.scalarWires])
        (hsub registers.phase2 hmem)
  have hsign : registers.sign ∉ wires := by
    intro hmem
    exact hlayout.scalarWire_not_lengthWires
      (wire := registers.sign) (by simp [PhaseUpdateRegisters.scalarWires])
        (hsub registers.sign hmem)
  have hzeroQ : registers.zeroQ ∉ wires := by
    intro hmem
    exact hlayout.scratchWire_not_lengthWires
      (wire := registers.zeroQ) (by simp [PhaseUpdateRegisters.scratch])
        (hsub registers.zeroQ hmem)
  have hzeroRPrime : registers.zeroRPrime ∉ wires := by
    intro hmem
    exact hlayout.scratchWire_not_lengthWires
      (wire := registers.zeroRPrime) (by simp [PhaseUpdateRegisters.scratch])
        (hsub registers.zeroRPrime hmem)
  have hzeroS : registers.zeroS ∉ wires := by
    intro hmem
    exact hlayout.scratchWire_not_lengthWires
      (wire := registers.zeroS) (by simp [PhaseUpdateRegisters.scratch])
        (hsub registers.zeroS hmem)
  unfold phaseUpdateFlaggedState phaseUpdateState
  rw [wireAnd_upd_not_mem _ _ _ _ hzeroS,
    wireAnd_upd_not_mem _ _ _ _ hzeroRPrime,
    wireAnd_upd_not_mem _ _ _ _ hzeroQ,
    wireAnd_upd_not_mem _ _ _ _ hsign,
    wireAnd_upd_not_mem _ _ _ _ hp2,
    wireAnd_upd_not_mem _ _ _ _ hp1]

set_option linter.unusedSimpArgs false in
private theorem run_phaseUpdateCleanupTests
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hlayout : PhaseUpdateLayout registers)
    (hready : PhaseUpdateReady registers state) :
    Classical.run (phaseUpdateCleanupTests registers)
        (phaseUpdateFlaggedState registers state) =
      phaseUpdateState registers state := by
  have hequalityClean : Clean registers.equalityScratch state := by
    intro wire hwire
    exact hready wire (by simp [PhaseUpdateRegisters.scratch, hwire])
  have hflaggedClean := phaseUpdateFlaggedState_equalityClean
    registers state hlayout hequalityClean
  have hzeroSNotEquality := hlayout.namedScratch_not_equality
    (wire := registers.zeroS) (by simp)
  have hzeroRPrimeNotEquality := hlayout.namedScratch_not_equality
    (wire := registers.zeroRPrime) (by simp)
  have hafterSClean : Clean registers.equalityScratch
      (phaseUpdateFlaggedState registers state)[registers.zeroS ↦ false] :=
    clean_upd_not_mem _ _ _ _ hzeroSNotEquality hflaggedClean
  have hafterSRClean : Clean registers.equalityScratch
      (phaseUpdateFlaggedState registers state)[registers.zeroS ↦ false]
        [registers.zeroRPrime ↦ false] :=
    clean_upd_not_mem _ _ _ _ hzeroRPrimeNotEquality hafterSClean
  have hwireAndS := phaseUpdateFlaggedState_wireAnd registers state
    registers.lengthS hlayout (by
      intro wire hwire
      simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
      exact Or.inr hwire)
  have hwireAndRPrime := phaseUpdateFlaggedState_wireAnd registers state
    registers.lengthRPrime hlayout (by
      intro wire hwire
      simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
      exact Or.inl (Or.inr hwire))
  have hwireAndQ := phaseUpdateFlaggedState_wireAnd registers state
    registers.lengthQ hlayout (by
      intro wire hwire
      simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
      exact Or.inl (Or.inl hwire))
  have hnd := hlayout.coreNodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  have hzeroQZeroRPrime := hnd.2.2.2.1.1
  have hzeroQZeroS := hnd.2.2.2.1.2.1
  have hzeroRPrimeZeroS := hnd.2.2.2.2.1.1
  have hzeroSValue : phaseUpdateFlaggedState registers state registers.zeroS =
      wireAnd registers.lengthS state := by
    simp [phaseUpdateFlaggedState, upd]
  have hzeroRPrimeValue :
      (phaseUpdateFlaggedState registers state)[registers.zeroS ↦ false]
          registers.zeroRPrime = wireAnd registers.lengthRPrime state := by
    rw [upd_other _ registers.zeroS _ hzeroRPrimeZeroS]
    simp [phaseUpdateFlaggedState, upd, hzeroRPrimeZeroS]
  have hzeroQValue :
      (phaseUpdateFlaggedState registers state)[registers.zeroS ↦ false]
          [registers.zeroRPrime ↦ false] registers.zeroQ =
        wireAnd registers.lengthQ state := by
    rw [upd_other _ registers.zeroRPrime _ hzeroQZeroRPrime,
      upd_other _ registers.zeroS _ hzeroQZeroS]
    simp [phaseUpdateFlaggedState, upd, hzeroQZeroRPrime, hzeroQZeroS]
  have hwireAndRAfterS :
      wireAnd registers.lengthRPrime
          (phaseUpdateFlaggedState registers state)[registers.zeroS ↦ false] =
        wireAnd registers.lengthRPrime state := by
    rw [wireAnd_upd_not_mem]
    · exact hwireAndRPrime
    · intro hmem
      exact hlayout.scratchWire_not_lengthWires
        (wire := registers.zeroS) (by simp [PhaseUpdateRegisters.scratch])
          (by
            simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
            exact Or.inl (Or.inr hmem))
  have hwireAndQAfterSR :
      wireAnd registers.lengthQ
          (phaseUpdateFlaggedState registers state)[registers.zeroS ↦ false]
            [registers.zeroRPrime ↦ false] =
        wireAnd registers.lengthQ state := by
    rw [wireAnd_upd_not_mem, wireAnd_upd_not_mem]
    · exact hwireAndQ
    · intro hmem
      exact hlayout.scratchWire_not_lengthWires
        (wire := registers.zeroS) (by simp [PhaseUpdateRegisters.scratch])
          (by
            simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
            exact Or.inl (Or.inl hmem))
    · intro hmem
      exact hlayout.scratchWire_not_lengthWires
        (wire := registers.zeroRPrime) (by simp [PhaseUpdateRegisters.scratch])
          (by
            simp only [PhaseUpdateRegisters.lengthWires, List.mem_append]
            exact Or.inl (Or.inl hmem))
  rw [phaseUpdateCleanupTests, Classical.run_append, Classical.run_append,
    run_mcxVChain registers.lengthS registers.zeroS registers.equalityScratch _
      hlayout.s_capacity hlayout.sChain hflaggedClean,
    hzeroSValue, hwireAndS, Bool.xor_self]
  rw [run_mcxVChain registers.lengthRPrime registers.zeroRPrime
      registers.equalityScratch _ hlayout.rPrime_capacity hlayout.rPrimeChain
      hafterSClean, hzeroRPrimeValue, hwireAndRAfterS, Bool.xor_self]
  rw [run_mcxVChain registers.lengthQ registers.zeroQ registers.equalityScratch _
      hlayout.q_capacity hlayout.qChain hafterSRClean,
    hzeroQValue, hwireAndQAfterSR, Bool.xor_self]
  funext wire
  have hzeroQClean := hready registers.zeroQ (by
    simp [PhaseUpdateRegisters.scratch])
  have hzeroRPrimeClean := hready registers.zeroRPrime (by
    simp [PhaseUpdateRegisters.scratch])
  have hzeroSClean := hready registers.zeroS (by
    simp [PhaseUpdateRegisters.scratch])
  have hp1ZeroQ := hlayout.scalarTailNe
    (scalar := registers.phase1) (wire := registers.zeroQ)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hp2ZeroQ := hlayout.scalarTailNe
    (scalar := registers.phase2) (wire := registers.zeroQ)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hsignZeroQ := hlayout.scalarTailNe
    (scalar := registers.sign) (wire := registers.zeroQ)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hp1ZeroRPrime := hlayout.scalarTailNe
    (scalar := registers.phase1) (wire := registers.zeroRPrime)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hp2ZeroRPrime := hlayout.scalarTailNe
    (scalar := registers.phase2) (wire := registers.zeroRPrime)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hsignZeroRPrime := hlayout.scalarTailNe
    (scalar := registers.sign) (wire := registers.zeroRPrime)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hp1ZeroS := hlayout.scalarTailNe
    (scalar := registers.phase1) (wire := registers.zeroS)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hp2ZeroS := hlayout.scalarTailNe
    (scalar := registers.phase2) (wire := registers.zeroS)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hsignZeroS := hlayout.scalarTailNe
    (scalar := registers.sign) (wire := registers.zeroS)
    (by simp [PhaseUpdateRegisters.scalarWires]) (by
      apply List.mem_append_right registers.lengthWires
      simp [PhaseUpdateRegisters.scratch])
  have hphaseQ : phaseUpdateState registers state registers.zeroQ =
      state registers.zeroQ := by
    unfold phaseUpdateState
    rw [upd_other _ registers.sign _ (Ne.symm hsignZeroQ),
      upd_other _ registers.phase2 _ (Ne.symm hp2ZeroQ),
      upd_other _ registers.phase1 _ (Ne.symm hp1ZeroQ)]
  have hphaseRPrime : phaseUpdateState registers state registers.zeroRPrime =
      state registers.zeroRPrime := by
    unfold phaseUpdateState
    rw [upd_other _ registers.sign _ (Ne.symm hsignZeroRPrime),
      upd_other _ registers.phase2 _ (Ne.symm hp2ZeroRPrime),
      upd_other _ registers.phase1 _ (Ne.symm hp1ZeroRPrime)]
  have hphaseS : phaseUpdateState registers state registers.zeroS =
      state registers.zeroS := by
    unfold phaseUpdateState
    rw [upd_other _ registers.sign _ (Ne.symm hsignZeroS),
      upd_other _ registers.phase2 _ (Ne.symm hp2ZeroS),
      upd_other _ registers.phase1 _ (Ne.symm hp1ZeroS)]
  by_cases hwireQ : wire = registers.zeroQ
  · subst wire
    simp [upd, hphaseQ, hzeroQClean]
  · by_cases hwireR : wire = registers.zeroRPrime
    · subst wire
      simp [upd, hphaseRPrime, hzeroRPrimeClean,
        Ne.symm hzeroQZeroRPrime]
    · by_cases hwireS : wire = registers.zeroS
      · subst wire
        simp [upd, hphaseS, hzeroSClean, Ne.symm hzeroQZeroS,
          Ne.symm hzeroRPrimeZeroS]
      · simp [phaseUpdateFlaggedState, upd, hwireQ, hwireR, hwireS]

/-- On the source clean boundary, the coherent phase-update block performs the advertised
Boolean transition and restores every named flag and equality-chain scratch wire. -/
private theorem run_phaseUpdateUnitary
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hlayout : PhaseUpdateLayout registers)
    (hready : PhaseUpdateReady registers state) :
    Classical.run (phaseUpdateUnitary registers) state =
      phaseUpdateState registers state := by
  rw [phaseUpdateUnitary, Classical.run_append, Classical.run_append,
    run_phaseUpdateForwardTests registers state hlayout hready,
    run_phaseUpdateCore_afterForward registers state hlayout hready,
    run_phaseUpdateCleanupTests registers state hlayout hready]

private theorem phaseUpdateState_preserves_scratch
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hlayout : PhaseUpdateLayout registers) {wire : Wire}
    (hwire : wire ∈ registers.scratch) :
    phaseUpdateState registers state wire = state wire := by
  have hp1Wire := hlayout.scalarTailNe
    (scalar := registers.phase1) (wire := wire)
    (by simp [PhaseUpdateRegisters.scalarWires])
    (List.mem_append_right registers.lengthWires hwire)
  have hp2Wire := hlayout.scalarTailNe
    (scalar := registers.phase2) (wire := wire)
    (by simp [PhaseUpdateRegisters.scalarWires])
    (List.mem_append_right registers.lengthWires hwire)
  have hsignWire := hlayout.scalarTailNe
    (scalar := registers.sign) (wire := wire)
    (by simp [PhaseUpdateRegisters.scalarWires])
    (List.mem_append_right registers.lengthWires hwire)
  unfold phaseUpdateState
  rw [upd_other _ registers.sign _ (Ne.symm hsignWire),
    upd_other _ registers.phase2 _ (Ne.symm hp2Wire),
    upd_other _ registers.phase1 _ (Ne.symm hp1Wire)]

private theorem phaseUpdateCore_usesOnly (registers : PhaseUpdateRegisters) :
    PaperCircuitUsesOnly
      [registers.phase1, registers.phase2, registers.sign,
        registers.zeroQ, registers.zeroRPrime, registers.zeroS,
        registers.condition, registers.temporary]
      (phaseUpdateCore registers) := by
  simp [phaseUpdateCore, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

private theorem phaseUpdateForwardTests_usesOnly
    (registers : PhaseUpdateRegisters) :
    PaperCircuitUsesOnly registers.allWires (phaseUpdateForwardTests registers) := by
  rw [phaseUpdateForwardTests]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · exact (mcxVChain_usesOnly registers.lengthQ registers.zeroQ
        registers.equalityScratch).mono fun wire hwire ↦
          (phaseUpdate_q_sublist registers).mem hwire
    · exact (mcxVChain_usesOnly registers.lengthRPrime registers.zeroRPrime
        registers.equalityScratch).mono fun wire hwire ↦
          (phaseUpdate_rPrime_sublist registers).mem hwire
  · exact (mcxVChain_usesOnly registers.lengthS registers.zeroS
      registers.equalityScratch).mono fun wire hwire ↦
        (phaseUpdate_s_sublist registers).mem hwire

private theorem phaseUpdateCleanupTests_usesOnly
    (registers : PhaseUpdateRegisters) :
    PaperCircuitUsesOnly registers.allWires (phaseUpdateCleanupTests registers) := by
  rw [phaseUpdateCleanupTests]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · exact (mcxVChain_usesOnly registers.lengthS registers.zeroS
        registers.equalityScratch).mono fun wire hwire ↦
          (phaseUpdate_s_sublist registers).mem hwire
    · exact (mcxVChain_usesOnly registers.lengthRPrime registers.zeroRPrime
        registers.equalityScratch).mono fun wire hwire ↦
          (phaseUpdate_rPrime_sublist registers).mem hwire
  · exact (mcxVChain_usesOnly registers.lengthQ registers.zeroQ
      registers.equalityScratch).mono fun wire hwire ↦
        (phaseUpdate_q_sublist registers).mem hwire

/-- Every gate in the source block lies in its declared physical register support. -/
private theorem phaseUpdateUnitary_usesOnly (registers : PhaseUpdateRegisters) :
    PaperCircuitUsesOnly registers.allWires (phaseUpdateUnitary registers) := by
  rw [phaseUpdateUnitary]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · exact phaseUpdateForwardTests_usesOnly registers
    · exact (phaseUpdateCore_usesOnly registers).mono (by
        intro wire hwire
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
        rcases hwire with hwire | hwire | hwire | hwire | hwire | hwire |
          hwire | hwire
        all_goals subst wire
        all_goals
          simp [PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scratch])
  · exact phaseUpdateCleanupTests_usesOnly registers

private theorem phaseUpdateCore_wellFormed
    (registers : PhaseUpdateRegisters) (hlayout : PhaseUpdateLayout registers) :
    CircuitWellFormed (phaseUpdateCore registers) := by
  have hnd := hlayout.coreNodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  simp_all [phaseUpdateCore, CircuitWellFormed, Gate.WellFormed, Ne.symm]

/-! ## Shared measurement-uncomputation helpers -/

private theorem phaseUpdate_mcx_preservesEqualityClean
    (registers : PhaseUpdateRegisters) (controls : List Wire) (target : Wire)
    (state : BasisState) (henough : controls.length - 2 ≤ registers.equalityScratch.length)
    (hchain : McxVChainLayout controls target registers.equalityScratch)
    (htarget : target ∉ registers.equalityScratch)
    (hclean : Clean registers.equalityScratch state) :
    Clean registers.equalityScratch
      (Classical.run (mcxVChain controls target registers.equalityScratch) state) := by
  rw [run_mcxVChain controls target registers.equalityScratch state
    henough hchain hclean]
  exact clean_upd_not_mem _ _ _ _ htarget hclean

private theorem phaseUpdateForwardTests_preservesEqualityClean
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hlayout : PhaseUpdateLayout registers)
    (hclean : Clean registers.equalityScratch state) :
    Clean registers.equalityScratch
      (Classical.run (phaseUpdateForwardTests registers) state) := by
  have hqNot := hlayout.namedScratch_not_equality
    (wire := registers.zeroQ) (by simp)
  have hrNot := hlayout.namedScratch_not_equality
    (wire := registers.zeroRPrime) (by simp)
  have hsNot := hlayout.namedScratch_not_equality
    (wire := registers.zeroS) (by simp)
  rw [phaseUpdateForwardTests, Classical.run_append, Classical.run_append]
  exact phaseUpdate_mcx_preservesEqualityClean registers registers.lengthS
    registers.zeroS _ hlayout.s_capacity hlayout.sChain hsNot
      (phaseUpdate_mcx_preservesEqualityClean registers registers.lengthRPrime
        registers.zeroRPrime _ hlayout.rPrime_capacity hlayout.rPrimeChain hrNot
          (phaseUpdate_mcx_preservesEqualityClean registers registers.lengthQ
            registers.zeroQ state hlayout.q_capacity hlayout.qChain hqNot hclean))

private theorem phaseUpdateCore_preservesEqualityClean
    (registers : PhaseUpdateRegisters) (state : BasisState)
    (hlayout : PhaseUpdateLayout registers)
    (hclean : Clean registers.equalityScratch state) :
    Clean registers.equalityScratch
      (Classical.run (phaseUpdateCore registers) state) := by
  intro wire hwire
  have houtside : wire ∉
      [registers.phase1, registers.phase2, registers.sign,
        registers.zeroQ, registers.zeroRPrime, registers.zeroS,
        registers.condition, registers.temporary] := by
    intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem | hmem | hmem | hmem | hmem
    · subst wire
      exact hlayout.scalarWire_not_equality
        (wire := registers.phase1) (by simp [PhaseUpdateRegisters.scalarWires])
          hwire
    · subst wire
      exact hlayout.scalarWire_not_equality
        (wire := registers.phase2) (by simp [PhaseUpdateRegisters.scalarWires])
          hwire
    · subst wire
      exact hlayout.scalarWire_not_equality
        (wire := registers.sign) (by simp [PhaseUpdateRegisters.scalarWires])
          hwire
    · subst wire
      exact hlayout.namedScratch_not_equality (wire := registers.zeroQ)
        (by simp) hwire
    · subst wire
      exact hlayout.namedScratch_not_equality (wire := registers.zeroRPrime)
        (by simp) hwire
    · subst wire
      exact hlayout.namedScratch_not_equality (wire := registers.zeroS)
        (by simp) hwire
    · subst wire
      exact hlayout.namedScratch_not_equality (wire := registers.condition)
        (by simp) hwire
    · subst wire
      exact hlayout.namedScratch_not_equality (wire := registers.temporary)
        (by simp) hwire
  rw [(phaseUpdateCore_usesOnly registers).preservesOutside state houtside]
  exact hclean wire hwire

private theorem phaseUpdate_coherent_seq_circuits
    {first second : Quantum.AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : Quantum.CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : Quantum.CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (Classical.run firstCircuit state)) :
    Quantum.CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [Quantum.run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact Quantum.supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit (Quantum.ket state)).symm

private theorem phaseUpdateAdaptive_measurementCount_seq
    (first second : Quantum.AdaptiveCircuit) :
    (first.seq second).measurementCount =
      first.measurementCount + second.measurementCount := by
  induction first with
  | done => simp [Quantum.AdaptiveCircuit.seq,
      Quantum.AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq,
        Quantum.AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq,
        Quantum.AdaptiveCircuit.measurementCount, ihFalse, ihTrue,
        Nat.add_max_add_right, Nat.add_assoc]

private theorem phaseUpdateAdaptive_tCount_seq
    (first second : Quantum.AdaptiveCircuit) :
    (first.seq second).tCount = first.tCount + second.tCount := by
  induction first with
  | done => simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount,
        ih, Nat.add_assoc]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

/-! ## Production borrowed-epoch specialization -/

/-- Extend the low shift-length word by the borrowed epoch discriminator exactly as the pinned
production generator does when `include_shift_epoch = True`. -/
def PhaseUpdateRegisters.withShiftEpoch
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) : PhaseUpdateRegisters :=
  { registers with lengthS := registers.lengthS ++ [shiftEpoch] }

/-- The physical production layout is precisely the generic layout after appending the borrowed
epoch wire to the third equality test. -/
abbrev PhaseUpdateEpochLayout
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) : Prop :=
  PhaseUpdateLayout (registers.withShiftEpoch shiftEpoch)

private def phaseUpdateEpochForwardTests
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) : Circuit :=
  let inner := registers.withShiftEpoch shiftEpoch
  mcxVChain inner.lengthQ inner.zeroQ inner.equalityScratch ++
    mcxVChain inner.lengthRPrime inner.zeroRPrime inner.equalityScratch ++
    [.X shiftEpoch] ++
    mcxVChain inner.lengthS inner.zeroS inner.equalityScratch ++
    [.X shiftEpoch]

private def phaseUpdateEpochCleanupTests
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) : Circuit :=
  let inner := registers.withShiftEpoch shiftEpoch
  ([.X shiftEpoch] : Circuit) ++
    mcxVChain inner.lengthS inner.zeroS inner.equalityScratch ++
    [.X shiftEpoch] ++
    mcxVChain inner.lengthRPrime inner.zeroRPrime inner.equalityScratch ++
    mcxVChain inner.lengthQ inner.zeroQ inner.equalityScratch

/-- Literal production circuit with each `X; equality; X` conjugation kept at its exact source
position. -/
def phaseUpdateEpochUnitary
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) : Circuit :=
  phaseUpdateEpochForwardTests registers shiftEpoch ++
    phaseUpdateCore (registers.withShiftEpoch shiftEpoch) ++
    phaseUpdateEpochCleanupTests registers shiftEpoch

private def toggleShiftEpoch (shiftEpoch : Wire) (state : BasisState) : BasisState :=
  state[shiftEpoch ↦ !state shiftEpoch]

private theorem wireAnd_append_singleton
    (wires : List Wire) (wire : Wire) (state : BasisState) :
    wireAnd (wires ++ [wire]) state =
      (wireAnd wires state && state wire) := by
  induction wires with
  | nil => simp [wireAnd]
  | cons head tail ih =>
      simp only [List.cons_append, wireAnd, ih, Bool.and_assoc]

/-- Gate-independent production state transition, expressed as the source's two epoch
conjugations around the already-explicit Boolean phase update. -/
def phaseUpdateEpochState
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState) : BasisState :=
  toggleShiftEpoch shiftEpoch
    (phaseUpdateState (registers.withShiftEpoch shiftEpoch)
      (toggleShiftEpoch shiftEpoch state))

private theorem phaseUpdate_shiftEpoch_mem_lengthWires
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    shiftEpoch ∈ (registers.withShiftEpoch shiftEpoch).lengthWires := by
  simp [PhaseUpdateRegisters.withShiftEpoch,
    PhaseUpdateRegisters.lengthWires]

private theorem PhaseUpdateEpochLayout.shiftEpoch_not_scratch
    {registers : PhaseUpdateRegisters} {shiftEpoch : Wire}
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    shiftEpoch ∉ registers.scratch := by
  intro hscratch
  exact (hlayout.lengthScratchNe
    (phaseUpdate_shiftEpoch_mem_lengthWires registers shiftEpoch)
    (by simpa [PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.scratch] using hscratch)) rfl

private theorem PhaseUpdateEpochLayout.shiftEpoch_not_lengths
    {registers : PhaseUpdateRegisters} {shiftEpoch : Wire}
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    shiftEpoch ∉ registers.lengthWires := by
  have hsub :
      ((registers.withShiftEpoch shiftEpoch).lengthWires ++
        (registers.withShiftEpoch shiftEpoch).scratch).Sublist
        (registers.withShiftEpoch shiftEpoch).allWires := by
    simpa [PhaseUpdateRegisters.allWires,
      PhaseUpdateRegisters.scalarWires,
      PhaseUpdateRegisters.lengthWires, List.append_assoc] using
      (List.sublist_append_right
        (registers.withShiftEpoch shiftEpoch).scalarWires
        ((registers.withShiftEpoch shiftEpoch).lengthWires ++
          (registers.withShiftEpoch shiftEpoch).scratch))
  have hlength := (List.nodup_append.mp
    (hsub.nodup hlayout.physical)).1
  have hsplit :
      (registers.lengthWires ++ [shiftEpoch]).Nodup := by
    simpa [PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.lengthWires, List.append_assoc] using hlength
  intro hmem
  exact (List.nodup_append.mp hsplit).2.2 shiftEpoch hmem shiftEpoch
    (by simp) rfl

private theorem PhaseUpdateEpochLayout.ready_toggle
    {registers : PhaseUpdateRegisters} {shiftEpoch : Wire}
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch)
    (state : BasisState)
    (hready : PhaseUpdateReady registers state) :
    PhaseUpdateReady (registers.withShiftEpoch shiftEpoch)
      (toggleShiftEpoch shiftEpoch state) := by
  apply clean_upd_not_mem registers.scratch state shiftEpoch (!state shiftEpoch)
  · exact hlayout.shiftEpoch_not_scratch
  · simpa [PhaseUpdateReady, PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.scratch] using hready

private theorem phaseUpdate_qr_usesOnly
    (registers : PhaseUpdateRegisters) :
    PaperCircuitUsesOnly (registers.lengthWires ++ registers.scratch)
      (mcxVChain registers.lengthQ registers.zeroQ registers.equalityScratch ++
        mcxVChain registers.lengthRPrime registers.zeroRPrime
          registers.equalityScratch) := by
  apply PaperCircuitUsesOnly.append
  · exact (mcxVChain_usesOnly registers.lengthQ registers.zeroQ
      registers.equalityScratch).mono (by
        intro wire hwire
        simp only [PhaseUpdateRegisters.lengthWires,
          PhaseUpdateRegisters.scratch, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hwire ⊢
        aesop)
  · exact (mcxVChain_usesOnly registers.lengthRPrime registers.zeroRPrime
      registers.equalityScratch).mono (by
        intro wire hwire
        simp only [PhaseUpdateRegisters.lengthWires,
          PhaseUpdateRegisters.scratch, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hwire ⊢
        aesop)

private theorem phaseUpdate_rq_usesOnly
    (registers : PhaseUpdateRegisters) :
    PaperCircuitUsesOnly (registers.lengthWires ++ registers.scratch)
      (mcxVChain registers.lengthRPrime registers.zeroRPrime
          registers.equalityScratch ++
        mcxVChain registers.lengthQ registers.zeroQ registers.equalityScratch) := by
  apply PaperCircuitUsesOnly.append
  · exact (mcxVChain_usesOnly registers.lengthRPrime registers.zeroRPrime
      registers.equalityScratch).mono (by
        intro wire hwire
        simp only [PhaseUpdateRegisters.lengthWires,
          PhaseUpdateRegisters.scratch, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hwire ⊢
        aesop)
  · exact (mcxVChain_usesOnly registers.lengthQ registers.zeroQ
      registers.equalityScratch).mono (by
        intro wire hwire
        simp only [PhaseUpdateRegisters.lengthWires,
          PhaseUpdateRegisters.scratch, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hwire ⊢
        aesop)

private theorem run_toggleShiftEpoch_commute
    {support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit)
    (shiftEpoch : Wire) (state : BasisState)
    (houtside : shiftEpoch ∉ support) :
    Classical.run circuit (toggleShiftEpoch shiftEpoch state) =
      toggleShiftEpoch shiftEpoch (Classical.run circuit state) := by
  unfold toggleShiftEpoch
  rw [huses.run_upd_outside shiftEpoch (!state shiftEpoch) state houtside,
    huses.preservesOutside state houtside]

private theorem toggleShiftEpoch_twice
    (shiftEpoch : Wire) (state : BasisState) :
    toggleShiftEpoch shiftEpoch (toggleShiftEpoch shiftEpoch state) = state := by
  funext wire
  by_cases hwire : wire = shiftEpoch
  · subst wire
    simp [toggleShiftEpoch, upd]
  · simp [toggleShiftEpoch, upd, hwire]

private theorem run_phaseUpdateEpochForwardTests_eq
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    Classical.run (phaseUpdateEpochForwardTests registers shiftEpoch) state =
      toggleShiftEpoch shiftEpoch
        (Classical.run
          (phaseUpdateForwardTests (registers.withShiftEpoch shiftEpoch))
          (toggleShiftEpoch shiftEpoch state)) := by
  let qr :=
    mcxVChain registers.lengthQ registers.zeroQ registers.equalityScratch ++
      mcxVChain registers.lengthRPrime registers.zeroRPrime
        registers.equalityScratch
  let s := mcxVChain (registers.lengthS ++ [shiftEpoch]) registers.zeroS
    registers.equalityScratch
  have hepochOutside : shiftEpoch ∉ registers.lengthWires ++ registers.scratch := by
    simp only [List.mem_append, not_or]
    exact ⟨hlayout.shiftEpoch_not_lengths, hlayout.shiftEpoch_not_scratch⟩
  have hcommute := run_toggleShiftEpoch_commute
    (phaseUpdate_qr_usesOnly registers) shiftEpoch state hepochOutside
  simp only [phaseUpdateEpochForwardTests, phaseUpdateForwardTests,
    PhaseUpdateRegisters.withShiftEpoch, Classical.run_append]
  have hx (input : BasisState) :
      Classical.run [.X shiftEpoch] input =
        toggleShiftEpoch shiftEpoch input := rfl
  rw [hx, hx]
  simpa [qr, s, Classical.run_append] using congrArg
    (fun input ↦ toggleShiftEpoch shiftEpoch (Classical.run s input))
    hcommute.symm

private theorem run_phaseUpdateEpochCleanupTests_eq
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    Classical.run (phaseUpdateEpochCleanupTests registers shiftEpoch) state =
      toggleShiftEpoch shiftEpoch
        (Classical.run
          (phaseUpdateCleanupTests (registers.withShiftEpoch shiftEpoch))
          (toggleShiftEpoch shiftEpoch state)) := by
  let s := mcxVChain (registers.lengthS ++ [shiftEpoch]) registers.zeroS
    registers.equalityScratch
  let rq :=
    mcxVChain registers.lengthRPrime registers.zeroRPrime
        registers.equalityScratch ++
      mcxVChain registers.lengthQ registers.zeroQ registers.equalityScratch
  have hepochOutside : shiftEpoch ∉ registers.lengthWires ++ registers.scratch := by
    simp only [List.mem_append, not_or]
    exact ⟨hlayout.shiftEpoch_not_lengths, hlayout.shiftEpoch_not_scratch⟩
  have hcommute := run_toggleShiftEpoch_commute
    (phaseUpdate_rq_usesOnly registers) shiftEpoch
      (Classical.run s (toggleShiftEpoch shiftEpoch state)) hepochOutside
  simp only [phaseUpdateEpochCleanupTests, phaseUpdateCleanupTests,
    PhaseUpdateRegisters.withShiftEpoch, Classical.run_append]
  have hx (input : BasisState) :
      Classical.run [.X shiftEpoch] input =
        toggleShiftEpoch shiftEpoch input := rfl
  rw [hx, hx]
  simpa [rq, s, Classical.run_append] using hcommute

private theorem run_phaseUpdateCore_toggleShiftEpoch
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    Classical.run (phaseUpdateCore (registers.withShiftEpoch shiftEpoch))
        (toggleShiftEpoch shiftEpoch state) =
      toggleShiftEpoch shiftEpoch
        (Classical.run (phaseUpdateCore (registers.withShiftEpoch shiftEpoch))
          state) := by
  let support := [registers.phase1, registers.phase2, registers.sign,
    registers.zeroQ, registers.zeroRPrime, registers.zeroS,
    registers.condition, registers.temporary]
  have huses : PaperCircuitUsesOnly support
      (phaseUpdateCore (registers.withShiftEpoch shiftEpoch)) := by
    simpa [support, PhaseUpdateRegisters.withShiftEpoch] using
      phaseUpdateCore_usesOnly (registers.withShiftEpoch shiftEpoch)
  have hepochOutside : shiftEpoch ∉ support := by
    have hp1Epoch := hlayout.scalarTailNe
      (scalar := registers.phase1) (wire := shiftEpoch)
      (by simp [PhaseUpdateRegisters.withShiftEpoch,
        PhaseUpdateRegisters.scalarWires])
      (List.mem_append_left _
        (phaseUpdate_shiftEpoch_mem_lengthWires registers shiftEpoch))
    have hp2Epoch := hlayout.scalarTailNe
      (scalar := registers.phase2) (wire := shiftEpoch)
      (by simp [PhaseUpdateRegisters.withShiftEpoch,
        PhaseUpdateRegisters.scalarWires])
      (List.mem_append_left _
        (phaseUpdate_shiftEpoch_mem_lengthWires registers shiftEpoch))
    have hsignEpoch := hlayout.scalarTailNe
      (scalar := registers.sign) (wire := shiftEpoch)
      (by simp [PhaseUpdateRegisters.withShiftEpoch,
        PhaseUpdateRegisters.scalarWires])
      (List.mem_append_left _
        (phaseUpdate_shiftEpoch_mem_lengthWires registers shiftEpoch))
    have hscratch := hlayout.shiftEpoch_not_scratch
    simp only [PhaseUpdateRegisters.scratch, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or] at hscratch
    simp [support, Ne.symm hp1Epoch, Ne.symm hp2Epoch,
      Ne.symm hsignEpoch, hscratch]
  exact run_toggleShiftEpoch_commute huses shiftEpoch state hepochOutside

/-- Direct whole-state correctness of the production epoch-aware source circuit. -/
theorem run_phaseUpdateEpochUnitary
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch)
    (hready : PhaseUpdateReady registers state) :
    Classical.run (phaseUpdateEpochUnitary registers shiftEpoch) state =
      phaseUpdateEpochState registers shiftEpoch state := by
  let inner := registers.withShiftEpoch shiftEpoch
  have hforward := run_phaseUpdateEpochForwardTests_eq registers shiftEpoch
    state hlayout
  have hcore := run_phaseUpdateCore_toggleShiftEpoch registers shiftEpoch
    (Classical.run (phaseUpdateForwardTests inner)
      (toggleShiftEpoch shiftEpoch state)) hlayout
  rw [phaseUpdateEpochUnitary, Classical.run_append, Classical.run_append,
    hforward, hcore]
  rw [run_phaseUpdateEpochCleanupTests_eq registers shiftEpoch _ hlayout]
  rw [toggleShiftEpoch_twice]
  have hbase := run_phaseUpdateUnitary inner
    (toggleShiftEpoch shiftEpoch state) hlayout
    (hlayout.ready_toggle state hready)
  rw [phaseUpdateUnitary, Classical.run_append, Classical.run_append] at hbase
  rw [hbase]
  rfl

/-- The appended control recognizes encoded shift zero exactly when every low-word bit is one and
the borrowed epoch discriminator is zero. -/
theorem phaseUpdateEpochState_spec
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    phaseUpdateEpochState registers shiftEpoch state =
      let zeroQ := wireAnd registers.lengthQ state
      let zeroRPrime := wireAnd registers.lengthRPrime state
      let zeroS := wireAnd registers.lengthS state && !state shiftEpoch
      let condition := zeroQ && !zeroRPrime
      let phase2 := Bool.xor (state registers.phase2)
        (condition && Bool.xor (state registers.sign) (state registers.phase1))
      let sign := Bool.xor (state registers.sign) (condition && phase2)
      state
        [registers.phase1 ↦ Bool.xor (state registers.phase1) zeroS]
        [registers.phase2 ↦ Bool.xor phase2 zeroS]
        [registers.sign ↦ sign] := by
  have hepochLengths := hlayout.shiftEpoch_not_lengths
  simp only [PhaseUpdateRegisters.lengthWires, List.mem_append,
    not_or] at hepochLengths
  have hepochQ := hepochLengths.1.1
  have hepochRPrime := hepochLengths.1.2
  have hepochS := hepochLengths.2
  have hp1Epoch := hlayout.scalarTailNe
    (scalar := registers.phase1) (wire := shiftEpoch)
    (by simp [PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.scalarWires])
    (List.mem_append_left _
      (phaseUpdate_shiftEpoch_mem_lengthWires registers shiftEpoch))
  have hp2Epoch := hlayout.scalarTailNe
    (scalar := registers.phase2) (wire := shiftEpoch)
    (by simp [PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.scalarWires])
    (List.mem_append_left _
      (phaseUpdate_shiftEpoch_mem_lengthWires registers shiftEpoch))
  have hsignEpoch := hlayout.scalarTailNe
    (scalar := registers.sign) (wire := shiftEpoch)
    (by simp [PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.scalarWires])
    (List.mem_append_left _
      (phaseUpdate_shiftEpoch_mem_lengthWires registers shiftEpoch))
  unfold phaseUpdateEpochState phaseUpdateState toggleShiftEpoch
  simp only [PhaseUpdateRegisters.withShiftEpoch]
  rw [wireAnd_upd_not_mem _ _ _ _ hepochQ,
    wireAnd_upd_not_mem _ _ _ _ hepochRPrime,
    wireAnd_append_singleton,
    wireAnd_upd_not_mem _ _ _ _ hepochS]
  funext wire
  by_cases hwire : wire = shiftEpoch
  · subst wire
    simp [upd, Ne.symm hp1Epoch, Ne.symm hp2Epoch, Ne.symm hsignEpoch]
  · simp [upd, hwire, hp1Epoch, hp2Epoch, hsignEpoch]

theorem phaseUpdateEpochState_preserves_scratch
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch)
    {wire : Wire} (hwire : wire ∈ registers.scratch) :
    phaseUpdateEpochState registers shiftEpoch state wire = state wire := by
  have hwireEpoch : wire ≠ shiftEpoch := by
    intro equality
    subst wire
    exact hlayout.shiftEpoch_not_scratch hwire
  unfold phaseUpdateEpochState toggleShiftEpoch
  rw [upd_other _ shiftEpoch _ hwireEpoch]
  change phaseUpdateState (registers.withShiftEpoch shiftEpoch)
      (toggleShiftEpoch shiftEpoch state) wire = state wire
  rw [phaseUpdateState_preserves_scratch
    (registers.withShiftEpoch shiftEpoch)
    (toggleShiftEpoch shiftEpoch state) hlayout
    (by simpa [PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.scratch] using hwire)]
  simp [toggleShiftEpoch, upd, hwireEpoch]

/-- The production wrapper restores the same shared scratch boundary. -/
theorem phaseUpdateEpochUnitary_ready
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch)
    (hready : PhaseUpdateReady registers state) :
    PhaseUpdateReady registers
      (Classical.run (phaseUpdateEpochUnitary registers shiftEpoch) state) := by
  rw [run_phaseUpdateEpochUnitary registers shiftEpoch state hlayout hready]
  intro wire hwire
  rw [phaseUpdateEpochState_preserves_scratch registers shiftEpoch state
    hlayout hwire]
  exact hready wire hwire

/-- Complete physical support of the production epoch-aware block. -/
def PhaseUpdateRegisters.epochWires
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) : List Wire :=
  (registers.withShiftEpoch shiftEpoch).allWires

private theorem phaseUpdateEpochForwardTests_usesOnly
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    PaperCircuitUsesOnly (registers.epochWires shiftEpoch)
      (phaseUpdateEpochForwardTests registers shiftEpoch) := by
  let inner := registers.withShiftEpoch shiftEpoch
  have hq := (mcxVChain_usesOnly inner.lengthQ inner.zeroQ
    inner.equalityScratch).mono fun wire hwire ↦
      (phaseUpdate_q_sublist inner).mem hwire
  have hr := (mcxVChain_usesOnly inner.lengthRPrime inner.zeroRPrime
    inner.equalityScratch).mono fun wire hwire ↦
      (phaseUpdate_rPrime_sublist inner).mem hwire
  have hs := (mcxVChain_usesOnly inner.lengthS inner.zeroS
    inner.equalityScratch).mono fun wire hwire ↦
      (phaseUpdate_s_sublist inner).mem hwire
  have hx : PaperCircuitUsesOnly inner.allWires
      ([.X shiftEpoch] : Circuit) := by
    simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires, inner,
      PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.allWires]
  rw [phaseUpdateEpochForwardTests]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply PaperCircuitUsesOnly.append
      · exact PaperCircuitUsesOnly.append hq hr
      · exact hx
    · exact hs
  · exact hx

private theorem phaseUpdateEpochCleanupTests_usesOnly
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    PaperCircuitUsesOnly (registers.epochWires shiftEpoch)
      (phaseUpdateEpochCleanupTests registers shiftEpoch) := by
  let inner := registers.withShiftEpoch shiftEpoch
  have hq := (mcxVChain_usesOnly inner.lengthQ inner.zeroQ
    inner.equalityScratch).mono fun wire hwire ↦
      (phaseUpdate_q_sublist inner).mem hwire
  have hr := (mcxVChain_usesOnly inner.lengthRPrime inner.zeroRPrime
    inner.equalityScratch).mono fun wire hwire ↦
      (phaseUpdate_rPrime_sublist inner).mem hwire
  have hs := (mcxVChain_usesOnly inner.lengthS inner.zeroS
    inner.equalityScratch).mono fun wire hwire ↦
      (phaseUpdate_s_sublist inner).mem hwire
  have hx : PaperCircuitUsesOnly inner.allWires
      ([.X shiftEpoch] : Circuit) := by
    simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires, inner,
      PhaseUpdateRegisters.withShiftEpoch,
      PhaseUpdateRegisters.allWires]
  rw [phaseUpdateEpochCleanupTests]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply PaperCircuitUsesOnly.append
      · exact PaperCircuitUsesOnly.append hx hs
      · exact hx
    · exact hr
  · exact hq

/-- Every production gate, including the two epoch conjugations, lies in the declared support. -/
theorem phaseUpdateEpochUnitary_usesOnly
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    PaperCircuitUsesOnly (registers.epochWires shiftEpoch)
      (phaseUpdateEpochUnitary registers shiftEpoch) := by
  rw [phaseUpdateEpochUnitary]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · exact phaseUpdateEpochForwardTests_usesOnly registers shiftEpoch
    · intro gate hgate wire hwire
      exact phaseUpdateUnitary_usesOnly
        (registers.withShiftEpoch shiftEpoch) gate
        (by simp [phaseUpdateUnitary, hgate]) wire hwire
  · exact phaseUpdateEpochCleanupTests_usesOnly registers shiftEpoch

theorem phaseUpdateEpochUnitary_preservesOutside
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState) {wire : Wire}
    (hwire : wire ∉ registers.epochWires shiftEpoch) :
    Classical.run (phaseUpdateEpochUnitary registers shiftEpoch) state wire =
      state wire :=
  (phaseUpdateEpochUnitary_usesOnly registers shiftEpoch).preservesOutside
    state hwire

@[simp]
theorem phaseUpdateEpochUnitary_HPFree
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    HPFree (phaseUpdateEpochUnitary registers shiftEpoch) := by
  simp [phaseUpdateEpochUnitary, phaseUpdateEpochForwardTests,
    phaseUpdateEpochCleanupTests, phaseUpdateCore]

private theorem phaseUpdateEpochForwardTests_wellFormed
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    CircuitWellFormed (phaseUpdateEpochForwardTests registers shiftEpoch) := by
  let inner := registers.withShiftEpoch shiftEpoch
  have hq := mcxVChain_wellFormed inner.lengthQ inner.zeroQ
    inner.equalityScratch hlayout.q_capacity hlayout.qChain
  have hr := mcxVChain_wellFormed inner.lengthRPrime inner.zeroRPrime
    inner.equalityScratch hlayout.rPrime_capacity hlayout.rPrimeChain
  have hs := mcxVChain_wellFormed inner.lengthS inner.zeroS
    inner.equalityScratch hlayout.s_capacity hlayout.sChain
  rw [phaseUpdateEpochForwardTests, circuitWellFormed_append,
    circuitWellFormed_append, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨⟨⟨hq, hr⟩,
    by simp [CircuitWellFormed, Gate.WellFormed]⟩, hs⟩,
    by simp [CircuitWellFormed, Gate.WellFormed]⟩

private theorem phaseUpdateEpochCleanupTests_wellFormed
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    CircuitWellFormed (phaseUpdateEpochCleanupTests registers shiftEpoch) := by
  let inner := registers.withShiftEpoch shiftEpoch
  have hq := mcxVChain_wellFormed inner.lengthQ inner.zeroQ
    inner.equalityScratch hlayout.q_capacity hlayout.qChain
  have hr := mcxVChain_wellFormed inner.lengthRPrime inner.zeroRPrime
    inner.equalityScratch hlayout.rPrime_capacity hlayout.rPrimeChain
  have hs := mcxVChain_wellFormed inner.lengthS inner.zeroS
    inner.equalityScratch hlayout.s_capacity hlayout.sChain
  rw [phaseUpdateEpochCleanupTests, circuitWellFormed_append,
    circuitWellFormed_append, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨⟨⟨by simp [CircuitWellFormed, Gate.WellFormed], hs⟩,
    by simp [CircuitWellFormed, Gate.WellFormed]⟩, hr⟩, hq⟩

theorem phaseUpdateEpochUnitary_wellFormed
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    CircuitWellFormed (phaseUpdateEpochUnitary registers shiftEpoch) := by
  rw [phaseUpdateEpochUnitary, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨phaseUpdateEpochForwardTests_wellFormed
      registers shiftEpoch hlayout,
    phaseUpdateCore_wellFormed
      (registers.withShiftEpoch shiftEpoch) hlayout⟩,
    phaseUpdateEpochCleanupTests_wellFormed
      registers shiftEpoch hlayout⟩

@[simp]
theorem phaseUpdateEpochUnitary_toffoliCount
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    eeaToffoliCount (phaseUpdateEpochUnitary registers shiftEpoch) =
      2 * (mcxVChainToffoliCost registers.lengthQ.length +
        mcxVChainToffoliCost registers.lengthRPrime.length +
        mcxVChainToffoliCost (registers.lengthS.length + 1)) + 4 := by
  have hq := mcxVChain_toffoliCount registers.lengthQ registers.zeroQ
    registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.q_capacity)
  have hr := mcxVChain_toffoliCount registers.lengthRPrime registers.zeroRPrime
    registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.rPrime_capacity)
  have hs := mcxVChain_toffoliCount (registers.lengthS ++ [shiftEpoch])
    registers.zeroS registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.s_capacity)
  have hforward :
      eeaToffoliCount (phaseUpdateEpochForwardTests registers shiftEpoch) =
        mcxVChainToffoliCost registers.lengthQ.length +
          mcxVChainToffoliCost registers.lengthRPrime.length +
          mcxVChainToffoliCost (registers.lengthS.length + 1) := by
    simp only [phaseUpdateEpochForwardTests,
      PhaseUpdateRegisters.withShiftEpoch, eeaToffoliCount_append,
      hq, hr, hs, List.length_append, List.length_singleton]
    simp [eeaToffoliCount]
  have hcleanup :
      eeaToffoliCount (phaseUpdateEpochCleanupTests registers shiftEpoch) =
        mcxVChainToffoliCost (registers.lengthS.length + 1) +
          mcxVChainToffoliCost registers.lengthRPrime.length +
          mcxVChainToffoliCost registers.lengthQ.length := by
    simp only [phaseUpdateEpochCleanupTests,
      PhaseUpdateRegisters.withShiftEpoch, eeaToffoliCount_append,
      hq, hr, hs, List.length_append, List.length_singleton]
    simp [eeaToffoliCount]
  have hcore : eeaToffoliCount
      (phaseUpdateCore (registers.withShiftEpoch shiftEpoch)) = 4 := by
    rfl
  rw [phaseUpdateEpochUnitary, eeaToffoliCount_append,
    eeaToffoliCount_append, hforward, hcore, hcleanup]
  omega

@[simp]
theorem phaseUpdateEpochUnitary_cnotCount
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    eeaCnotCount (phaseUpdateEpochUnitary registers shiftEpoch) =
      2 * (mcxVChainCnotCost registers.lengthQ.length +
        mcxVChainCnotCost registers.lengthRPrime.length +
        mcxVChainCnotCost (registers.lengthS.length + 1)) + 6 := by
  have hq := mcxVChain_cnotCount registers.lengthQ registers.zeroQ
    registers.equalityScratch
  have hr := mcxVChain_cnotCount registers.lengthRPrime registers.zeroRPrime
    registers.equalityScratch
  have hs := mcxVChain_cnotCount (registers.lengthS ++ [shiftEpoch])
    registers.zeroS registers.equalityScratch
  have hforward :
      eeaCnotCount (phaseUpdateEpochForwardTests registers shiftEpoch) =
        mcxVChainCnotCost registers.lengthQ.length +
          mcxVChainCnotCost registers.lengthRPrime.length +
          mcxVChainCnotCost (registers.lengthS.length + 1) := by
    simp only [phaseUpdateEpochForwardTests,
      PhaseUpdateRegisters.withShiftEpoch, eeaCnotCount_append,
      hq, hr, hs, List.length_append, List.length_singleton]
    simp [eeaCnotCount]
  have hcleanup :
      eeaCnotCount (phaseUpdateEpochCleanupTests registers shiftEpoch) =
        mcxVChainCnotCost (registers.lengthS.length + 1) +
          mcxVChainCnotCost registers.lengthRPrime.length +
          mcxVChainCnotCost registers.lengthQ.length := by
    simp only [phaseUpdateEpochCleanupTests,
      PhaseUpdateRegisters.withShiftEpoch, eeaCnotCount_append,
      hq, hr, hs, List.length_append, List.length_singleton]
    simp [eeaCnotCount]
  have hcore : eeaCnotCount
      (phaseUpdateCore (registers.withShiftEpoch shiftEpoch)) = 6 := by
    rfl
  rw [phaseUpdateEpochUnitary, eeaCnotCount_append,
    eeaCnotCount_append, hforward, hcore, hcleanup]
  omega

@[simp]
theorem phaseUpdateEpochUnitary_tCount
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    ShorECDLP.tCount (phaseUpdateEpochUnitary registers shiftEpoch) =
      7 * (2 * (mcxVChainToffoliCost registers.lengthQ.length +
        mcxVChainToffoliCost registers.lengthRPrime.length +
        mcxVChainToffoliCost (registers.lengthS.length + 1)) + 4) := by
  have hq := mcxVChain_tCount registers.lengthQ registers.zeroQ
    registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.q_capacity)
  have hr := mcxVChain_tCount registers.lengthRPrime registers.zeroRPrime
    registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.rPrime_capacity)
  have hs := mcxVChain_tCount (registers.lengthS ++ [shiftEpoch])
    registers.zeroS registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.s_capacity)
  have hforward :
      ShorECDLP.tCount (phaseUpdateEpochForwardTests registers shiftEpoch) =
        7 * mcxVChainToffoliCost registers.lengthQ.length +
          7 * mcxVChainToffoliCost registers.lengthRPrime.length +
          7 * mcxVChainToffoliCost (registers.lengthS.length + 1) := by
    simp only [phaseUpdateEpochForwardTests,
      PhaseUpdateRegisters.withShiftEpoch, tCount_append,
      hq, hr, hs, List.length_append, List.length_singleton]
    simp [ShorECDLP.tCount, ShorECDLP.tCost]
  have hcleanup :
      ShorECDLP.tCount (phaseUpdateEpochCleanupTests registers shiftEpoch) =
        7 * mcxVChainToffoliCost (registers.lengthS.length + 1) +
          7 * mcxVChainToffoliCost registers.lengthRPrime.length +
          7 * mcxVChainToffoliCost registers.lengthQ.length := by
    simp only [phaseUpdateEpochCleanupTests,
      PhaseUpdateRegisters.withShiftEpoch, tCount_append,
      hq, hr, hs, List.length_append, List.length_singleton]
    simp [ShorECDLP.tCount, ShorECDLP.tCost]
  have hcore : ShorECDLP.tCount
      (phaseUpdateCore (registers.withShiftEpoch shiftEpoch)) = 28 := by
    rfl
  rw [phaseUpdateEpochUnitary, tCount_append, tCount_append,
    hforward, hcore, hcleanup]
  omega

private def phaseUpdateEpochForwardTestsAdaptive
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    Quantum.AdaptiveCircuit :=
  let inner := registers.withShiftEpoch shiftEpoch
  (((((mcxVChainAdaptive inner.lengthQ inner.zeroQ inner.equalityScratch).seq
    (mcxVChainAdaptive inner.lengthRPrime inner.zeroRPrime
      inner.equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done)).seq
    (mcxVChainAdaptive inner.lengthS inner.zeroS inner.equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done))

private def phaseUpdateEpochCleanupTestsAdaptive
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    Quantum.AdaptiveCircuit :=
  let inner := registers.withShiftEpoch shiftEpoch
  (((((Quantum.AdaptiveCircuit.unitary [.X shiftEpoch] .done).seq
    (mcxVChainAdaptive inner.lengthS inner.zeroS inner.equalityScratch)).seq
    (.unitary [.X shiftEpoch] .done)).seq
    (mcxVChainAdaptive inner.lengthRPrime inner.zeroRPrime
      inner.equalityScratch)).seq
    (mcxVChainAdaptive inner.lengthQ inner.zeroQ inner.equalityScratch))

/-- Production adaptive term.  As in the source, the epoch conjugations remain unitary at their
literal test boundaries while every eligible v-chain cleanup follows the global
measurement-uncomputation mode. -/
def phaseUpdateEpochAdaptive
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire) :
    Quantum.AdaptiveCircuit :=
  ((phaseUpdateEpochForwardTestsAdaptive registers shiftEpoch).seq
    (.unitary (phaseUpdateCore (registers.withShiftEpoch shiftEpoch)) .done)).seq
  (phaseUpdateEpochCleanupTestsAdaptive registers shiftEpoch)

private theorem phaseUpdateEpochX_preservesEqualityClean
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch)
    (hclean : Clean registers.equalityScratch state) :
    Clean registers.equalityScratch
      (Classical.run [.X shiftEpoch] state) := by
  change Clean registers.equalityScratch
    (toggleShiftEpoch shiftEpoch state)
  apply clean_upd_not_mem registers.equalityScratch state shiftEpoch
    (!state shiftEpoch)
  · intro hequality
    exact hlayout.shiftEpoch_not_scratch (by
      simp [PhaseUpdateRegisters.scratch, hequality])
  · exact hclean

private theorem phaseUpdateEpochForwardTestsAdaptive_coherent
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    Quantum.CoherentlyImplementsOn
      (phaseUpdateEpochForwardTestsAdaptive registers shiftEpoch)
      (Quantum.run (phaseUpdateEpochForwardTests registers shiftEpoch))
      (fun state ↦ Clean registers.equalityScratch state) := by
  let inner := registers.withShiftEpoch shiftEpoch
  let qCircuit := mcxVChain inner.lengthQ inner.zeroQ inner.equalityScratch
  let rCircuit := mcxVChain inner.lengthRPrime inner.zeroRPrime inner.equalityScratch
  let sCircuit := mcxVChain inner.lengthS inner.zeroS inner.equalityScratch
  let epochX : Circuit := [.X shiftEpoch]
  let qAdaptive := mcxVChainAdaptive inner.lengthQ inner.zeroQ inner.equalityScratch
  let rAdaptive := mcxVChainAdaptive inner.lengthRPrime inner.zeroRPrime inner.equalityScratch
  let sAdaptive := mcxVChainAdaptive inner.lengthS inner.zeroS inner.equalityScratch
  have hlayoutInner : PhaseUpdateLayout inner := by
    simpa [inner] using hlayout
  have hq := mcxVChainAdaptive_coherent inner.lengthQ inner.zeroQ
    inner.equalityScratch hlayoutInner.q_capacity hlayoutInner.qChain
  have hr := mcxVChainAdaptive_coherent inner.lengthRPrime inner.zeroRPrime
    inner.equalityScratch hlayoutInner.rPrime_capacity hlayoutInner.rPrimeChain
  have hs := mcxVChainAdaptive_coherent inner.lengthS inner.zeroS
    inner.equalityScratch hlayoutInner.s_capacity hlayoutInner.sChain
  have hx := Quantum.CoherentlyImplementsOn.unitary epochX
    (fun state ↦ Clean registers.equalityScratch state)
  have hxHPFree : HPFree epochX := by
    simp [epochX, HPFree]
  have hqPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch (Classical.run qCircuit state) := by
    intro state hclean
    exact phaseUpdate_mcx_preservesEqualityClean inner inner.lengthQ inner.zeroQ
      state hlayoutInner.q_capacity hlayoutInner.qChain
      (hlayoutInner.namedScratch_not_equality (wire := inner.zeroQ) (by simp)) hclean
  have hrPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch (Classical.run rCircuit state) := by
    intro state hclean
    exact phaseUpdate_mcx_preservesEqualityClean inner inner.lengthRPrime
      inner.zeroRPrime state hlayoutInner.rPrime_capacity hlayoutInner.rPrimeChain
      (hlayoutInner.namedScratch_not_equality (wire := inner.zeroRPrime) (by simp)) hclean
  have hsPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch (Classical.run sCircuit state) := by
    intro state hclean
    exact phaseUpdate_mcx_preservesEqualityClean inner inner.lengthS inner.zeroS
      state hlayoutInner.s_capacity hlayoutInner.sChain
      (hlayoutInner.namedScratch_not_equality (wire := inner.zeroS) (by simp)) hclean
  have hxPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch (Classical.run epochX state) := by
    intro state hclean
    exact phaseUpdateEpochX_preservesEqualityClean registers shiftEpoch state
      hlayout hclean
  have hqr := phaseUpdate_coherent_seq_circuits hq hr
    (by simp) hqPreserves
  have hqrPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch
        (Classical.run (qCircuit ++ rCircuit) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact hrPreserves _ (hqPreserves state hclean)
  have hqrx := phaseUpdate_coherent_seq_circuits hqr hx
    (by simp) hqrPreserves
  have hqrxPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch
        (Classical.run (qCircuit ++ rCircuit ++ epochX) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact hxPreserves _ (hqrPreserves state hclean)
  have hqrxs := phaseUpdate_coherent_seq_circuits hqrx hs
    (by simpa using hxHPFree) hqrxPreserves
  have hqrxsPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch
        (Classical.run (qCircuit ++ rCircuit ++ epochX ++ sCircuit) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact hsPreserves _ (hqrxPreserves state hclean)
  have hall := phaseUpdate_coherent_seq_circuits hqrxs hx
    (by simpa using hxHPFree) hqrxsPreserves
  simpa [phaseUpdateEpochForwardTestsAdaptive,
    phaseUpdateEpochForwardTests, inner, qCircuit, rCircuit, sCircuit,
    epochX, qAdaptive, rAdaptive, sAdaptive] using hall

private theorem phaseUpdateEpochCleanupTestsAdaptive_coherent
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    Quantum.CoherentlyImplementsOn
      (phaseUpdateEpochCleanupTestsAdaptive registers shiftEpoch)
      (Quantum.run (phaseUpdateEpochCleanupTests registers shiftEpoch))
      (fun state ↦ Clean registers.equalityScratch state) := by
  let inner := registers.withShiftEpoch shiftEpoch
  let qCircuit := mcxVChain inner.lengthQ inner.zeroQ inner.equalityScratch
  let rCircuit := mcxVChain inner.lengthRPrime inner.zeroRPrime inner.equalityScratch
  let sCircuit := mcxVChain inner.lengthS inner.zeroS inner.equalityScratch
  let epochX : Circuit := [.X shiftEpoch]
  let qAdaptive := mcxVChainAdaptive inner.lengthQ inner.zeroQ inner.equalityScratch
  let rAdaptive := mcxVChainAdaptive inner.lengthRPrime inner.zeroRPrime inner.equalityScratch
  let sAdaptive := mcxVChainAdaptive inner.lengthS inner.zeroS inner.equalityScratch
  have hlayoutInner : PhaseUpdateLayout inner := by
    simpa [inner] using hlayout
  have hq := mcxVChainAdaptive_coherent inner.lengthQ inner.zeroQ
    inner.equalityScratch hlayoutInner.q_capacity hlayoutInner.qChain
  have hr := mcxVChainAdaptive_coherent inner.lengthRPrime inner.zeroRPrime
    inner.equalityScratch hlayoutInner.rPrime_capacity hlayoutInner.rPrimeChain
  have hs := mcxVChainAdaptive_coherent inner.lengthS inner.zeroS
    inner.equalityScratch hlayoutInner.s_capacity hlayoutInner.sChain
  have hx := Quantum.CoherentlyImplementsOn.unitary epochX
    (fun state ↦ Clean registers.equalityScratch state)
  have hxHPFree : HPFree epochX := by
    simp [epochX, HPFree]
  have hqPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch (Classical.run qCircuit state) := by
    intro state hclean
    exact phaseUpdate_mcx_preservesEqualityClean inner inner.lengthQ inner.zeroQ
      state hlayoutInner.q_capacity hlayoutInner.qChain
      (hlayoutInner.namedScratch_not_equality (wire := inner.zeroQ) (by simp)) hclean
  have hrPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch (Classical.run rCircuit state) := by
    intro state hclean
    exact phaseUpdate_mcx_preservesEqualityClean inner inner.lengthRPrime
      inner.zeroRPrime state hlayoutInner.rPrime_capacity hlayoutInner.rPrimeChain
      (hlayoutInner.namedScratch_not_equality (wire := inner.zeroRPrime) (by simp)) hclean
  have hsPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch (Classical.run sCircuit state) := by
    intro state hclean
    exact phaseUpdate_mcx_preservesEqualityClean inner inner.lengthS inner.zeroS
      state hlayoutInner.s_capacity hlayoutInner.sChain
      (hlayoutInner.namedScratch_not_equality (wire := inner.zeroS) (by simp)) hclean
  have hxPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch (Classical.run epochX state) := by
    intro state hclean
    exact phaseUpdateEpochX_preservesEqualityClean registers shiftEpoch state
      hlayout hclean
  have hxs := phaseUpdate_coherent_seq_circuits hx hs
    hxHPFree hxPreserves
  have hxsPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch
        (Classical.run (epochX ++ sCircuit) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact hsPreserves _ (hxPreserves state hclean)
  have hxsx := phaseUpdate_coherent_seq_circuits hxs hx
    (by simpa using hxHPFree) hxsPreserves
  have hxsxPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch
        (Classical.run (epochX ++ sCircuit ++ epochX) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact hxPreserves _ (hxsPreserves state hclean)
  have hxsxr := phaseUpdate_coherent_seq_circuits hxsx hr
    (by simpa using hxHPFree) hxsxPreserves
  have hxsxrPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch
        (Classical.run (epochX ++ sCircuit ++ epochX ++ rCircuit) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact hrPreserves _ (hxsxPreserves state hclean)
  have hall := phaseUpdate_coherent_seq_circuits hxsxr hq
    (by simpa using hxHPFree) hxsxrPreserves
  simpa [phaseUpdateEpochCleanupTestsAdaptive,
    phaseUpdateEpochCleanupTests, inner, qCircuit, rCircuit, sCircuit,
    epochX, qAdaptive, rAdaptive, sAdaptive] using hall

private theorem phaseUpdateEpochForwardTests_preservesEqualityClean
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (state : BasisState)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch)
    (hclean : Clean registers.equalityScratch state) :
    Clean registers.equalityScratch
      (Classical.run (phaseUpdateEpochForwardTests registers shiftEpoch) state) := by
  rw [run_phaseUpdateEpochForwardTests_eq registers shiftEpoch state hlayout]
  exact phaseUpdateEpochX_preservesEqualityClean registers shiftEpoch _ hlayout
    (phaseUpdateForwardTests_preservesEqualityClean
      (registers.withShiftEpoch shiftEpoch)
      (toggleShiftEpoch shiftEpoch state) hlayout
      (phaseUpdateEpochX_preservesEqualityClean registers shiftEpoch state
        hlayout hclean))

private theorem phaseUpdateEpochAdaptive_coherent_equalityClean
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    Quantum.CoherentlyImplementsOn
      (phaseUpdateEpochAdaptive registers shiftEpoch)
      (Quantum.run (phaseUpdateEpochUnitary registers shiftEpoch))
      (fun state ↦ Clean registers.equalityScratch state) := by
  have hforward := phaseUpdateEpochForwardTestsAdaptive_coherent
    registers shiftEpoch hlayout
  have hcore := Quantum.CoherentlyImplementsOn.unitary
    (phaseUpdateCore (registers.withShiftEpoch shiftEpoch))
    (fun state ↦ Clean registers.equalityScratch state)
  have hforwardCore := phaseUpdate_coherent_seq_circuits hforward hcore
    (by simp [phaseUpdateEpochForwardTests])
    (fun state hclean ↦
      phaseUpdateEpochForwardTests_preservesEqualityClean registers
        shiftEpoch state hlayout hclean)
  have hcleanup := phaseUpdateEpochCleanupTestsAdaptive_coherent
    registers shiftEpoch hlayout
  have hprefixPreserves : ∀ state, Clean registers.equalityScratch state →
      Clean registers.equalityScratch
        (Classical.run
          (phaseUpdateEpochForwardTests registers shiftEpoch ++
            phaseUpdateCore (registers.withShiftEpoch shiftEpoch)) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact phaseUpdateCore_preservesEqualityClean
      (registers.withShiftEpoch shiftEpoch) _ hlayout
      (phaseUpdateEpochForwardTests_preservesEqualityClean registers
        shiftEpoch state hlayout hclean)
  have hall := phaseUpdate_coherent_seq_circuits hforwardCore hcleanup
    (by simp [phaseUpdateEpochForwardTests, phaseUpdateCore]) hprefixPreserves
  simpa [phaseUpdateEpochAdaptive, phaseUpdateEpochUnitary] using hall

/-- Every adaptive branch of the epoch-aware production term is coefficient-aligned with its
exact coherent source circuit. -/
theorem phaseUpdateEpochAdaptive_coherent
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    Quantum.CoherentlyImplementsOn
      (phaseUpdateEpochAdaptive registers shiftEpoch)
      (Quantum.run (phaseUpdateEpochUnitary registers shiftEpoch))
      (PhaseUpdateReady registers) := by
  rcases phaseUpdateEpochAdaptive_coherent_equalityClean registers shiftEpoch
    hlayout with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hready ↦
    hbranch state (by
      intro wire hwire
      exact hready wire (by
        simp [PhaseUpdateRegisters.scratch, hwire]))

private theorem phaseUpdateEpochForwardTestsAdaptive_wellFormed
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    (phaseUpdateEpochForwardTestsAdaptive registers shiftEpoch).WellFormed := by
  simp only [phaseUpdateEpochForwardTestsAdaptive]
  apply Quantum.AdaptiveCircuit.WellFormed.seq
  · apply Quantum.AdaptiveCircuit.WellFormed.seq
    · apply Quantum.AdaptiveCircuit.WellFormed.seq
      · exact Quantum.AdaptiveCircuit.WellFormed.seq
          (mcxVChainAdaptive_wellFormed _ _ _ hlayout.q_capacity hlayout.qChain)
          (mcxVChainAdaptive_wellFormed _ _ _ hlayout.rPrime_capacity
            hlayout.rPrimeChain)
      · simp [Quantum.AdaptiveCircuit.WellFormed,
          CircuitWellFormed, Gate.WellFormed]
    · exact mcxVChainAdaptive_wellFormed _ _ _ hlayout.s_capacity
        hlayout.sChain
  · simp [Quantum.AdaptiveCircuit.WellFormed,
      CircuitWellFormed, Gate.WellFormed]

private theorem phaseUpdateEpochCleanupTestsAdaptive_wellFormed
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    (phaseUpdateEpochCleanupTestsAdaptive registers shiftEpoch).WellFormed := by
  simp only [phaseUpdateEpochCleanupTestsAdaptive]
  apply Quantum.AdaptiveCircuit.WellFormed.seq
  · apply Quantum.AdaptiveCircuit.WellFormed.seq
    · apply Quantum.AdaptiveCircuit.WellFormed.seq
      · exact Quantum.AdaptiveCircuit.WellFormed.seq
          (by simp [Quantum.AdaptiveCircuit.WellFormed,
            CircuitWellFormed, Gate.WellFormed])
          (mcxVChainAdaptive_wellFormed _ _ _ hlayout.s_capacity
            hlayout.sChain)
      · simp [Quantum.AdaptiveCircuit.WellFormed,
          CircuitWellFormed, Gate.WellFormed]
    · exact mcxVChainAdaptive_wellFormed _ _ _ hlayout.rPrime_capacity
        hlayout.rPrimeChain
  · exact mcxVChainAdaptive_wellFormed _ _ _ hlayout.q_capacity
      hlayout.qChain

theorem phaseUpdateEpochAdaptive_wellFormed
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    (phaseUpdateEpochAdaptive registers shiftEpoch).WellFormed := by
  rw [phaseUpdateEpochAdaptive]
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (Quantum.AdaptiveCircuit.WellFormed.seq
      (phaseUpdateEpochForwardTestsAdaptive_wellFormed
        registers shiftEpoch hlayout)
      ⟨phaseUpdateCore_wellFormed
        (registers.withShiftEpoch shiftEpoch) hlayout, trivial⟩)
    (phaseUpdateEpochCleanupTestsAdaptive_wellFormed
      registers shiftEpoch hlayout)

@[simp]
theorem phaseUpdateEpochAdaptive_measurementCount
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    (phaseUpdateEpochAdaptive registers shiftEpoch).measurementCount =
      2 * (mcxVChainMeasurementCost registers.lengthQ.length +
        mcxVChainMeasurementCost registers.lengthRPrime.length +
        mcxVChainMeasurementCost (registers.lengthS.length + 1)) := by
  have hq := mcxVChainAdaptive_measurementCount registers.lengthQ
    registers.zeroQ registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.q_capacity)
  have hr := mcxVChainAdaptive_measurementCount registers.lengthRPrime
    registers.zeroRPrime registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.rPrime_capacity)
  have hs := mcxVChainAdaptive_measurementCount
    (registers.lengthS ++ [shiftEpoch]) registers.zeroS
    registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.s_capacity)
  simp only [phaseUpdateEpochAdaptive,
    phaseUpdateEpochForwardTestsAdaptive,
    phaseUpdateEpochCleanupTestsAdaptive,
    phaseUpdateAdaptive_measurementCount_seq,
    PhaseUpdateRegisters.withShiftEpoch, hq, hr, hs,
    List.length_append, List.length_singleton]
  simp [Quantum.AdaptiveCircuit.measurementCount]
  omega

@[simp]
theorem phaseUpdateEpochAdaptive_tCount
    (registers : PhaseUpdateRegisters) (shiftEpoch : Wire)
    (hlayout : PhaseUpdateEpochLayout registers shiftEpoch) :
    (phaseUpdateEpochAdaptive registers shiftEpoch).tCount =
      7 * (2 * (mcxVChainAdaptiveToffoliCost registers.lengthQ.length +
        mcxVChainAdaptiveToffoliCost registers.lengthRPrime.length +
        mcxVChainAdaptiveToffoliCost (registers.lengthS.length + 1)) + 4) := by
  have hq := mcxVChainAdaptive_tCount registers.lengthQ registers.zeroQ
    registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.q_capacity)
  have hr := mcxVChainAdaptive_tCount registers.lengthRPrime registers.zeroRPrime
    registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.rPrime_capacity)
  have hs := mcxVChainAdaptive_tCount (registers.lengthS ++ [shiftEpoch])
    registers.zeroS registers.equalityScratch (by
      simpa [PhaseUpdateRegisters.withShiftEpoch] using hlayout.s_capacity)
  simp only [phaseUpdateEpochAdaptive,
    phaseUpdateEpochForwardTestsAdaptive,
    phaseUpdateEpochCleanupTestsAdaptive,
    phaseUpdateAdaptive_tCount_seq,
    PhaseUpdateRegisters.withShiftEpoch, hq, hr, hs,
    List.length_append, List.length_singleton]
  simp [Quantum.AdaptiveCircuit.tCount, phaseUpdateCore,
    ShorECDLP.tCount, ShorECDLP.tCost]
  omega

/-! ## Pinned-source regressions -/

private def phaseUpdateSmallRegisters : PhaseUpdateRegisters where
  phase1 := 0
  phase2 := 1
  sign := 2
  lengthQ := [3, 4, 5]
  lengthRPrime := [6, 7, 8]
  lengthS := [9, 10, 11, 12]
  zeroQ := 14
  zeroRPrime := 15
  zeroS := 16
  condition := 17
  temporary := 18
  equalityScratch := [19, 20, 21]

private theorem phaseUpdateSmallLayout :
    PhaseUpdateEpochLayout phaseUpdateSmallRegisters 13 := by
  refine ⟨rfl,
    by norm_num [PhaseUpdateRegisters.withShiftEpoch, phaseUpdateSmallRegisters],
    by norm_num [PhaseUpdateRegisters.withShiftEpoch, phaseUpdateSmallRegisters],
    by norm_num [PhaseUpdateRegisters.withShiftEpoch, phaseUpdateSmallRegisters], ?_⟩
  norm_num [
    PhaseUpdateRegisters.withShiftEpoch,
    PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scratch,
    phaseUpdateSmallRegisters]

/-- Exact flattened `len_width = 3`, `shift_width = 4`, epoch-aware gate stream emitted by pinned
supplement commit `e64aa3c`.  This catches register-order and conjugation drift, not merely counts. -/
theorem phaseUpdateEpochUnitary_source_regression :
    phaseUpdateEpochUnitary phaseUpdateSmallRegisters 13 =
      [.CCX 3 4 19, .CCX 5 19 14, .CCX 3 4 19,
       .CCX 6 7 19, .CCX 8 19 15, .CCX 6 7 19,
       .X 13,
       .CCX 9 10 19, .CCX 11 19 20, .CCX 12 20 21,
       .CCX 13 21 16, .CCX 12 20 21, .CCX 11 19 20,
       .CCX 9 10 19, .X 13,
       .X 15, .CCX 14 15 17, .X 15,
       .CX 2 18, .CX 0 18, .CCX 17 18 1,
       .CX 0 18, .CX 2 18, .CCX 17 1 2,
       .X 15, .CCX 14 15 17, .X 15,
       .CX 16 0, .CX 16 1,
       .X 13,
       .CCX 9 10 19, .CCX 11 19 20, .CCX 12 20 21,
       .CCX 13 21 16, .CCX 12 20 21, .CCX 11 19 20,
       .CCX 9 10 19, .X 13,
       .CCX 6 7 19, .CCX 8 19 15, .CCX 6 7 19,
       .CCX 3 4 19, .CCX 5 19 14, .CCX 3 4 19] := by
  rfl

theorem phaseUpdateEpochUnitary_small_resources :
    eeaToffoliCount
          (phaseUpdateEpochUnitary phaseUpdateSmallRegisters 13) = 30 ∧
      eeaCnotCount
          (phaseUpdateEpochUnitary phaseUpdateSmallRegisters 13) = 6 ∧
      ShorECDLP.tCount
          (phaseUpdateEpochUnitary phaseUpdateSmallRegisters 13) = 210 := by
  rw [phaseUpdateEpochUnitary_toffoliCount _ _ phaseUpdateSmallLayout,
    phaseUpdateEpochUnitary_cnotCount,
    phaseUpdateEpochUnitary_tCount _ _ phaseUpdateSmallLayout]
  norm_num [phaseUpdateSmallRegisters, mcxVChainToffoliCost,
    mcxVChainCnotCost]

theorem phaseUpdateEpochAdaptive_small_resources :
    (phaseUpdateEpochAdaptive phaseUpdateSmallRegisters 13).measurementCount = 10 ∧
      (phaseUpdateEpochAdaptive phaseUpdateSmallRegisters 13).tCount = 140 := by
  rw [phaseUpdateEpochAdaptive_measurementCount _ _ phaseUpdateSmallLayout,
    phaseUpdateEpochAdaptive_tCount _ _ phaseUpdateSmallLayout]
  norm_num [phaseUpdateSmallRegisters, mcxVChainMeasurementCost,
    mcxVChainAdaptiveToffoliCost]

private def phaseUpdateSecp256k1Registers : PhaseUpdateRegisters where
  phase1 := 0
  phase2 := 1
  sign := 2
  lengthQ := List.range' 3 9
  lengthRPrime := List.range' 12 9
  lengthS := List.range' 21 9
  zeroQ := 31
  zeroRPrime := 32
  zeroS := 33
  condition := 34
  temporary := 35
  equalityScratch := List.range' 36 8

private theorem phaseUpdateSecp256k1Layout :
    PhaseUpdateEpochLayout phaseUpdateSecp256k1Registers 30 := by
  refine ⟨rfl,
    by norm_num [PhaseUpdateRegisters.withShiftEpoch,
      phaseUpdateSecp256k1Registers, List.range'],
    by norm_num [PhaseUpdateRegisters.withShiftEpoch,
      phaseUpdateSecp256k1Registers, List.range'],
    by norm_num [PhaseUpdateRegisters.withShiftEpoch,
      phaseUpdateSecp256k1Registers, List.range'], ?_⟩
  norm_num [
    PhaseUpdateRegisters.withShiftEpoch,
    PhaseUpdateRegisters.allWires, PhaseUpdateRegisters.scratch,
    phaseUpdateSecp256k1Registers, List.range']

/-- Production-width source regression: 44 wires, 98 coherent Toffolis, six CNOTs, and 686 T. -/
theorem phaseUpdateEpochUnitary_secp256k1_resources :
    (phaseUpdateSecp256k1Registers.epochWires 30).length = 44 ∧
      eeaToffoliCount
          (phaseUpdateEpochUnitary phaseUpdateSecp256k1Registers 30) = 98 ∧
      eeaCnotCount
          (phaseUpdateEpochUnitary phaseUpdateSecp256k1Registers 30) = 6 ∧
      ShorECDLP.tCount
          (phaseUpdateEpochUnitary phaseUpdateSecp256k1Registers 30) = 686 := by
  rw [phaseUpdateEpochUnitary_toffoliCount _ _
      phaseUpdateSecp256k1Layout,
    phaseUpdateEpochUnitary_cnotCount,
    phaseUpdateEpochUnitary_tCount _ _ phaseUpdateSecp256k1Layout]
  norm_num [PhaseUpdateRegisters.epochWires,
    PhaseUpdateRegisters.withShiftEpoch, PhaseUpdateRegisters.allWires,
    PhaseUpdateRegisters.scratch, phaseUpdateSecp256k1Registers,
    List.range', mcxVChainToffoliCost, mcxVChainCnotCost]

/-- Production measurement-uncomputation regression from the same 9/9/9-bit source instance. -/
theorem phaseUpdateEpochAdaptive_secp256k1_resources :
    (phaseUpdateEpochAdaptive phaseUpdateSecp256k1Registers 30).measurementCount = 44 ∧
      (phaseUpdateEpochAdaptive phaseUpdateSecp256k1Registers 30).tCount = 378 := by
  rw [phaseUpdateEpochAdaptive_measurementCount _ _
      phaseUpdateSecp256k1Layout,
    phaseUpdateEpochAdaptive_tCount _ _ phaseUpdateSecp256k1Layout]
  norm_num [phaseUpdateSecp256k1Registers,
    mcxVChainMeasurementCost, mcxVChainAdaptiveToffoliCost]
