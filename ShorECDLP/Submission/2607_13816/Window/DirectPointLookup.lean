import ShorECDLP.Submission.«2607_13816».Window.PointInitialize
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

def pointTableMask (table : Nat → Point) (i : Nat) : List Wire :=
  tableBitsMask pointLogicalWires (pointCoordinateWord (fig14PointEncoding (table i)))

def directPointLookup (table : Nat → Point) (bits paths : List Wire) (q : Wire) : AdaptiveCircuit :=
  tableLookupProgram (pointTableMask table) bits q paths

private theorem mask_subset (table : Nat → Point) (i : Nat) :
    pointTableMask table i ⊆ pointLogicalWires := tableBitsMask_subset _ _

private theorem mask_nodup (table : Nat → Point) (i : Nat) :
    (pointTableMask table i).Nodup := tableBitsMask_nodup _ _ pointLogicalWires_nodup

private theorem mask_load (table : Nat → Point) (i : Nat) (s : BasisState)
    (hs : Clean pointLogicalWires s) :
    tableXorState (pointTableMask table i) true s=pointWrite (table i) s := by
  have hw := tableBitsMask_read pointLogicalWires
    (pointCoordinateWord (fig14PointEncoding (table i))) s pointLogicalWires_nodup
    (by simp [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,pointCoordinateWord]) hs
  funext w
  by_cases hm : w∈pointLogicalWires
  · exact List.map_inj_left.mp (hw.trans (pointWrite_word (table i) s).symm) w hm
  · exact (tableXorState_outside _ _ _ w (fun h => hm (mask_subset table i h))).trans
      (pointWrite_frame (table i) s w hm).symm

def DirectPointLookupValid (paths : List Wire) (q : Wire) (s : BasisState) : Prop :=
  Clean paths s ∧ Clean pointLogicalWires s ∧ s q=true

theorem directPointLookup_coherent (table : Nat → Point) (bits paths : List Wire) (q : Wire)
    (hl : bits.length≤paths.length) (hn : (q::bits++paths).Nodup)
    (hd : (q::bits++paths).Disjoint pointLogicalWires) :
    CoherentlyImplementsOn (directPointLookup table bits paths q)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (table (tableAddressValue bits s)) s))
      (DirectPointLookupValid paths q) := by
  have hc := tableLookupProgram_coherent_state (pointTableMask table) bits paths q hl hn
    (mask_nodup table) (by
      intro i w hw hm
      exact List.disjoint_left.mp hd hw (mask_subset table i hm))
  obtain ⟨cs,hcs,hcm⟩ := hc
  have hrestricted : CoherentlyImplementsOn (directPointLookup table bits paths q)
      (Finsupp.lmapDomain ℂ ℂ (tableLookupState (pointTableMask table) bits q))
      (DirectPointLookupValid paths q) :=
    ⟨cs,hcs.imp (fun b c hb s hs => hb s hs.1),hcm⟩
  apply hrestricted.congrIdeal
  intro s hs
  have he : tableLookupState (pointTableMask table) bits q s=
      pointWrite (table (tableAddressValue bits s)) s := by
    rw [tableLookupState,hs.2.2,mask_load table _ s hs.2.1]
  simp [ket,he]

theorem directPointLookup_support (table : Nat → Point) (bits paths : List Wire) (q : Wire) :
    (directPointLookup table bits paths q).wires ⊆ q::bits++paths++pointLogicalWires :=
  tableLookupProgram_support _ _ _ _ _ (mask_subset table)

theorem directPointLookup_tCount (table : Nat → Point) (bits paths : List Wire) (q : Wire)
    (hl : bits.length≤paths.length) (hn : (q::bits++paths).Nodup) :
    (directPointLookup table bits paths q).tCount=7*(2^bits.length-1) :=
  tableLookupProgram_tCount _ _ _ _ hl hn

theorem directPointLookup_measurementCount (table : Nat → Point) (bits paths : List Wire) (q : Wire)
    (hl : bits.length≤paths.length) (hn : (q::bits++paths).Nodup) :
    (directPointLookup table bits paths q).measurementCount=2^bits.length-1 :=
  tableLookupProgram_measurementCount _ _ _ _ hl hn

/-- Direct first-point initialization on the physical 16-bit address and path banks. -/
def physicalPointLookup (table : Nat → Point) : AdaptiveCircuit :=
  directPointLookup table (List.range' 855 16) (List.range' 519 16) 836

theorem physicalPointLookup_coherent (table : Nat → Point) :
    CoherentlyImplementsOn (physicalPointLookup table)
      (Finsupp.lmapDomain ℂ ℂ (fun s =>
        pointWrite (table (tableAddressValue (List.range' 855 16) s)) s))
      (DirectPointLookupValid (List.range' 519 16) 836) :=
  directPointLookup_coherent table _ _ _ (by decide +kernel) (by decide +kernel)
    (by
      apply List.disjoint_left.mpr
      intro w hw hp
      simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hw
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hp
      dsimp only [Wire] at *
      omega)

theorem physicalPointLookup_resources (table : Nat → Point) :
    (physicalPointLookup table).tCount=458745 ∧
    (physicalPointLookup table).measurementCount=65535 ∧
    (physicalPointLookup table).qubitCount≤546 := by
  constructor
  · exact directPointLookup_tCount table _ _ _ (by decide +kernel) (by decide +kernel)
  constructor
  · exact directPointLookup_measurementCount table _ _ _ (by decide +kernel) (by decide +kernel)
  · have h := tableLookupProgram_qubitCount (pointTableMask table) (List.range' 855 16)
      (List.range' 519 16) pointLogicalWires 836 (mask_subset table)
    simpa only [List.length_range',pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
      List.length_append,List.length_cons,List.length_nil] using h

end
end ShorECDLP.Paper2607_13816
