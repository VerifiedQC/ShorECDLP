import ShorECDLP.Submission.«2607_13816».Challenge.ModularPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem squareAddProgram_wellFormed (n start : Nat) (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=bits.length) (hnd : ([copied,c,r,t,f]++input++acc).Nodup)
    (hq : q∈input) : (squareAddProgram n start input acc bits p q copied c r t f).2.WellFormed := by
  have hqc : q≠copied := by
    intro he
    exact (List.nodup_cons.mp hnd).1 (by simp [← he,hq])
  have hg : CircuitWellFormed [.CX q copied] := by simp [CircuitWellFormed,Gate.WellFormed,hqc]
  exact prependCompiled_wellFormed _ _ hg
    (appendCompiled_wellFormed _ _
      (modularAddProgram_wellFormed n start input acc bits p copied c r t f hlen hne hk hnd)
      (literalProgram_wellFormed _ hg))

theorem squareSubProgram_wellFormed (n start : Nat) (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=bits.length) (hnd : ([copied,c,r,t,f]++input++acc).Nodup)
    (hq : q∈input) : (squareSubProgram n start input acc bits p q copied c r t f).2.WellFormed := by
  have hqc : q≠copied := by
    intro he
    exact (List.nodup_cons.mp hnd).1 (by simp [← he,hq])
  have hg : CircuitWellFormed [.CX q copied] := by simp [CircuitWellFormed,Gate.WellFormed,hqc]
  exact prependCompiled_wellFormed _ _ hg
    (appendCompiled_wellFormed _ _
      (modularSubProgram_wellFormed n start input acc bits p copied c r t f hlen hne hk hnd)
      (literalProgram_wellFormed _ hg))

attribute [local irreducible] squareAddProgram squareSubProgram

theorem squareProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcontrols : ∀ q∈controls,q∈input) :
    (squareProgram n start controls input (a::rest) bits p copied c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [squareProgram]
    apply appendCompiled_wellFormed
    · exact ih _ (fun z hz => hcontrols z (List.mem_cons_of_mem q hz))
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(squareProgram n start qs input (a::rest) bits p copied c r t f).1)
          (start+(squareProgram n start qs input (a::rest) bits p copied c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · exact squareAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
          hnd (hcontrols q (by simp))
      · apply appendCompiled_wellFormed
        · exact modularDoubleProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout [] input (a::rest) c r t f (List.nodup_cons.mp hnd).2)
        · exact squareAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
            hnd (hcontrols q (by simp))

theorem squareInverseProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcontrols : ∀ q∈controls,q∈input) :
    (squareInverseProgram n start controls input (a::rest) bits p copied c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [squareInverseProgram]
    apply appendCompiled_wellFormed
    · exact squareSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
        hnd (hcontrols q (by simp))
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(squareSubProgram n start input (a::rest) bits p q copied c r t f).1)
          (start+(squareSubProgram n start input (a::rest) bits p q copied c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · trivial
      · apply appendCompiled_wellFormed
        · exact modularHalveProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout [] input (a::rest) c r t f (List.nodup_cons.mp hnd).2)
        · exact ih _ (fun z hz => hcontrols z (List.mem_cons_of_mem q hz))
attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_wellFormed (n start : Nat) (x y : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire)
    (hxlen : x.length=(a::rest).length) (hylen : y.length=(a::rest).length)
    (hk : (a::rest).length=correction.length) (hm : (a::rest).length=modulus.length)
    (hsq : ([copied,c,r,t,f]++y++(a::rest)).Nodup)
    (hsub : ([q,copied,f,r,c]++(a::rest)++x).Nodup) :
    (squareSubtractProgram n start x y (a::rest) correction modulus p q copied c r t f).2.WellFormed := by
  unfold squareSubtractProgram
  apply appendCompiled_wellFormed
  · exact squareProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hylen hk hsq (fun _ h => h)
  · apply appendCompiled_wellFormed
    · exact modularSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hxlen.symm
        (by rw [hxlen]; simp) (hxlen.trans hm) hsub
    · exact squareInverseProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hylen hm hsq (fun _ h => h)

end ShorECDLP.Paper2607_13816.ChallengeMigration
