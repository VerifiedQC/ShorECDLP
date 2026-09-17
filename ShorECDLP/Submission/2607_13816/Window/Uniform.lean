import ShorECDLP.Submission.«2607_13816».Window.Outcomes
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Assign a little-endian physical input bit string, preserving all other wires. -/
def phaseWordState : List Wire → List Bool → BasisState → BasisState
  | w::ws,b::bs,s => phaseWordState ws bs (s[w ↦ b])
  | _,_,s => s

theorem phaseWordState_frame (ws : List Wire) (bs : List Bool) (s : BasisState)
    (q : Wire) (hq : q∉ws) : phaseWordState ws bs s q=s q := by
  induction ws generalizing bs s with
  | nil => rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      rw [phaseWordState,ih bs _ (by intro h; exact hq (List.mem_cons_of_mem _ h))]
      exact upd_other _ _ _ (by intro h; subst q; exact hq List.mem_cons_self)

theorem phaseWordState_word (ws : List Wire) (hn : ws.Nodup) (bs : List Bool)
    (hlen : bs.length=ws.length) (s : BasisState) :
    wireValues ws (phaseWordState ws bs s)=bs := by
  induction ws generalizing bs s with
  | nil => have he : bs=[] := List.length_eq_zero_iff.mp hlen; subst bs; rfl
  | cons w ws ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hn' := List.nodup_cons.mp hn
      simp only [phaseWordState,wireValues,List.map_cons]
      rw [phaseWordState_frame ws bs _ w hn'.1,upd_same]
      congr 1
      exact ih hn'.2 bs (by simpa using hlen) _


theorem phaseWordState_append (ws vs : List Wire) (bs cs : List Bool)
    (hlen : bs.length=ws.length) (s : BasisState) :
    phaseWordState (ws++vs) (bs++cs) s=phaseWordState vs cs (phaseWordState ws bs s) := by
  induction ws generalizing bs s with
  | nil => have he : bs=[] := List.length_eq_zero_iff.mp hlen; subst bs; rfl
  | cons w ws ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simpa only [List.cons_append,phaseWordState] using ih bs (by simpa using hlen) (s[w ↦ b])


def phaseUniformSum (ws : List Wire) (s : BasisState) : State :=
  ((fourierOutcomes ws.length).map (fun bs => ket (phaseWordState ws bs s))).sum

theorem phaseHadamards_uniform (ws : List Wire) (hn : ws.Nodup) (s : BasisState)
    (hz : Clean ws s) : Quantum.run (ws.map Gate.H) (ket s)=
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^ws.length) • phaseUniformSum ws s := by
  induction ws generalizing s with
  | nil => simp [Quantum.run,phaseUniformSum,fourierOutcomes,phaseWordState]
  | cons w ws ih =>
    have hn' := List.nodup_cons.mp hn
    have hc (b : Bool) : Clean ws (s[w ↦ b]) := by
      intro q hq
      rw [upd_other _ _ _ (by intro he; subst q; exact hn'.1 hq)]
      exact hz q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons,Quantum.run_cons,Quantum.applyGate_H_ket,
      hz w List.mem_cons_self,Bool.false_eq_true,if_false,mul_one,map_add,map_smul]
    rw [ih hn'.2 _ (hc false),ih hn'.2 _ (hc true)]
    simp [phaseUniformSum,fourierOutcomes,List.map_map,Function.comp_def,phaseWordState,smul_add,smul_smul,pow_succ,mul_comm]

theorem scalarPhasePrepare_uniform : Quantum.run scalarPhasePrepare (ket zeroBasisState)=
    (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^514) • phaseUniformSum scalarPhaseWires zeroBasisState := by
  have hz := windowTrial_zero_initial.2
  have h := phaseHadamards_uniform scalarPhaseWires (by decide +kernel) zeroBasisState hz
  simpa only [scalarPhaseWires,List.length_append,List.length_range'] using h
theorem stateLinear_list_sum (L : State →ₗ[ℂ] State) (xs : List State) :
    L xs.sum=(xs.map L).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- An explicit finite amplitude sum, with interference retained inside each Fourier row. -/
theorem windowTrialOutputMass_uniform (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (a b : List Bool)
    (ha : a.length=257) (hb : b.length=257) :
    windowTrialOutputMass P Q hP hQ hrP hrQ a b=
      normSq ((((((Real.sqrt 2)⁻¹:ℝ):ℂ))^514) •
        (((fourierOutcomes 514).map (fun bits =>
          measuredFourierKernel .inverse scalarFourierRight b
            (measuredFourierKernel .inverse scalarFourierLeft a
              (ket (scalarRegisterOutput P Q (phaseWordState scalarPhaseWires bits zeroBasisState)))))).sum)) := by
  rw [windowTrialOutputMass_kernel P Q hP hQ hrP hrQ a b ha hb,scalarPhasePrepare_uniform]
  simp only [map_smul,phaseUniformSum,stateLinear_list_sum,List.map_map]
  apply congrArg normSq
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^514) • ψ)
  have hl : scalarPhaseWires.length=514 := by
    simp only [scalarPhaseWires,List.length_append,List.length_range']
  rw [hl]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bits _
  simp [Function.comp_def,ket]

private theorem outcomes_add (n m : Nat) : fourierOutcomes (n+m)=
    (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a++b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add,fourierOutcomes,ih,List.flatMap_append,List.flatMap_map,
      List.map_flatMap,List.map_map,Function.comp_def,List.cons_append]

private theorem sum_flatMap {α : Type} (xs : List α) (f : α → List State) :
    (xs.flatMap f).sum=(xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem phaseUniformSum_append (ws vs : List Wire) (s : BasisState) :
    phaseUniformSum (ws++vs) s =
      ((fourierOutcomes ws.length).map (fun bs => phaseUniformSum vs (phaseWordState ws bs s))).sum := by
  simp only [phaseUniformSum,List.length_append,outcomes_add,List.map_flatMap,List.map_map,
    sum_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bs hbs
  apply congrArg List.sum
  apply List.map_congr_left
  intro cs _
  simp only [Function.comp_apply,phaseWordState_append ws vs bs cs ((fourierOutcomes_mem _ _).mp hbs)]

/-- The two input registers receive their actual emitted assignment words. -/
theorem scalarPhaseWord_inputs (a b : List Bool) (ha : a.length=257) (hb : b.length=257)
    (s : BasisState) :
    scalarInputValue 0 (phaseWordState scalarPhaseWires (a++b) s)=boolWordToNat a ∧
    scalarInputValue 17 (phaseWordState scalarPhaseWires (a++b) s)=boolWordToNat b := by
  have hsplit := phaseWordState_append (List.range' 855 257) (List.range' 1127 257) a b
    (by simpa using ha) s
  change phaseWordState scalarPhaseWires (a++b) s=_ at hsplit
  rw [hsplit]
  have hleft : wireValues (List.range' 855 257)
      (phaseWordState (List.range' 1127 257) b (phaseWordState (List.range' 855 257) a s))=a := by
    calc
      _ = wireValues (List.range' 855 257) (phaseWordState (List.range' 855 257) a s) := by
        apply List.map_congr_left
        intro w hw
        apply phaseWordState_frame
        simp only [List.mem_range'_1] at hw ⊢
        omega
      _ = a := phaseWordState_word _ (List.nodup_range') a (by simpa using ha) s
  have hright := phaseWordState_word (List.range' 1127 257) (List.nodup_range') b
    (by simpa using hb) (phaseWordState (List.range' 855 257) a s)
  constructor
  · change boolWordToNat (wireValues (List.range' 855 257) _)=_
    rw [hleft]
  · change boolWordToNat (wireValues (List.range' 1127 257) _)=_
    rw [hright]

end
end ShorECDLP.Paper2607_13816
