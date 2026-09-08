import ShorECDLP.Submission.«2607_13816».Arithmetic.Square

/-!
# Symbolic quadratic resource growth

These formulas count the actual adaptive modular circuits at arbitrary widths.
The odd correction has its low bit set; at least two data bits are required for
the uniform `3n - 4` constant-adder formula.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

private theorem growth_constant_add (a b d : Wire) (rest input : List Wire) (constant : List Bool)
    (q c r t : Wire) (hlen : (d :: input).length = (a :: b :: rest).length)
    (hk : (a :: b :: rest).length = (true :: constant).length) :
    gidneyToffoliCount (controlledGidneyAddConst (a :: b :: rest)
      ((d :: input).take ((a :: b :: rest).length - 1)) (true :: constant) q c r t) =
      3 * (a :: b :: rest).length - 4 := by
  have hd : (b :: rest).length = (input.take rest.length).length + 1 := by
    simp only [List.length_cons,List.length_take] at hlen ⊢
    rw [Nat.min_eq_left (by omega)]
  exact controlledGidneyAddConst_toffoli_exact a d q c r t (b :: rest) (input.take rest.length) constant
    (by simpa using hk) hd

/-- At width `n ≥ 2`, the actual four-stage modular adder has `11n - 3` CCX gates. -/
theorem controlledModularAdd_toffoli_exact (a b d : Wire) (rest input : List Wire)
    (constant : List Bool) (p : Nat) (q c r t f : Wire)
    (hlen : (d :: input).length = (a :: b :: rest).length)
    (hk : (a :: b :: rest).length = (true :: constant).length)
    (hp0 : 0 < p) (hp : p < 2 ^ (a :: b :: rest).length) :
    gidneyToffoliCount (controlledModularAdd (d :: input) (a :: b :: rest) (true :: constant) p q c r t f) =
      11 * (a :: b :: rest).length - 3 := by
  have hfirst := controlledAddCarry_toffoliCount (d :: input) (a :: b :: rest) q c f hlen
  have hge := gidneyCompareGE_toffoli_exact a (b :: rest) (d :: input) p c r t f hlen.symm hp0 hp
  have hadd := growth_constant_add a b d rest input constant f c r t hlen hk
  have hlast := (controlledCompareLT_counts a (b :: rest) (d :: input) q c f hlen.symm).1
  unfold controlledModularAdd
  apply (doublingFour_counts _ _ _ _).1.trans
  rw [hfirst,hge,hadd,hlast]
  simp only [List.length_cons] at hlen ⊢
  omega

/-- At width `n ≥ 2`, modular doubling uses `6n - 5` CCX gates. -/
theorem modularDouble_toffoli_exact (a b d : Wire) (rest input : List Wire)
    (constant : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : (d :: input).length = (a :: b :: rest).length)
    (hk : (a :: b :: rest).length = (true :: constant).length)
    (hp0 : 0 < p) (hp : p < 2 ^ (a :: b :: rest).length) :
    gidneyToffoliCount (modularDouble (a :: b :: rest) (d :: input) (true :: constant) p c r t f) =
      6 * (a :: b :: rest).length - 5 := by
  have hfirst := (doublingShift_counts a f (b :: rest)).1
  have hge := gidneyCompareGE_toffoli_exact a (b :: rest) (d :: input) p c r t f hlen.symm hp0 hp
  have hadd := growth_constant_add a b d rest input constant f c r t hlen hk
  unfold modularDouble
  dsimp only
  apply (doublingFour_counts _ _ _ _).1.trans
  rw [hfirst,hge]
  change 0 + (3 * (a :: b :: rest).length - 1 +
    (gidneyToffoliCount (controlledGidneyAddConst (a :: b :: rest)
      ((d :: input).take ((a :: b :: rest).length-1)) (true :: constant) f c r t) + 0)) = _
  rw [hadd]
  simp only [List.length_cons]
  omega

private theorem growth_copy_count (q copied : Wire) (g : Quantum.AdaptiveCircuit) :
    gidneyToffoliCount (.unitary [.CX q copied] (g.seq (.unitary [.CX q copied] .done))) = gidneyToffoliCount g := by
  have h := (doublingFour_counts ([.CX q copied] : Circuit) ([.CX q copied] : Circuit) g .done).1
  simpa only [Quantum.AdaptiveCircuit.seq,
    show eeaToffoliCount [.CX q copied] = 0 from rfl,
    show gidneyToffoliCount .done = 0 from rfl,Nat.add_zero,Nat.zero_add] using h

private theorem growth_loops (controls : List Wire) (a b d : Wire) (rest input : List Wire)
    (constant : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : (d :: input).length = (a :: b :: rest).length)
    (hk : (a :: b :: rest).length = (true :: constant).length)
    (hp0 : 0 < p) (hp : p < 2 ^ (a :: b :: rest).length) :
    let n := (a :: b :: rest).length
    let cost := controls.length * (11*n-3) + (controls.length-1) * (6*n-5)
    gidneyToffoliCount (hornerMul controls (d :: input) (a :: b :: rest) (true :: constant) p c r t f) = cost ∧
    gidneyToffoliCount (squareLoop controls (d :: input) (a :: b :: rest) (true :: constant) p copied c r t f) = cost := by
  have hseq (g h : Quantum.AdaptiveCircuit) : gidneyToffoliCount (g.seq h) =
      gidneyToffoliCount g + gidneyToffoliCount h := modularGateCount_seq _ g h
  induction controls with
  | nil => simp [hornerMul,squareLoop,gidneyToffoliCount,gidneyGateCount]
  | cons q qs ih =>
    let n := (a :: b :: rest).length
    let A := 11*n-3
    let D := 6*n-5
    have ha := controlledModularAdd_toffoli_exact a b d rest input constant p q c r t f hlen hk hp0 hp
    have hc := controlledModularAdd_toffoli_exact a b d rest input constant p copied c r t f hlen hk hp0 hp
    have hd := modularDouble_toffoli_exact a b d rest input constant p f r t c hlen hk hp0 hp
    have hs : gidneyToffoliCount (squareAdd (d :: input) (a :: b :: rest) (true :: constant) p q copied c r t f) = A :=
      (growth_copy_count q copied _).trans hc
    have hH : gidneyToffoliCount (hornerMul (q :: qs) (d :: input) (a :: b :: rest) (true :: constant) p c r t f) =
        (qs.length*A+(qs.length-1)*D) + if qs = [] then A else D+A := by
      rw [hornerMul,hseq,ih.1]
      split <;> rename_i hz
      · rw [ha]
      · rw [hseq,hd,ha]
    have hS : gidneyToffoliCount (squareLoop (q :: qs) (d :: input) (a :: b :: rest) (true :: constant) p copied c r t f) =
        (qs.length*A+(qs.length-1)*D) + if qs = [] then A else D+A := by
      rw [squareLoop,hseq,ih.2]
      split <;> rename_i hz
      · rw [hs]
      · rw [hseq,hd,hs]
    have hstep : (qs.length*A+(qs.length-1)*D) + (if qs = [] then A else D+A) =
        (q :: qs).length*A+((q :: qs).length-1)*D := by
      cases qs with
      | nil => simp
      | cons x xs => simp [Nat.add_mul]; omega
    exact ⟨hH.trans hstep,hS.trans hstep⟩

private theorem growth_polynomial (n : Nat) (hn : 2 ≤ n) :
    n*(11*n-3)+(n-1)*(6*n-5) = 17*n^2-14*n+5 := by
  have hA : 3 ≤ 11*n := by omega
  have hD : 5 ≤ 6*n := by omega
  have hN : 1 ≤ n := by omega
  have hP : 14*n ≤ 17*n^2 := by nlinarith
  have ha := congrArg (fun v => n*v) (Nat.sub_add_cancel hA)
  have hd := congrArg (fun v => (n-1)*v) (Nat.sub_add_cancel hD)
  have hm := congrArg (fun v => (6*n)*v) (Nat.sub_add_cancel hN)
  have hp := Nat.sub_add_cancel hP
  nlinarith

/-- The literal width-`n` multiplier has the paper's quadratic Toffoli count,
including its exact linear correction. No separate resource model is assumed. -/
theorem hornerMul_toffoli_exact (controls : List Wire) (a b d : Wire) (rest input : List Wire)
    (constant : List Bool) (p : Nat) (c r t f : Wire)
    (hcontrols : controls.length = (a :: b :: rest).length)
    (hlen : (d :: input).length = (a :: b :: rest).length)
    (hk : (a :: b :: rest).length = (true :: constant).length)
    (hp0 : 0 < p) (hp : p < 2 ^ (a :: b :: rest).length) :
    let n := (a :: b :: rest).length
    gidneyToffoliCount (hornerMul controls (d :: input) (a :: b :: rest) (true :: constant) p c r t f) =
      17*n^2-14*n+5 := by
  have h := (growth_loops controls a b d rest input constant p c c r t f hlen hk hp0 hp).1
  rw [hcontrols] at h
  exact h.trans (growth_polynomial _ (by simp))

/-- Copying controls adds no Toffoli gates, so the actual squaring circuit has
the same exact quadratic polynomial as multiplication. -/
theorem squareLoop_toffoli_exact (controls : List Wire) (a b d : Wire) (rest input : List Wire)
    (constant : List Bool) (p : Nat) (copied c r t f : Wire)
    (hcontrols : controls.length = (a :: b :: rest).length)
    (hlen : (d :: input).length = (a :: b :: rest).length)
    (hk : (a :: b :: rest).length = (true :: constant).length)
    (hp0 : 0 < p) (hp : p < 2 ^ (a :: b :: rest).length) :
    let n := (a :: b :: rest).length
    gidneyToffoliCount (squareLoop controls (d :: input) (a :: b :: rest) (true :: constant) p copied c r t f) =
      17*n^2-14*n+5 := by
  have h := (growth_loops controls a b d rest input constant p copied c r t f hlen hk hp0 hp).2
  rw [hcontrols] at h
  exact h.trans (growth_polynomial _ (by simp))

end ShorECDLP.Paper2607_13816
