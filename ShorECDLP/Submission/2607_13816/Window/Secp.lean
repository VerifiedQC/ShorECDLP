import ShorECDLP.Submission.«2607_13816».Window.Success
import ShorECDLP.Math.EllipticCurve.GeneratorOrder
import Mathlib.Analysis.Real.Pi.Bounds
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
theorem secpGenerator_ne_zero : G≠0 := by
  intro h
  have hg := generator_order
  rw [h,addOrderOf_zero] at hg
  have hp := order_prime.two_le
  omega
private theorem order_precision : order<2^257 := by decide +kernel
/-- The zero public point is solved classically with output zero modulo the subgroup order. -/
theorem secpWindow_zero_input (d : Nat) (h : d • G=0) : (d : ZMod order)=0 := by
  have hd : order ∣ d := by
    rw [←generator_order]
    exact (addOrderOf_dvd_iff_nsmul_eq_zero).mpr h
  exact (CharP.cast_eq_zero_iff (ZMod order) order d).mpr hd
/-- The zero public point needs no quantum gates. -/
def secpWindowProgram (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit := by
  classical
  exact if hQ : Q=0 then .done else
    windowTrialProgram G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ
/-- Public-input classical postprocessing, including the zero-point case. -/
def secpWindowPostprocess (Q : Point) (out : Fin (2^257) × Fin (2^257)) : Option (ZMod order) := by
  classical
  exact if Q=0 then some 0 else orderFindingPostprocess order 257 order_prime out
/-- Distribution of decoded output pairs; zero input uses the deterministic pair (0,0). -/
def secpWindowOutputMass (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^257) × Fin (2^257)) : ℝ := by
  classical
  exact if hQ : Q=0 then if out=(0,0) then 1 else 0 else
    windowTrialFiniteOutputMass G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ out
/-- Success event of the public-input program and its classical postprocessor. -/
def secpWindowSuccessMass (Q : Point) (hrQ : order • Q=0) (d : Nat) : ℝ :=
  ∑ out : Fin (2^257) × Fin (2^257),
    if secpWindowPostprocess Q out=some (d:ZMod order) then secpWindowOutputMass Q hrQ out else 0

theorem secpWindow_zero_success (Q : Point) (hrQ : order • Q=0) (hQ : Q=0)
    (d : Nat) (hQd : Q=d • G) : secpWindowSuccessMass Q hrQ d=1 := by
  have hd := secpWindow_zero_input d (hQd.symm.trans hQ)
  simp only [secpWindowSuccessMass,secpWindowPostprocess,secpWindowOutputMass,hd,
    dif_pos hQ,if_pos hQ,ite_true,Finset.sum_ite_eq',Finset.mem_univ]
theorem secpWindow_nonzero_success (Q : Point) (hQ : Q≠0) (hrQ : order • Q=0) (d : Nat) :
    secpWindowSuccessMass Q hrQ d=
      windowTrialSuccessMass order order_prime G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ d := by
  simp only [secpWindowSuccessMass,secpWindowPostprocess,secpWindowOutputMass,if_neg hQ,dif_neg hQ,
    windowTrialSuccessMass]
theorem secpWindowProgram_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (secpWindowProgram Q hrQ).qubitCount≤1383 := by
  by_cases hQ : Q=0
  · simp [secpWindowProgram,hQ,AdaptiveCircuit.qubitCount,AdaptiveCircuit.wires]
  · simpa only [secpWindowProgram,dif_neg hQ] using
      windowTrialProgram_qubitCount G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ
theorem secpWindowProgram_zero (hrQ : order • (0:Point)=0) : secpWindowProgram 0 hrQ=.done := by
  simp [secpWindowProgram]
theorem secpWindowProgram_nonzero (Q : Point) (hrQ : order • Q=0) (hQ : Q≠0) :
    secpWindowProgram Q hrQ=windowTrialProgram G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ := by
  simp only [secpWindowProgram,dif_neg hQ]
theorem secpWindowOutputMass_total (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    ∑ out : Fin (2^257) × Fin (2^257), secpWindowOutputMass Q hrQ out=1 := by
  by_cases hQ : Q=0
  · simp only [secpWindowOutputMass,dif_pos hQ,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · simp only [secpWindowOutputMass,dif_neg hQ]
    exact windowTrialFiniteOutputMass_total order_prime G Q secpGenerator_ne_zero hQ
      generator_nsmul_eq_zero hrQ generator_order d hQd
theorem secpSuccessBound_le_one :
    (((order-1:Nat):ℝ)/(order:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ 1 := by
  have ho : (0:ℝ)<order := by exact_mod_cast order_prime.pos
  have hratio : (0:ℝ)≤((order-1:Nat):ℝ)/(order:ℝ) := by positivity
  have hratio1 : ((order-1:Nat):ℝ)/(order:ℝ)≤1 := by
    apply (div_le_one ho).mpr
    exact_mod_cast Nat.sub_le order 1
  have hpi := Real.pi_gt_three
  have hpi2 : (4:ℝ)≤Real.pi^2 := by nlinarith
  have hpipos : (0:ℝ)<Real.pi^2 := by positivity
  have hf : (4:ℝ)/Real.pi^2≤1 := (div_le_one hpipos).mpr hpi2
  have hfn : (0:ℝ)≤4/Real.pi^2 := by positivity
  have hf2 : ((4:ℝ)/Real.pi^2)^2≤1 := by nlinarith
  nlinarith
/-- The classical zero case and quantum nonzero case satisfy one concrete success bound. -/
theorem secpWindowSuccessMass_lower (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (((order-1:Nat):ℝ)/(order:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ secpWindowSuccessMass Q hrQ d := by
  by_cases hQ : Q=0
  · exact secpSuccessBound_le_one.trans_eq (secpWindow_zero_success Q hrQ hQ d hQd).symm
  · exact (windowTrialSuccessMass_lower order_prime G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ
      generator_order d hQd order_precision).trans_eq (secpWindow_nonzero_success Q hQ hrQ d).symm
/-- Decode the public-input program's actual transcript; the gate-free case emits the classical zero pair. -/
def secpWindowDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) := by
  classical
  exact if hQ : Q=0 then
    if hist=[] then some (paperOutcomeBits 257 0,paperOutcomeBits 257 0) else none
  else decodeWindowTrial G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ hist
theorem doneFiltered_mass (f : List Bool → Bool) :
    Instrument.bornMass (AdaptiveCircuit.done.run.filter (fun b => f b.history)) (ket zeroBasisState)=
      if f [] then 1 else 0 := by
  cases h : f [] <;> simp [AdaptiveCircuit.run,List.filter,Instrument.bornMass,h,normSq_ket]
theorem zeroOutcomeBits_pair (n m : Nat) (out : Fin (2^n) × Fin (2^m)) :
    (paperOutcomeBits n 0,paperOutcomeBits m 0)=(paperOutcomeBits n out.1,paperOutcomeBits m out.2) ↔
      out=(0,0) := by
  constructor
  · intro h
    have h1 := paperOutcomeBits_injective n (congrArg Prod.fst h)
    have h2 := paperOutcomeBits_injective m (congrArg Prod.snd h)
    exact Prod.ext h1.symm h2.symm
  · intro h
    rw [h]
/-- The distribution is obtained by filtering the actual public-input adaptive program. -/
theorem secpWindowOutputMass_physical (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^257) × Fin (2^257)) :
    Instrument.bornMass ((secpWindowProgram Q hrQ).run.filter
      (fun b => secpWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))) (ket zeroBasisState)=
      secpWindowOutputMass Q hrQ out := by
  by_cases hQ : Q=0
  · simp only [secpWindowProgram,dif_pos hQ,secpWindowOutputMass]
    rw [doneFiltered_mass (fun hist => secpWindowDecode Q hrQ hist==
      some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))]
    simp only [secpWindowDecode,dif_pos hQ,ite_true,beq_iff_eq,Option.some.injEq,zeroOutcomeBits_pair]
  · simp only [secpWindowProgram,secpWindowDecode,secpWindowOutputMass,dif_neg hQ]
    rfl
end
end ShorECDLP.Paper2607_13816
