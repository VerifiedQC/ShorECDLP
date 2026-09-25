import ShorECDLP.Submission.«2607_13816».Window.StreamPathMass
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq preparedRawProgram physicalPointLookup
private theorem bulk_tail (calls : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit) :
    streamArithmeticBulk calls tail = (streamArithmeticBulk calls .done).seq tail := by
  induction calls with
  | nil => simp only [streamArithmeticBulk,List.foldr_nil,AdaptiveCircuit.seq]
  | cons c calls ih =>
    simp only [streamArithmeticBulk,List.foldr_cons] at *
    rw [ih,circuit_seq_assoc]
private theorem bulk_append (a b : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit) :
    streamArithmeticBulk (a++b) tail =
      (streamArithmeticBulk a .done).seq (streamArithmeticBulk b tail) := by
  rw [streamArithmeticBulk,List.foldr_append]
  exact bulk_tail a _
private theorem indexed_append (start : Nat) (a b : List AdaptiveCircuit) :
    indexedStreamCalls start (a++b) =
      indexedStreamCalls start a ++ indexedStreamCalls (start+a.length) b := by
  simp only [indexedStreamCalls,List.zipIdx_append,List.map_append]


private theorem indexed_raw (P Q : Point) :
    indexedStreamCalls 2 ((List.range' 1 28).map (streamRawIndexedCall P Q)) =
    (List.range' 1 28).map (fun j => (j+1,streamRawIndexedCall P Q j)) := by
  apply List.ext_getElem
  · simp [indexedStreamCalls]
  · intro i hi hj
    simp only [indexedStreamCalls,List.getElem_map,List.getElem_zipIdx,
      List.getElem_range',Nat.one_mul,Prod.swap_prod_mk]
    congr 1
    omega

private theorem indexed_cons (start : Nat) (c : AdaptiveCircuit) (cs : List AdaptiveCircuit) :
    indexedStreamCalls start (c::cs) = (start,c)::indexedStreamCalls (start+1) cs := by
  simp only [indexedStreamCalls,List.zipIdx_cons,List.map_cons,Prod.swap_prod_mk]
private theorem bulk_cons (k : Nat) (c : AdaptiveCircuit)
    (cs : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit) :
    streamArithmeticBulk ((k,c)::cs) tail =
      (c.relabel (streamBankPerm k)).seq (streamArithmeticBulk cs tail) := rfl
private theorem bulk_map (js : List Nat) (f : Nat → AdaptiveCircuit) :
    streamArithmeticBulk (js.map (fun j => (j+1,f j))) .done =
    js.foldr (fun j tail => ((f j).relabel (streamBankPerm (j+1))).seq tail) .done := by
  simp only [streamArithmeticBulk,List.foldr_map]
/-- Both actual relocated axes are exactly the prepared lookup and raw schedule. -/
theorem streamArithmeticBulk_prepared (P Q : Point) (tail : AdaptiveCircuit) :
    (streamArithmeticBulk (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done).seq
      (streamArithmeticBulk (indexedStreamCalls 17 (streamRawRightCalls Q)) tail) =
    ((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q)).seq tail := by
  have hl : 1+(streamRawLeftCalls P Q).length=17 := by simp [streamRawLeftCalls]
  rw [← hl,← bulk_append,← indexed_append,← streamRawIndexedCalls_order]
  rw [indexed_cons,bulk_cons,indexed_raw,bulk_tail,bulk_map,
    ← streamPreparedRawProgram_calls,circuit_seq_assoc]
  rw [streamPreparedLookup]

/-- Fourier acceptance as an instrument with zero maps on rejected outcomes. -/
def streamSelectedFourier (P Q : Point) (accept : List Bool × List Bool → Bool) : Instrument :=
  (fourierOutcomes 256).flatMap (fun ls => (fourierOutcomes 208).map (fun rs =>
    ⟨ls++rs, if accept (ls,rs) then
      (measuredFourierKernel .inverse
        (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) rs).comp
      (measuredFourierKernel .inverse
        (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) ls)
      else 0⟩))
private theorem flat_sum {α : Type} (xs : List α) (f : α → List ℝ) :
    (xs.flatMap f).sum=(xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons,ih]
theorem streamSelectedFourier_mass (P Q : Point) (accept : List Bool × List Bool → Bool) (ψ : State) :
    (streamSelectedFourier P Q accept).bornMass ψ = streamFourierKernelEventMass P Q accept ψ := by
  simp only [streamSelectedFourier,Instrument.bornMass,List.map_flatMap,List.map_map,
    flat_sum,Function.comp_def,streamFourierKernelEventMass]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ls hls
  apply congrArg List.sum
  apply List.map_congr_left
  intro rs hrs
  split <;> simp_all [LinearMap.comp_apply]

private theorem instrument_assoc (I J K : Instrument) :
    (I.seq J).seq K=I.seq (J.seq K) := by
  simp only [Instrument.seq,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,
    List.map_map,Function.comp_def,InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]
/-- Good-input arithmetic mass, retaining final root cleanup before the terminal instrument. -/
theorem streamArithmeticBulk_good_terminal (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (J : Instrument) :
    ((((streamArithmeticBulk (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done).seq
      (streamArithmeticBulk (indexedStreamCalls 17 (streamRawRightCalls Q))
        (.unitary [.X 836] .done))).run).seq J).bornMass
      (streamPreparedGoodEntry P Q hP hQ hrP hrQ) =
    (((AdaptiveCircuit.unitary [.X 836] .done).run).seq J).bornMass
      (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q)
        (streamPreparedGoodEntry P Q hP hQ hrP hrQ)) := by
  rw [streamArithmeticBulk_prepared,AdaptiveCircuit.run_seq,instrument_assoc]
  exact streamPreparedGoodEntry_terminalMass P Q hP hQ hrP hrQ _

private theorem root_kernel_commute (ws : List Wire) (hw : ws.Nodup)
    (hr : 836 ∉ ws) (bs : List Bool) (hb : bs.length=ws.length) (ψ : State) :
    Quantum.run [.X 836] (measuredFourierKernel .inverse ws bs ψ) =
    measuredFourierKernel .inverse ws bs (Quantum.run [.X 836] ψ) := by
  rw [← fourierBranch_eq_kernel .inverse ws hw bs hb]
  exact adaptiveBranch_fourier_commute (.unitary [.X 836] .done) .inverse ws ([] : List Bool) bs
    (by intro w h; simpa [AdaptiveCircuit.wires,circuitWires,gateWires] using
      (show w≠836 from fun e => hr (e ▸ h)))
    ⟨[],Quantum.run [.X 836]⟩ (by simp) ψ
theorem streamTwoKernel_root_norm (xs ys : List Wire) (hx : xs.Nodup) (hy : ys.Nodup)
    (hrx : 836 ∉ xs) (hry : 836 ∉ ys) (ls rs : List Bool)
    (hl : ls.length=xs.length) (hr : rs.length=ys.length) (ψ : State) :
    normSq (measuredFourierKernel .inverse ys rs
      (measuredFourierKernel .inverse xs ls (Quantum.run [.X 836] ψ))) =
    normSq (measuredFourierKernel .inverse ys rs
      (measuredFourierKernel .inverse xs ls ψ)) := by
  rw [← root_kernel_commute xs hx hrx ls hl,
    ← root_kernel_commute ys hy hry rs hr]
  exact normSq_run _ (by simp [CircuitWellFormed,Gate.WellFormed]) _

private theorem indexed_nodup (start : Nat) (cs : List AdaptiveCircuit) :
    ((indexedStreamCalls start cs).map Prod.fst).Nodup := by
  simp only [indexedStreamCalls,List.map_map,Function.comp_def,Prod.fst_swap,List.zipIdx_map_snd]
  exact List.nodup_range'
private theorem wires_no_root (calls : List (Nat × AdaptiveCircuit)) :
    836 ∉ streamFourierWires calls := by
  intro hm
  obtain ⟨c,hc,hw⟩ := List.mem_flatMap.mp hm
  simp only [List.mem_reverse,List.mem_range'_1,windowBankStart] at hw
  omega
/-- Final root cleanup does not change the selected Fourier mass. -/
theorem streamFourierKernelEventMass_root (P Q : Point) (accept : List Bool × List Bool → Bool) (ψ : State) :
    streamFourierKernelEventMass P Q accept (Quantum.run [.X 836] ψ) =
    streamFourierKernelEventMass P Q accept ψ := by
  unfold streamFourierKernelEventMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro ls hls
  apply congrArg List.sum
  apply List.map_congr_left
  intro rs hrs
  split
  · apply streamTwoKernel_root_norm
    · exact streamFourierWires_nodup _ (indexed_nodup _ _)
    · exact streamFourierWires_nodup _ (indexed_nodup _ _)
    · exact wires_no_root _
    · exact wires_no_root _
    · exact ((fourierOutcomes_mem _ _).mp hls).trans (streamRawKernel_precisions P Q).1.symm
    · exact ((fourierOutcomes_mem _ _).mp hrs).trans (streamRawKernel_precisions P Q).2.symm
  · rfl

private theorem seq_mass (I J : Instrument) (ψ : State) :
    (I.seq J).bornMass ψ = (I.map (fun b => J.bornMass (b.kraus ψ))).sum := by
  simp only [Instrument.seq,Instrument.bornMass,List.map_flatMap,List.map_map,
    flat_sum,Function.comp_def,InstrumentBranch.seq,LinearMap.comp_apply]

/-- The same selected Fourier instrument represents the actual record event. -/
theorem streamRawFourierEventMass_terminal (P Q : Point)
    (accept : List Bool × List Bool → Bool) :
    streamRawFourierEventMass P Q accept =
      (((((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q)).seq
        (.unitary [.X 836] .done)).run).seq (streamSelectedFourier P Q accept)).bornMass
          (streamPreparedEntry P Q) := by
  rw [streamRawFourierEventMass_bulk,← streamArithmeticBulk_prepared,seq_mass]
  simp_rw [streamSelectedFourier_mass]

/-- On the original good input component, all arithmetic histories sum to the
ideal scalar output's Fourier event mass. This input decomposition is not a
physical postselection and supplies no lower bound for the full input. -/
theorem streamPreparedGoodEntry_fourierMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0)
    (accept : List Bool × List Bool → Bool) :
    (((((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q)).seq
      (.unitary [.X 836] .done)).run).seq (streamSelectedFourier P Q accept)).bornMass
        (streamPreparedGoodEntry P Q hP hQ hrP hrQ) =
    streamFourierKernelEventMass P Q accept
      (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q)
        (streamPreparedGoodEntry P Q hP hQ hrP hrQ)) := by
  rw [← streamArithmeticBulk_prepared,streamArithmeticBulk_good_terminal,
    seq_mass,AdaptiveCircuit.run_unitary_done,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,streamSelectedFourier_mass,streamFourierKernelEventMass_root]
end
end ShorECDLP.Paper2607_13816
