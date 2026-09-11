import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyAdd
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private def gidneyAddVirtualControl (input dirty : List Wire) (c r t : Wire) : Wire :=
  ([c,r,t]++input++dirty).sum+1
private theorem addVirtual_fresh (input dirty : List Wire) (c r t : Wire) :
    gidneyAddVirtualControl input dirty c r t ∉ [c,r,t]++input++dirty := by
  intro h
  have hh : ([c,r,t]++input++dirty).sum+1≤([c,r,t]++input++dirty).sum := List.le_sum_of_mem h
  exact (Nat.not_succ_le_self _) hh
/-- Unconditional source constant adder; its virtual control is compiled away. -/
def gidneyAddConst (input dirty : List Wire) (constant : List Bool) (c r t : Wire) : AdaptiveCircuit :=
  let q := gidneyAddVirtualControl input dirty c r t
  constantControlProgram q (controlledGidneyAddConst input dirty constant q c r t)

theorem gidneyAddConst_wellFormed (input dirty : List Wire) (constant : List Bool) (c r t : Wire)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hnd : ([c,r,t]++input++dirty).Nodup) :
    (gidneyAddConst input dirty constant c r t).WellFormed := by
  apply constantControlProgram_wellFormed
  apply controlledGidneyAddConst_wellFormed _ _ _ _ _ _ _ hk hd
  exact List.nodup_cons.mpr ⟨addVirtual_fresh input dirty c r t,hnd⟩

theorem gidneyAddConst_branch_correct (input dirty : List Wire) (constant : List Bool) (c r t : Wire)
    (s : BasisState) (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hnd : ([c,r,t]++input++dirty).Nodup) (hc : s c=false) (hr : s r=false) (ht : s t=false)
    (b : InstrumentBranch) (hb : b ∈ (gidneyAddConst input dirty constant c r t).run) :
    b.kraus (ket s)=registerXResetMagnitude b.history.length • ket (gidneyUncontrolledAddIdealState input constant s) := by
  let q := gidneyAddVirtualControl input dirty c r t
  have hq : q ∉ [c,r,t]++input++dirty := addVirtual_fresh input dirty c r t
  have hqi : q ∉ input := fun hh => hq (by simp [hh])
  have hneq (w : Wire) (hw : w ∈ [c,r,t]) : w≠q := by intro he; subst w; exact hq (List.mem_append_left _ (List.mem_append_left _ hw))
  have hndq : ([q,c,r,t]++input++dirty).Nodup := List.nodup_cons.mpr ⟨hq,hnd⟩
  obtain ⟨before,hbefore,hh,htransfer⟩ := constantControlProgram_branch q _
    (controlledGidneyAddConst_controlSafe input dirty constant q c r t hq) b hb
  have hold := controlledGidneyAddConst_branch_correct input dirty constant q c r t (upd s q true)
    hk hd hndq (by simpa [upd,hneq c (by simp)] using hc)
    (by simpa [upd,hneq r (by simp)] using hr) (by simpa [upd,hneq t (by simp)] using ht) before hbefore
  have he := gidneyAddIdealState_enabled input constant s q hqi
  have result := htransfer s (gidneyUncontrolledAddIdealState input constant s)
    (registerXResetMagnitude before.history.length) (by rw [hold.1]; simpa only [he] using hold.2)
  have hframe := (gidneyUncontrolledAddIdealState_correct input constant s hk
    (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1).2 q hqi
  have hrestore : upd (gidneyUncontrolledAddIdealState input constant s) q (s q)=gidneyUncontrolledAddIdealState input constant s := by
    funext w
    by_cases hw : w=q <;> simp_all [upd]
  simpa only [hh,hrestore] using result

/-- The specialization emits no gate or measurement on its compiler-only control. -/
theorem gidneyAddConst_virtualControl_absent (input dirty : List Wire) (constant : List Bool) (c r t : Wire) :
    gidneyAddVirtualControl input dirty c r t ∉ (gidneyAddConst input dirty constant c r t).wires := by
  intro h
  have hh := (constantControlProgram_wires _ _
    (controlledGidneyAddConst_controlSafe input dirty constant _ c r t (addVirtual_fresh input dirty c r t)) _).1 h
  exact hh.2 rfl

/-- The virtual constant control is absent from every physical branch. -/
theorem gidneyAddConst256_wires_subset (input dirty : List Wire) (constant : List Bool) (c r t : Wire)
    (hi : input.length=256) (hd : dirty.length=255) (hk : constant.length=256) :
    (gidneyAddConst input dirty constant c r t).wires ⊆ [c,r,t]++input++dirty := by
  let q := gidneyAddVirtualControl input dirty c r t
  have hq : q ∉ [c,r,t]++input++dirty := addVirtual_fresh input dirty c r t
  intro w hw
  obtain ⟨hw,hne⟩ := (constantControlProgram_wires q _
    (controlledGidneyAddConst_controlSafe input dirty constant q c r t hq) w).mp hw
  cases input with
  | nil => simp at hi
  | cons a as =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        have hh := controlledGidneyAddConst_wires_subset a d q c r t as ds k ks hw
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh ⊢
        tauto
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- Complete exact primitive counts for the actual unconditional source adder. -/
theorem gidneyAddConst_primitive_exact (a d c r t : Wire) (k : Bool)
    (input dirty : List Wire) (constant : List Bool)
    (hk : input.length=constant.length) (hd : input.length=dirty.length+1)
    (hn : (k::constant).all (fun b => !b)≠true) :
    primitiveResources (gidneyAddConst (a::input) (d::dirty) (k::constant) c r t)=
      (⟨4*(input.length+1)-2+8*k.toNat+10*constantBitWeight (constant.take dirty.length)+
          (constant.getLastD false).toNat,4*input.length,5*(input.length-1)+6,
        3*(input.length+1)-4,0,input.length⟩ : PrimitiveResources) := by
  let q := gidneyAddVirtualControl (a::input) (d::dirty) c r t
  have hq : q ∉ [c,r,t]++(a::input)++(d::dirty) := addVirtual_fresh _ _ _ _ _
  have hc : c≠q := by intro h; apply hq; simp [← h]
  have hr : r≠q := by intro h; apply hq; simp [← h]
  unfold gidneyAddConst
  exact controlledGidneyAddConst_lowered_primitive_exact a d q c r t k input dirty constant hk hd hn hc hr
end ShorECDLP.Paper2607_13816
