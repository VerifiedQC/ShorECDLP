import ShorECDLP.Framework.Quantum.AdaptiveMeasurement
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Source provenance of a lowered Clifford/reversible fragment. One selected
correction block is one logical event, independently of its primitive gate count. -/
inductive CorrectionFragment where
  | ordinary (gates : Circuit)
  | selected (gates : Circuit)
def CorrectionFragment.erase : CorrectionFragment → Circuit
  | .ordinary g | .selected g => g
def CorrectionFragment.events : CorrectionFragment → Nat
  | .ordinary _ => 0
  | .selected _ => 1
def correctionBlockErase (fs : List CorrectionFragment) : Circuit := fs.flatMap CorrectionFragment.erase
def correctionBlockEvents (fs : List CorrectionFragment) : Nat := (fs.map CorrectionFragment.events).sum
/-- Source markers retain the actual unitary-block boundaries. Erasure adds no gates. -/
inductive CorrectionProgram where
  | done
  | unitary (fragments : List CorrectionFragment) (next : CorrectionProgram)
  | reset (wire : Wire) (onFalse onTrue : CorrectionProgram)
namespace CorrectionProgram
def erase : CorrectionProgram → AdaptiveCircuit
  | .done => .done
  | .unitary fs p => .unitary (correctionBlockErase fs) p.erase
  | .reset w a b => .xMeasureReset w a.erase b.erase
def events : CorrectionProgram → Nat
  | .done => 0
  | .unitary fs p => correctionBlockEvents fs+p.events
  | .reset _ a b => max a.events b.events
def seq : CorrectionProgram → CorrectionProgram → CorrectionProgram
  | .done, b => b
  | .unitary fs a, b => .unitary fs (a.seq b)
  | .reset w a c, b => .reset w (a.seq b) (c.seq b)
theorem erase_seq (a b : CorrectionProgram) : (a.seq b).erase=a.erase.seq b.erase := by
  induction a with
  | done => rfl
  | unitary fs a ih => simp [seq,erase,AdaptiveCircuit.seq,ih]
  | reset w a c iha ihc => simp [seq,erase,AdaptiveCircuit.seq,iha,ihc]
theorem events_seq (a b : CorrectionProgram) : (a.seq b).events=a.events+b.events := by
  induction a with
  | done => simp [seq,events]
  | unitary fs a ih => simp [seq,events,ih,Nat.add_assoc]
  | reset w a c iha ihc => simp [seq,events,iha,ihc,max_add_add_right]
end CorrectionProgram
/-- One marker for each selected Z; false outcomes select no fragment. -/
def registerZFragments : List Wire → List Bool → List CorrectionFragment
  | w::ws, b::bs => (if b then [CorrectionFragment.selected (pauliZ w)] else []) ++ registerZFragments ws bs
  | _, _ => []
theorem registerZFragments_erase (ws : List Wire) (bs : List Bool) :
    correctionBlockErase (registerZFragments ws bs)=registerZCorrection ws bs := by
  induction ws generalizing bs with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    simp only [correctionBlockErase] at ih
    cases bs with
    | nil => rfl
    | cons b bs =>
      cases b <;> simp [registerZFragments,correctionBlockErase,CorrectionFragment.erase,registerZCorrection,ih]
theorem registerZFragments_events (ws : List Wire) (bs : List Bool) (hlen : bs.length=ws.length) :
    correctionBlockEvents (registerZFragments ws bs)=bs.count true := by
  induction ws generalizing bs with
  | nil =>
    have hb : bs=[] := by simpa using hlen
    subst bs
    rfl
  | cons w ws ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have ht : bs.length=ws.length := by simpa using hlen
      have hh := ih bs ht
      simp only [correctionBlockEvents] at hh
      cases b <;> simp [registerZFragments,correctionBlockEvents,CorrectionFragment.events,hh,Nat.add_comm]
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Preserve the reset tree while retaining source annotations in its continuation. -/
def correctionResetThen : List Wire → (List Bool → CorrectionProgram) → CorrectionProgram
  | [], next => next []
  | w::ws, next => .reset w (correctionResetThen ws (fun bs => next (false::bs)))
      (correctionResetThen ws (fun bs => next (true::bs)))
theorem correctionResetThen_erase (ws : List Wire) (next : List Bool → CorrectionProgram) :
    (correctionResetThen ws next).erase=measureResetThen ws (fun bs => (next bs).erase) := by
  induction ws generalizing next with
  | nil => rfl
  | cons w ws ih => simp [correctionResetThen,CorrectionProgram.erase,measureResetThen,ih]
/-- A nonnegative per-true-outcome event cost attains its maximum at all true. -/
theorem correctionResetThen_events (ws : List Wire) (next : List Bool → CorrectionProgram)
    (base perTrue : Nat) (h : ∀ bs, bs.length=ws.length → (next bs).events=base+perTrue*bs.count true) :
    (correctionResetThen ws next).events=base+perTrue*ws.length := by
  induction ws generalizing next base with
  | nil => simpa [correctionResetThen] using h [] rfl
  | cons w ws ih =>
    have h0 : ∀ bs, bs.length=ws.length → (next (false::bs)).events=base+perTrue*bs.count true := by
      intro bs hb
      simpa using h (false::bs) (by simpa using hb)
    have h1 : ∀ bs, bs.length=ws.length → (next (true::bs)).events=(base+perTrue)+perTrue*bs.count true := by
      intro bs hb
      have hh := h (true::bs) (by simpa using hb)
      simp only [List.count_cons] at hh
      simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    rw [correctionResetThen,CorrectionProgram.events,ih _ base h0,ih _ (base+perTrue) h1]
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega
/-- Literal reset followed by one Z correction for each selected register bit. -/
def registerZResetSource (ws : List Wire) : CorrectionProgram :=
  correctionResetThen ws (fun bs => .unitary (registerZFragments ws bs) .done)
theorem registerZResetSource_erase (ws : List Wire) :
    (registerZResetSource ws).erase=measureResetThen ws (fun bs => .unitary (registerZCorrection ws bs) .done) := by
  rw [registerZResetSource,correctionResetThen_erase]
  simp only [CorrectionProgram.erase,registerZFragments_erase]
theorem registerZResetSource_events (ws : List Wire) : (registerZResetSource ws).events=ws.length := by
  unfold registerZResetSource
  have hh := correctionResetThen_events ws (fun bs => .unitary (registerZFragments ws bs) .done) 0 1 (by
    intro bs hb
    simp [CorrectionProgram.events,registerZFragments_events ws bs hb])
  simpa using hh
/-- Two selected copies surrounding the unchanged carry recomputation, as in Gidney cleanup. -/
def doubleZCorrectionFragments (ws : List Wire) (bs : List Bool) (middle : Circuit) : List CorrectionFragment :=
  registerZFragments ws bs ++ [.ordinary middle] ++ registerZFragments ws bs
theorem doubleZCorrectionFragments_erase (ws : List Wire) (bs : List Bool) (middle : Circuit) :
    correctionBlockErase (doubleZCorrectionFragments ws bs middle)=
      registerZCorrection ws bs ++ middle ++ registerZCorrection ws bs := by
  simp only [doubleZCorrectionFragments,correctionBlockErase,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,CorrectionFragment.erase,List.append_nil]
  rw [← correctionBlockErase,registerZFragments_erase]
theorem doubleZCorrectionFragments_events (ws : List Wire) (bs : List Bool) (middle : Circuit)
    (hlen : bs.length=ws.length) : correctionBlockEvents (doubleZCorrectionFragments ws bs middle)=2*bs.count true := by
  have hh := registerZFragments_events ws bs hlen
  simp only [correctionBlockEvents] at hh
  simp [doubleZCorrectionFragments,correctionBlockEvents,CorrectionFragment.events,hh,two_mul]
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Reset then perform the two source correction copies around carry recomputation. -/
def doubleZResetSource (ws : List Wire) (middle : Circuit) : CorrectionProgram :=
  correctionResetThen ws (fun bs => .unitary (doubleZCorrectionFragments ws bs middle) .done)
theorem doubleZResetSource_erase (ws : List Wire) (middle : Circuit) :
    (doubleZResetSource ws middle).erase=measureResetThen ws
      (fun bs => .unitary (registerZCorrection ws bs ++ middle ++ registerZCorrection ws bs) .done) := by
  rw [doubleZResetSource,correctionResetThen_erase]
  simp only [CorrectionProgram.erase,doubleZCorrectionFragments_erase]
theorem doubleZResetSource_events (ws : List Wire) (middle : Circuit) :
    (doubleZResetSource ws middle).events=2*ws.length := by
  unfold doubleZResetSource
  have hh := correctionResetThen_events ws (fun bs => .unitary (doubleZCorrectionFragments ws bs middle) .done) 0 2 (by
    intro bs hb
    simp [CorrectionProgram.events,doubleZCorrectionFragments_events ws bs middle hb])
  simpa using hh
end ShorECDLP.Paper2607_13816
