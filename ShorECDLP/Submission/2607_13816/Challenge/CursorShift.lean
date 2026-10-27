import ShorECDLP.Submission.«2607_13816».Challenge.SharedTable
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
/-- Prefix existing records without allowing this program to read them. -/
def shiftStraight {n s e : Nat} (offset : Nat) : Straight n s e → Straight n (offset+s) (offset+e)
  | .done => .done
  | .gate g p => .gate g (shiftStraight offset p)
  | .recordGate i v g p => .recordGate (Fin.natAdd offset i) v g (shiftStraight offset p)
  | .measure w p => .measure w (shiftStraight offset p)

theorem shift_lastCases (offset s : Nat) (b : Bool) (h : Fin (offset+s) → Bool) :
    (fun i : Fin (s+1) => (Fin.lastCases b h : Fin (offset+s+1) → Bool) (Fin.natAdd offset i)) =
      Fin.lastCases b (fun i => h (Fin.natAdd offset i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : Fin.natAdd offset (Fin.last s) = Fin.last (offset+s) := Fin.ext rfl
    simp only [he,Fin.lastCases_last]
  · have he : Fin.natAdd offset j.castSucc = (Fin.natAdd offset j).castSucc := rfl
    simp only [he,Fin.lastCases_castSucc]

theorem shiftStraight_instantiate {n s e : Nat} (p : Straight n s e) (offset : Nat)
    (read : ConstantBit n → Bool) (history : Fin (offset+s) → Bool) :
    (shiftStraight offset p).instantiate read history =
      p.instantiate read (fun i => history (Fin.natAdd offset i)) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [shiftStraight,Straight.instantiate,ih]
  | recordGate i v g p ih => simp only [shiftStraight,Straight.instantiate,ih]
  | measure w p ih => simp only [shiftStraight,Straight.instantiate,ih,shift_lastCases]

theorem shiftStraight_gateSlots {n s e : Nat} (p : Straight n s e) (offset : Nat) :
    (shiftStraight offset p).gateSlots = p.gateSlots := by
  induction p <;> simp_all [shiftStraight,Straight.gateSlots]

theorem shiftStraight_wellFormed {n s e : Nat} (p : Straight n s e) (offset : Nat)
    (hp : p.WellFormed) : (shiftStraight offset p).WellFormed := by
  induction p <;> simp_all [shiftStraight,Straight.WellFormed]

def closedWindow {n count : Nat} (p : Straight n 0 count) : OuterWindow n :=
  ⟨count,fun start => shiftStraight start p⟩

theorem closedWindow_run {n count : Nat} (p : Straight n 0 count) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((closedWindow p).program start).instantiate read history = p.instantiate read Fin.elim0 := by
  have he : (fun i : Fin 0 => history (Fin.natAdd start i)) = (Fin.elim0 : Fin 0 → Bool) := by
    funext i; exact Fin.elim0 i
  exact (shiftStraight_instantiate p start read history).trans (congrArg (fun h : Fin 0 → Bool => Straight.instantiate read h p) he)
end ShorECDLP.Paper2607_13816.ChallengeMigration
