import ShorECDLP.Submission.«2607_13816».Challenge.Gates
import ShorECDLP.Submission.«2607_13816».Challenge.ExceptionalFields

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- A literal bit or a reference to one protected field bit. -/
abbrev EndpointBit (n : Nat) := Sum Bool (ConstantBit n)
def EndpointBit.read {n : Nat} (read : ConstantBit n → Bool) : EndpointBit n → Bool
  | .inl b => b
  | .inr r => read r

def endpointLoadGate {n : Nat} (port : Wire × EndpointBit n) : List (TemplateGate n) :=
  match port.2 with
  | .inl false => []
  | .inl true => [.literal (.X port.1)]
  | .inr r => [.whenBit r true (.X port.1)]

def endpointLoadGates {n : Nat} (ports : List (Wire × EndpointBit n)) : List (TemplateGate n) :=
  ports.flatMap endpointLoadGate

def bitLoadCircuit : List (Wire × Bool) → Circuit
  | [] => []
  | (w,b)::ps => (if b then [.X w] else []) ++ bitLoadCircuit ps

theorem endpointLoadGates_instantiate {n : Nat}
    (ports : List (Wire × EndpointBit n)) (read : ConstantBit n → Bool) :
    (endpointLoadGates ports).flatMap (TemplateGate.instantiate read) =
      bitLoadCircuit (ports.map fun p => (p.1, EndpointBit.read read p.2)) := by
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨w, b⟩
    cases b with
    | inl b => cases b <;> simpa [endpointLoadGates, endpointLoadGate,
        TemplateGate.instantiate, EndpointBit.read, bitLoadCircuit] using ih
    | inr r => cases h : read r <;> simpa [endpointLoadGates, endpointLoadGate,
        TemplateGate.instantiate, EndpointBit.read, bitLoadCircuit, h] using ih

theorem bitLoadCircuit_frame (ps : List (Wire × Bool)) (st : BasisState)
    (w : Wire) (hw : w ∉ ps.map Prod.fst) :
    Classical.run (bitLoadCircuit ps) st w = st w := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨v,b⟩
    have h : w ≠ v ∧ w ∉ ps.map Prod.fst := by simpa using hw
    cases b with
    | false => exact ih st h.2
    | true =>
      change Classical.run (bitLoadCircuit ps) (st[v ↦ !(st v)]) w = _
      rw [ih _ h.2, upd_other _ _ _ h.1]

theorem bitLoadCircuit_value (ps : List (Wire × Bool))
    (hn : (ps.map Prod.fst).Nodup) (st : BasisState)
    (w : Wire) (b : Bool) (hb : (w,b) ∈ ps) :
    Classical.run (bitLoadCircuit ps) st w = xor (st w) b := by
  induction ps generalizing st with
  | nil => simp at hb
  | cons p ps ih =>
    rcases p with ⟨v,c⟩
    have hn' : v ∉ ps.map Prod.fst ∧ (ps.map Prod.fst).Nodup := by simpa using hn
    rcases List.mem_cons.mp hb with he | ht
    · cases he
      cases b with
      | false => simpa [bitLoadCircuit] using bitLoadCircuit_frame ps st w hn'.1
      | true =>
        change Classical.run (bitLoadCircuit ps) (st[w ↦ !(st w)]) w = _
        rw [bitLoadCircuit_frame ps _ w hn'.1, upd_same]
        cases st w <;> rfl
    · have hw : w ≠ v := by
        intro he
        apply hn'.1
        exact List.mem_map.mpr ⟨(w,b),ht,he⟩
      cases c with
      | false => exact ih hn'.2 st ht
      | true =>
        change Classical.run (bitLoadCircuit ps) (st[v ↦ !(st v)]) w = _
        rw [ih hn'.2 _ ht, upd_other _ _ _ hw]

/-- Every endpoint load is its own unload; no initial zero assumption is needed. -/
theorem bitLoadCircuit_involutive (ps : List (Wire × Bool))
    (hn : (ps.map Prod.fst).Nodup) (st : BasisState) :
    Classical.run (bitLoadCircuit ps) (Classical.run (bitLoadCircuit ps) st) = st := by
  funext w
  by_cases hw : w ∈ ps.map Prod.fst
  · obtain ⟨⟨v,b⟩, hp, he⟩ := List.mem_map.mp hw
    change v = w at he
    subst v
    rw [bitLoadCircuit_value ps hn _ w b hp, bitLoadCircuit_value ps hn st w b hp]
    cases st w <;> cases b <;> rfl
  · rw [bitLoadCircuit_frame ps _ w hw, bitLoadCircuit_frame ps st w hw]

/-- Coordinates are little-endian; bit 512 is the infinity tag, as in pointCoordinateWord. -/
def endpointFieldWord {n : Nat} (row : Fin n) (tag : EndpointBit n)
    (fx fy : Option PointField) (i : Fin 513) : EndpointBit n :=
  if h : i.val < 256 then
    match fx with
    | none => .inl false
    | some f => .inr ⟨row, f, ⟨i.val, h⟩⟩
  else if h : i.val < 512 then
    match fy with
    | none => .inl false
    | some f => .inr ⟨row, f, ⟨i.val-256, by omega⟩⟩

  else tag

/-- All eight words use the same coefficient row. There is no point callback. -/
def exceptionalEndpointWords {n : Nat} (row : Fin n) : Fin 8 → Fin 513 → EndpointBit n :=
  ![endpointFieldWord row (.inl true) (some .exceptionalZeroX) (some .exceptionalZeroY),
    endpointFieldWord row (.inl false) (some .negDoubleX) (some .negY),
    endpointFieldWord row (.inl false) (some .exceptionalNegX) (some .exceptionalNegY),
    endpointFieldWord row (.inr ⟨row, .doubleInfinity, 0⟩)
      (some .exceptionalNegDoubleX) (some .exceptionalNegDoubleY),
    endpointFieldWord row (.inl false) (some .x) (some .y),
    endpointFieldWord row (.inr ⟨row, .doubleInfinity, 0⟩) (some .doubleX) (some .doubleY),
    endpointFieldWord row (.inl true) none none,
    endpointFieldWord row (.inl false) (some .x) (some .negY)]

def exceptionalEndpointPorts {n : Nat} (row : Fin n) (ports : Fin 8 → Fin 513 → Wire) :
    List (Wire × EndpointBit n) :=
  (List.ofFn fun j => List.ofFn fun i => (ports j i, exceptionalEndpointWords row j i)).flatten

theorem exceptionalEndpointPorts_length {n : Nat}
    (row : Fin n) (ports : Fin 8 → Fin 513 → Wire) :
    (exceptionalEndpointPorts row ports).length = 4104 := by
  simp only [exceptionalEndpointPorts, List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn]
  rfl
end ShorECDLP.Paper2607_13816.ChallengeMigration
