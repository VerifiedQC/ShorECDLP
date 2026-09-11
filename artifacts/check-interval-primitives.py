#!/usr/bin/env python3
"""Check full interval primitive formulas on extremal measurement paths."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.IntervalPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def gateVector : Gate → PrimitiveResources
  | .X _ => ⟨1,0,0,0,0,0⟩
  | .H _ => ⟨0,1,0,0,0,0⟩
  | .CX _ _ => ⟨0,0,1,0,0,0⟩
  | .CCX _ _ _ => ⟨0,0,0,1,0,0⟩
  | .P _ _ _ => ⟨0,0,0,0,1,0⟩
def pathVector (outcome : Bool) : AdaptiveCircuit → PrimitiveResources
  | .done => ⟨0,0,0,0,0,0⟩
  | .unitary g next => (g.foldl (fun (v : PrimitiveResources) gate => v.add (gateVector gate)) ⟨0,0,0,0,0,0⟩).add (pathVector outcome next)
  | .xMeasureReset _ l r => (⟨0,0,0,0,0,1⟩ : PrimitiveResources).add
      (if outcome then pathVector outcome r else pathVector outcome l)
def regs (k K : Nat) : IntervalRegisters :=
  ⟨0,1,List.range' 2 (intervalLaneCount k K),List.range' 300 (intervalLaneCount k K),
    List.range' 600 9,List.range' 610 9,List.range' 620 9,List.range' 630 24⟩
def main : IO Unit := do
  let mut checked := 0
  for (k,K) in [(4,4),(128,128)] do
    let r := regs k K
    for mode in [RippleMode.add,RippleMode.sub] do
      for signUpdate in [false,true] do
        for target in [IntervalTarget.work1,IntervalTarget.work2] do
        for inverse in [false,true] do
            let program := if inverse then intervalAddSubInverse else intervalAddSub
            let c := program r 256 k K mode signUpdate target
            let expected := intervalPrimitiveFormula9 r 256 k K mode signUpdate
            unless pathVector true c == expected do throw (IO.userError "interval all-one path mismatch")
            let zero : PrimitiveResources := ⟨expected.x,0,expected.cnot-expected.measurements,
              expected.toffoli,0,expected.measurements⟩
            unless pathVector false c == zero do throw (IO.userError "interval all-zero path mismatch")
            checked := checked+1
  IO.println s!"{checked} actual singleton intervals passed both extremal measurement paths"

"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="interval-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
