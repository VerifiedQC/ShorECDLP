#!/usr/bin/env python3
"""Cross-check all production step vectors against prior T/M formulas and wire renaming."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.SchedulePrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleResources
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def main : IO Unit := do
  let mut total : PrimitiveResources := ⟨0,0,0,0,0,0⟩
  for T in List.range' 1 1620 do
    let v := indexedStepPrimitiveFormula256 indexedStepProductionRegisters T
    unless secp256k1StepPrimitiveShape T == v do throw (IO.userError s!"scalar mismatch at {T}")
    unless 7*v.toffoli == secp256k1StepTCount T do
      throw (IO.userError s!"T mismatch at {T}: {7*v.toffoli} versus {secp256k1StepTCount T}")
    unless v.measurements == secp256k1StepMeasurements T do
      throw (IO.userError s!"M mismatch at {T}")
    unless v.phase == 0 do throw (IO.userError s!"phase mismatch at {T}")
    let shifted := { indexedStepProductionRegisters with
      work1 := List.range' 1004 259, work2 := List.range' 1263 259,
      lengthT := List.range' 1522 9, lengthQ := List.range' 1531 9,
      lengthS := List.range' 1540 9, lengthRPrime := List.range' 1549 9,
      aux := List.range' 1558 22,phase1 := 1000,phase2 := 1001,iter := 1002,sign := 1003 }
    unless indexedStepPrimitiveFormula256 shifted T == v do
      throw (IO.userError s!"wire-renaming mismatch at {T}")
    total := total.add v
  IO.println s!"1620 indexed-step vectors agree with prior independent T/M formulas and wire renaming; total {repr total}"

"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="indexed-step-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
