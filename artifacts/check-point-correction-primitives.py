#!/usr/bin/env python3
"""Compare emitted equality-edge gate streams with independent scalar counts."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r'''
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCorrectionResources
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def gateVector : Gate → PrimitiveResources
  | .X _ => ⟨1,0,0,0,0,0⟩
  | .H _ => ⟨0,1,0,0,0,0⟩
  | .CX _ _ => ⟨0,0,1,0,0,0⟩
  | .CCX _ _ _ => ⟨0,0,0,1,0,0⟩
  | .P _ _ _ => ⟨0,0,0,0,1,0⟩
def emit (kind : String) (n m a b : Nat) (g : Circuit) : IO Unit := do
  let v := g.foldl (fun v g => v.add (gateVector g)) (⟨0,0,0,0,0,0⟩ : PrimitiveResources)
  IO.println s!"{kind} {n} {m} {a} {b} {v.x} {v.h} {v.cnot} {v.toffoli} {v.phase} {v.measurements}"
def main : IO Unit := do
  for n in List.range' 1 5 do
    for m in List.range' 1 5 do
      for a in List.range (2^n) do
        for b in [0,2^m-1,(2^m-1)/3] do
          emit "small" n m a b (twoRegisterControlledFlip 0 1 2 3
            (List.range' 10 n) (List.range' 20 m) a b (List.range' 30 5))
  for t in [263,518,580,835,838,0] do
    let n := (pointCorrectionX.erase t).length
    let m := (pointCorrectionYInf.erase t).length
    for a in [0,1,2^(n-1),2^n-1,(2^n-1)/3] do
      for b in [0,2^m-1,(2^m-1)/3] do
        emit "production" n m a b (pointCorrectionEdge t a b)
'''
def main():
    with tempfile.TemporaryDirectory(prefix='point-correction-primitives-') as tmp:
        p=Path(tmp)/'Main.lean';p.write_text(LEAN_CHECK)
        result=subprocess.run(['lake','env','lean','--run',str(p)],cwd=ROOT,text=True,capture_output=True,check=True)
    checks=0
    for line in result.stdout.splitlines():
        kind,*nums=line.split(); n,m,a,b,*actual=map(int,nums)
        ones=lambda v,w: bin(v & ((1<<w)-1)).count('1')
        cx=lambda w: int(w==1)
        ccx=lambda w: 0 if w<2 else 2*w-3
        expected=[8*(n-ones(a,n))+4*(m-ones(b,m)),0,4*cx(n)+2*cx(m),4*ccx(n)+2*ccx(m)+3,0,0]
        assert actual==expected,(kind,n,m,a,b,actual,expected)
        if kind=='production':
            assert actual[0]<=3076 and actual[3]<=3061
        checks+=1
    assert checks==1020,checks
    print('PASS: 930 small-selector streams and 90 production correction streams')
if __name__=='__main__': main()
