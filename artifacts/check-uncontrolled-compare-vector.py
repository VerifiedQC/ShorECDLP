#!/usr/bin/env python3
"""Replay actual unconditional threshold-comparator trees, including shortcut branches."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r'''
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledCompare
open ShorECDLP ShorECDLP.Paper2607_13816
def main : IO Unit := do
  for offset in [0,100] do
    for n in List.range 7 do
      for k in List.range (2^n+2) do
        let input := List.range' (offset+10) n
        let dirty := List.range' (offset+20) n
        let actual := gidneyCompareGE input dirty k (offset+1) (offset+2) (offset+3) (offset+4)
        let lowered := constantControlProgram offset (controlledGidneyCompareGE input dirty k offset (offset+1) (offset+2) (offset+3) (offset+4))
        let v := primitiveResources actual
        unless v==primitiveResources lowered do
          throw (IO.userError "virtual-control choice changed counts")
        IO.println s!"{n} {k} {v.x} {v.h} {v.cnot} {v.toffoli} {v.phase} {v.measurements}"
'''
def main():
    with tempfile.TemporaryDirectory(prefix='gidney-add-exact-') as tmp:
        p=Path(tmp)/'Main.lean';p.write_text(LEAN_CHECK)
        result=subprocess.run(['lake','env','lean','--run',str(p)],cwd=ROOT,text=True,capture_output=True,check=True)
    checks=0
    for line in result.stdout.splitlines():
        n,k,x,h,cx,ccx,p,m=map(int,line.split())
        bits=(1<<n)-k
        expected=(1,0,0,0,0,0) if k==0 else ((0,0,0,0,0,0) if k>=(1<<n) else (2*n+7*(bits&1)+9*bin(bits>>1).count('1'),4*n,6*n+1,3*n-1,0,n))
        assert (x,h,cx,ccx,p,m)==expected,(n,k,(x,h,cx,ccx,p,m),expected)
        checks+=1
    assert checks==282,checks
    print('PASS: 282 complete actual unconditional-threshold-comparator vectors and alternate virtual controls, including zero/out-of-range thresholds and widths 0–6')
if __name__=='__main__': main()
