#!/usr/bin/env python3
"""Replay actual Lean gate streams with an independent imperative XOR interpreter."""
from pathlib import Path
import subprocess, tempfile, json
ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r'''
import ShorECDLP.Submission.«2607_13816».Window.TableLookup
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def gateRow : Gate → List Nat
 | .X a => [a]
 | .CX a b => [a,b]
 | .CCX a b c => [a,b,c]
 | _ => []
def main : IO Unit := do
 for n in [0:5] do
  let bits := List.range' 1 n
  let paths := List.range' 8 n
  let mask := fun label => (List.range 3).filterMap fun i =>
   if (label*5+3).testBit i then some (20+i) else none
  let circuit := unaryActionUnitary .inc (fun label q => tableXorGates q (mask label))
    (tableAddressTree bits 0 1) 0 paths
  IO.println s!"{n}:{(Lean.toJson (circuit.map gateRow)).compress}"
'''
def replay(gates, state):
    state=state.copy()
    for row in gates:
        assert 1<=len(row)<=3
        if all(state[w] for w in row[:-1]): state[row[-1]] ^= 1
    return state
if __name__=='__main__':
    with tempfile.TemporaryDirectory(prefix='lookup-stream-') as directory:
        source=Path(directory)/'Check.lean'; source.write_text(LEAN_CHECK)
        result=subprocess.run(['lake','env','lean','--run',str(source)],cwd=ROOT,check=True,text=True,capture_output=True)
    checked=0
    for line in result.stdout.splitlines():
        width,raw=line.split(':',1); n=int(width); gates=json.loads(raw)
        nodes=2**n-1
        assert sum(len(g)==3 for g in gates)==2*nodes
        assert {w for g in gates for w in g}<={0,*range(1,n+1),*range(8,8+n),20,21,22}
        for address in range(2**n):
            for control in range(2):
                for target in range(8):
                    for spectator in range(2):
                        state=[spectator]*26; state[0]=control
                        for i in range(n): state[1+i]=(address>>i)&1; state[8+i]=0
                        for i in range(3): state[20+i]=(target>>i)&1
                        expected=state.copy()
                        for i in range(3): expected[20+i]^=control*((address*5+3)>>i&1)
                        actual=replay(gates,state)
                        assert actual==expected,(n,address,control,target)
                        assert replay(gates,actual)==state
                        checked+=1
    print(f'{checked} actual Lean gate-stream cases passed selection, frame, cleanup and reference counts')
