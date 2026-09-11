#!/usr/bin/env python3
"""Replay actual negative-controlled measured negation, including dirty-bank superpositions."""
from pathlib import Path
import subprocess,tempfile,json,math,cmath,runpy
ROOT=Path(__file__).resolve().parents[1]
ENGINE=runpy.run_path(str(ROOT/'artifacts/check-lookup-add.py'))
run=ENGINE['run'];add=ENGINE['add']
LEAN=r'''

import ShorECDLP.Submission.«2607_13816».Window.NegativeControl
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
private def row : Gate → List Int
 | .X a => [0,a]
 | .CX a b => [1,a,b]
 | .CCX a b c => [2,a,b,c]
 | .H a => [3,a]
 | .P dir k a => [4,a,k,if dir==.forward then 1 else -1]
private def encode : AdaptiveCircuit → Lean.Json
 | .done => Lean.toJson ([0] : List Nat)
 | .unitary gates next => Lean.Json.arr #[Lean.toJson (1:Nat),Lean.toJson (gates.map row),encode next]
 | .xMeasureReset w a b => Lean.Json.arr #[Lean.toJson (2:Nat),Lean.toJson w,encode a,encode b]
def main : IO Unit := do
 let program := negativeControlledModularNegate ([1,2] : List Wire) ([3,4] : List Wire)
   (constantBits 2 3) 0 5 6 7 8
 IO.println (encode program).compress
'''
with tempfile.TemporaryDirectory(prefix='negative-control-') as directory:
 source=Path(directory)/'Check.lean';source.write_text(LEAN)
 out=subprocess.run(['lake','env','lean','--run',str(source)],cwd=ROOT,check=True,text=True,capture_output=True).stdout
 tree=json.loads(out)
basis=[q|(value<<1)|(dirty<<3)|(spectator<<9) for q in range(2) for value in range(3) for dirty in range(4) for spectator in range(2)]
states=[{w:1+0j} for w in basis]
states.append({w:cmath.exp(1j*(i+1))/math.sqrt(len(basis)) for i,w in enumerate(basis)})
branches=0
for state in states:
 expected={}
 for w,amp in state.items():
  value=w>>1&3
  result=value if w&1 else (-value)%3
  add(expected,(w&~(3<<1))|(result<<1),amp)
 outputs=run(tree,state)
 assert abs(sum(abs(a)**2 for _,v in outputs for a in v.values())-1)<1e-9
 for history,actual in outputs:
  coefficient=2**(-len(history)/2)
  for w in actual.keys()|expected.keys():
   assert abs(actual.get(w,0)-coefficient*expected.get(w,0))<1e-9,(history,w)
  branches+=1
print(f'{len(states)} basis/superposition inputs, {branches} actual branches passed sign, modular result, dirty bank, full frame and shared phase')
