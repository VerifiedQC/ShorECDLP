import ShorECDLP.Submission.EllipticCurve.AffineFormula
import ShorECDLP.Submission.EllipticCurve.PointRegister
import ShorECDLP.Submission.Arithmetic.ModSub
import ShorECDLP.Submission.Arithmetic.Predicates
import ShorECDLP.Submission.Arithmetic.Secp256k1Instance

namespace ShorECDLP
namespace Secp256k1

open Classical
open Arithmetic
open scoped ArithmeticNotation

/-!
# Clean addition of a classical secp256k1 point

This file constructs the reversible operation

    |R⟩ |0⟩ |0_work⟩
      ↦
    |R⟩ |R + C⟩ |0_work⟩

where

* `R` is a quantum secp256k1 point;
* `C` is a classical constant point;
* the input point is preserved;
* every scratch wire is restored.

For a finite constant `C = (x₂,y₂)`, the circuit implements the same
decision tree as `affineAdd`:

    R = O          -> C
    R = -C         -> O
    R = C          -> double R
    otherwise      -> generic affine addition

The generic affine formula is

    λ  = (y₁ - y₂) / (x₁ - x₂)
    x₃ = λ² - x₁ - x₂
    y₃ = λ(x₁ - x₃) - y₁

and doubling is

    λ  = 3x₁² / 2y₁
    x₃ = λ² - 2x₁
    y₃ = λ(x₁ - x₃) - y₁.

All field operations are built from the concrete width-257 arithmetic
already supplied by `Secp256k1Instance`.
-/

private def fieldWidth : Nat :=
  Secp256k1Instance.fieldWidth

/-! -------------------------------------------------------------------------
    Wire relabelling

`Secp256k1Instance` gives us one concrete field-arithmetic circuit whose
wires start at zero.  Point addition needs to place that arithmetic engine
inside a larger circuit, so we translate every arithmetic wire by a fixed
offset.

This does not introduce a new gate.  It simply renames the wires of the
already-defined circuit.
------------------------------------------------------------------------- -/

def shiftGate (offset : Wire) : Gate → Gate
  | .X t       => .X (offset + t)
  | .H t       => .H (offset + t)
  | .CX c t    => .CX (offset + c) (offset + t)
  | .CCX a b t => .CCX (offset + a) (offset + b) (offset + t)
  | .P dir k t => .P dir k (offset + t)

def shiftCircuit (offset : Wire) (c : Circuit) : Circuit :=
  c.map (shiftGate offset)

def shiftWires (offset : Wire) (ws : List Wire) : List Wire :=
  ws.map fun w => offset + w

/-! -------------------------------------------------------------------------
    Local PointAdd workspace

The public registers `pointReg` and `outReg` are supplied to `pointAdd`.

Everything else is allocated consecutively beginning at `workStart`.

There are seven 257-bit field registers:

    xField, yField
        Copies of the quantum point coordinates, padded from 256 to 257 bits.

    t0 ... t4
        Five reusable field temporaries.  Their meanings change as the
        affine formulas progress.

After those come the predicate workspace, branch flags, one candidate
point, and the selected result.

The much larger multiplication/exponentiation scratch is placed after this
small local workspace and is reused by every field operation.
------------------------------------------------------------------------- -/

private def fieldAreaSize : Nat :=
  7 * fieldWidth

private def constOffset : Nat :=
  fieldAreaSize

private def zeroHistoryOffset : Nat :=
  constOffset + 256

private def xDifferenceOffset : Nat :=
  zeroHistoryOffset + 1

private def xHistoryOffset : Nat :=
  xDifferenceOffset + 256

private def yDifferenceOffset : Nat :=
  xHistoryOffset + 256

private def yHistoryOffset : Nat :=
  yDifferenceOffset + 256

private def flagOffset : Nat :=
  yHistoryOffset + 256

private def candidateOffset : Nat :=
  flagOffset + 6

private def selectedOffset : Nat :=
  candidateOffset + pointWidth

private def localWorkSize : Nat :=
  selectedOffset + pointWidth

/-! The seven reusable 257-bit registers. -/

def pointAddX (workStart : Wire) : List Wire :=
  List.range' workStart fieldWidth

def pointAddY (workStart : Wire) : List Wire :=
  List.range' (workStart + fieldWidth) fieldWidth

def pointAddT0 (workStart : Wire) : List Wire :=
  List.range' (workStart + 2 * fieldWidth) fieldWidth

def pointAddT1 (workStart : Wire) : List Wire :=
  List.range' (workStart + 3 * fieldWidth) fieldWidth

def pointAddT2 (workStart : Wire) : List Wire :=
  List.range' (workStart + 4 * fieldWidth) fieldWidth

def pointAddT3 (workStart : Wire) : List Wire :=
  List.range' (workStart + 5 * fieldWidth) fieldWidth

def pointAddT4 (workStart : Wire) : List Wire :=
  List.range' (workStart + 6 * fieldWidth) fieldWidth

/-!
Temporary 256-bit classical-coordinate register.

It is used only while computing

    x_R = x_C
    y_R = -y_C.

The constant is loaded, the clean equality predicate is computed, and the
constant is immediately unloaded.
-/

def pointAddConst (workStart : Wire) : List Wire :=
  List.range' (workStart + constOffset) 256

/-! Predicate histories used by `zeroFlag` and `equalFlag`. -/

def pointAddZeroHistory (workStart : Wire) : List Wire :=
  [workStart + zeroHistoryOffset]

def pointAddXDifference (workStart : Wire) : List Wire :=
  List.range' (workStart + xDifferenceOffset) 256

def pointAddXHistory (workStart : Wire) : List Wire :=
  List.range' (workStart + xHistoryOffset) 256

def pointAddYDifference (workStart : Wire) : List Wire :=
  List.range' (workStart + yDifferenceOffset) 256

def pointAddYHistory (workStart : Wire) : List Wire :=
  List.range' (workStart + yHistoryOffset) 256

/-!
Branch flags.

`infinityFlag`
    1 iff the quantum input point is O.

`xEqFlag`
    1 iff x_R = x_C.

`yNegFlag`
    1 iff y_R = -y_C.

`genericFlag`
    1 iff R is finite and x_R ≠ x_C.

`pairFlag`
    temporary conjunction x_R = x_C and y_R ≠ -y_C.

`doubleFlag`
    1 iff R is finite and the doubling branch must be used.
-/

def pointAddInfinityFlag (workStart : Wire) : Wire :=
  workStart + flagOffset

def pointAddXEqFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 1

def pointAddYNegFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 2

def pointAddGenericFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 3

def pointAddPairFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 4

def pointAddDoubleFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 5

/-!
`candidate` is reused:

* first it stores the generic-addition point;
* then the doubling point;
* finally the classical constant C.

After each use it is uncomputed back to zero.

`selected` accumulates exactly one of these mutually-exclusive branches.
-/

def pointAddCandidate (workStart : Wire) : List Wire :=
  List.range' (workStart + candidateOffset) pointWidth

def pointAddSelected (workStart : Wire) : List Wire :=
  List.range' (workStart + selectedOffset) pointWidth

/-!
The concrete M1 arithmetic engine is placed immediately after the local
PointAdd workspace.

Every field operation below loads its operands into this engine, runs the
already-defined concrete arithmetic circuit, copies the result out, and
reverses the engine.  Therefore this same workspace can be reused for every
field operation in one point addition.
-/

def pointAddArithmeticOffset (workStart : Wire) : Wire :=
  workStart + localWorkSize

def pointAddArithmeticWork (workStart : Wire) : List Wire :=
  shiftWires
    (pointAddArithmeticOffset workStart)
    Secp256k1Instance.secpLayout.allWires

def pointAddWork (workStart : Wire) : List Wire :=
  List.range' workStart localWorkSize ++
    pointAddArithmeticWork workStart

/-! -------------------------------------------------------------------------
    Small reversible helpers
------------------------------------------------------------------------- -/

/--
Conditionally XOR-copy one aligned register into another.

If `control = 0`, `dst` is unchanged.
If `control = 1`, `dst := dst XOR src`.

When `dst` starts at zero this is a controlled copy.
-/
def controlledCopyReg (control : Wire) :
    List Wire → List Wire → Circuit
  | s :: src, d :: dst =>
      circuit! {
        gate! Gate.CCX control s d;
        controlledCopyReg control src dst
      }
  | _, _ => circuit! {}

/--
Pack two 257-bit field values into the 513-bit finite-point representation.

Only the low 256 bits of each field register are used.  The most-significant
257th arithmetic bit is zero for every canonical field element.
-/
def packFinitePoint
    (x y point : List Wire) : Circuit :=
  circuit! {
    loadConst (PointRegister.tag point) 1;
    Arithmetic.copyReg
      (x.take 256)
      (PointRegister.x point);
    Arithmetic.copyReg
      (y.take 256)
      (PointRegister.y point)
  }

/-! -------------------------------------------------------------------------
    Reusable concrete field operations

These wrappers let PointAdd treat the fixed `Secp256k1Instance` circuits
as ordinary clean operations on arbitrary PointAdd registers.

Each wrapper has the conceptual behavior

    |a⟩ |b⟩ |0_out⟩ |0_engine⟩
      ->
    |a⟩ |b⟩ |f(a,b)⟩ |0_engine⟩.

The arithmetic engine is clean again before the wrapper returns.
------------------------------------------------------------------------- -/

private def engineAddLhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.lhs

private def engineAddRhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.rhs

private def engineAddOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.out

def fieldAdd
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineAddLhs offset
  let b := engineAddRhs offset
  let r := engineAddOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpAddProgram
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/-!
A concrete modular-subtraction core using the same first arithmetic blocks
as the concrete modular adder.

Relative blocks:

    0  lhs
    1  rhs
    2  out
    3  raw subtraction
    4  modulus constant
    5  corrected candidate
    6  subtraction carry-in
    7  subtraction carry bank
    8  correction carry-in
    9  correction carry bank
-/

private def fieldSubCore : Circuit :=
  modSub
    (Secp256k1Instance.reg 0).wires
    (Secp256k1Instance.reg 1).wires
    (Secp256k1Instance.reg 2).wires
    (Secp256k1Instance.reg 3).wires
    (Secp256k1Instance.reg 4).wires
    (Secp256k1Instance.reg 5).wires
    (Secp256k1Instance.bitWire 6)
    (Secp256k1Instance.reg 7).wires
    (Secp256k1Instance.bitWire 8)
    (Secp256k1Instance.reg 9).wires
    p

private def engineSubLhs (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 0).wires

private def engineSubRhs (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 1).wires

private def engineSubOut (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 2).wires

def fieldSub
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineSubLhs offset
  let b := engineSubRhs offset
  let r := engineSubOut offset
  let core := shiftCircuit offset fieldSubCore
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/--
Specialized subtraction by a classical constant.

This avoids reserving a permanent 257-bit register for every classical
constant appearing in the affine formulas.
-/
def fieldSubConst
    (offset : Wire)
    (lhs : List Wire)
    (c : Nat)
    (out : List Wire) : Circuit :=
  let a := engineSubLhs offset
  let b := engineSubRhs offset
  let r := engineSubOut offset
  let core := shiftCircuit offset fieldSubCore
  circuit! {
    Arithmetic.copyReg lhs a;
    loadConst b c;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    loadConst b c;
    Arithmetic.copyReg lhs a
  }

private def engineMulLhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.lhs

private def engineMulRhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.rhs

private def engineMulOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.out

def fieldMul
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineMulLhs offset
  let b := engineMulRhs offset
  let r := engineMulOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpMulProgram
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/-!
Fermat inversion.

The concrete exponentiation circuit computes

    a^(p-2) = a⁻¹

for nonzero field elements.

The exponent register is loaded with the classical constant `p - 2`.
-/

private def engineInvBase (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.lhs

private def engineInvExponent (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.rhs

private def engineInvOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.out

def fieldInv
    (offset : Wire)
    (input out : List Wire) : Circuit :=
  let base := engineInvBase offset
  let exponent := engineInvExponent offset
  let result := engineInvOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpProgram
  circuit! {
    Arithmetic.copyReg input base;
    loadConst exponent (p - 2);

    core;

    Arithmetic.copyReg result out;

    core.reverse;

    loadConst exponent (p - 2);
    Arithmetic.copyReg input base
  }

/-! -------------------------------------------------------------------------
    Generic affine addition
------------------------------------------------------------------------- -/

/--
Compute the generic affine coordinates for

    R = (x₁,y₁)
    C = (x₂,y₂)

with `x₁ ≠ x₂`.

Only five temporary field registers are used.

At the end:

    t2 = x₃
    t4 = y₃

while the other temporaries contain reversible history that is removed when
this circuit is run backwards.
-/
def genericPointCompute
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let offset := pointAddArithmeticOffset workStart

  let x := pointAddX workStart
  let y := pointAddY workStart

  let t0 := pointAddT0 workStart
  let t1 := pointAddT1 workStart
  let t2 := pointAddT2 workStart
  let t3 := pointAddT3 workStart
  let t4 := pointAddT4 workStart

  /- t0 = y₁ - y₂ -/
  let numerator :=
    fieldSubConst offset y yC.val t0

  /- t1 = x₁ - x₂ -/
  let denominator :=
    fieldSubConst offset x xC.val t1

  /- t2 = (x₁ - x₂)⁻¹ -/
  let inverse :=
    fieldInv offset t1 t2

  /- t3 = λ -/
  let slope :=
    fieldMul offset t0 t2 t3

  /- After λ has been obtained, numerator/denominator/inverse are no
     longer needed.  Uncomputing them frees t0,t1,t2 for reuse. -/

  /- t0 = λ² -/
  let slopeSq :=
    fieldMul offset t3 t3 t0

  /- t1 = λ² - x₁ -/
  let minusX :=
    fieldSub offset t0 x t1

  /- t2 = x₃ = λ² - x₁ - x₂ -/
  let xOut :=
    fieldSubConst offset t1 xC.val t2

  /- Once x₃ is available, λ² and λ²-x₁ can be uncomputed. -/

  /- t0 = x₁ - x₃ -/
  let xDifference :=
    fieldSub offset x t2 t0

  /- t1 = λ(x₁-x₃) -/
  let yProduct :=
    fieldMul offset t3 t0 t1

  /- t4 = y₃ -/
  let yOut :=
    fieldSub offset t1 y t4

  circuit! {
    numerator;
    denominator;
    inverse;
    slope;

    inverse.reverse;
    denominator.reverse;
    numerator.reverse;

    slopeSq;
    minusX;
    xOut;

    minusX.reverse;
    slopeSq.reverse;

    xDifference;
    yProduct;
    yOut
  }

/-! -------------------------------------------------------------------------
    Point doubling
------------------------------------------------------------------------- -/

/--
Cleanly compute `3*x²` into `out`.

`scratch0` and `scratch1` are restored before the operation returns.
-/
def threeXSquared
    (offset : Wire)
    (x scratch0 scratch1 out : List Wire) : Circuit :=
  let square :=
    fieldMul offset x x scratch0
  let twice :=
    fieldAdd offset scratch0 scratch0 scratch1
  let three :=
    fieldAdd offset scratch1 scratch0 out
  circuit! {
    square;
    twice;
    three;
    twice.reverse;
    square.reverse
  }

/--
Compute the affine doubling coordinates.

For secp256k1, the curve coefficient `a` is zero, hence

    λ = 3x² / 2y.

At the end:

    t2 = x₃
    t4 = y₃.
-/
def doublePointCompute
    (workStart : Wire) : Circuit :=
  let offset := pointAddArithmeticOffset workStart

  let x := pointAddX workStart
  let y := pointAddY workStart

  let t0 := pointAddT0 workStart
  let t1 := pointAddT1 workStart
  let t2 := pointAddT2 workStart
  let t3 := pointAddT3 workStart
  let t4 := pointAddT4 workStart

  /- t2 = 3x₁²; t0,t1 are returned to zero. -/
  let numerator :=
    threeXSquared offset x t0 t1 t2

  /- t0 = 2y₁ -/
  let denominator :=
    fieldAdd offset y y t0

  /- t1 = (2y₁)⁻¹ -/
  let inverse :=
    fieldInv offset t0 t1

  /- t3 = λ -/
  let slope :=
    fieldMul offset t2 t1 t3

  /- t0 = λ² -/
  let slopeSq :=
    fieldMul offset t3 t3 t0

  /- t1 = 2x₁ -/
  let twoX :=
    fieldAdd offset x x t1

  /- t2 = x₃ = λ² - 2x₁ -/
  let xOut :=
    fieldSub offset t0 t1 t2

  /- t0 = x₁ - x₃ -/
  let xDifference :=
    fieldSub offset x t2 t0

  /- t1 = λ(x₁-x₃) -/
  let yProduct :=
    fieldMul offset t3 t0 t1

  /- t4 = y₃ -/
  let yOut :=
    fieldSub offset t1 y t4

  circuit! {
    numerator;
    denominator;
    inverse;
    slope;

    inverse.reverse;
    denominator.reverse;
    numerator.reverse;

    slopeSq;
    twoX;
    xOut;

    twoX.reverse;
    slopeSq.reverse;

    xDifference;
    yProduct;
    yOut
  }

/-! -------------------------------------------------------------------------
    Exceptional-case flags
------------------------------------------------------------------------- -/

/--
Compute the branch flags for addition by the finite constant `(xC,yC)`.

For a valid input point exactly one of the following happens:

* `infinityFlag = 1`
      R = O

* `genericFlag = 1`
      R is finite and x_R ≠ x_C

* `doubleFlag = 1`
      R is finite, x_R = x_C, and y_R ≠ -y_C

* all three are zero
      R = -C, so the result is O.

The inverse-pair branch deliberately requires no output candidate:
the canonical encoding of O is all zero, and `selected` already starts zero.
-/
def pointAddFlags
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let constReg := pointAddConst workStart

  let infinityFlag := pointAddInfinityFlag workStart
  let xEqFlag := pointAddXEqFlag workStart
  let yNegFlag := pointAddYNegFlag workStart
  let genericFlag := pointAddGenericFlag workStart
  let pairFlag := pointAddPairFlag workStart
  let doubleFlag := pointAddDoubleFlag workStart

  circuit! {
    /- infinityFlag = (R = O) -/
    zeroFlag
      (PointRegister.tag pointReg)
      infinityFlag
      (pointAddZeroHistory workStart);

    /- xEqFlag = (x_R = x_C) -/
    loadConst constReg xC.val;
    equalFlag
      (PointRegister.x pointReg)
      constReg
      xEqFlag
      (pointAddXDifference workStart)
      (pointAddXHistory workStart);
    loadConst constReg xC.val;

    /- yNegFlag = (y_R = -y_C) -/
    loadConst constReg (-yC).val;
    equalFlag
      (PointRegister.y pointReg)
      constReg
      yNegFlag
      (pointAddYDifference workStart)
      (pointAddYHistory workStart);
    loadConst constReg (-yC).val;

    /- genericFlag = !infinityFlag && !xEqFlag -/
    gate! Gate.X infinityFlag;
    gate! Gate.X xEqFlag;
    gate! Gate.CCX infinityFlag xEqFlag genericFlag;
    gate! Gate.X xEqFlag;
    gate! Gate.X infinityFlag;

    /- pairFlag = xEqFlag && !yNegFlag -/
    gate! Gate.X yNegFlag;
    gate! Gate.CCX xEqFlag yNegFlag pairFlag;
    gate! Gate.X yNegFlag;

    /- doubleFlag = !infinityFlag && pairFlag -/
    gate! Gate.X infinityFlag;
    gate! Gate.CCX infinityFlag pairFlag doubleFlag;
    gate! Gate.X infinityFlag
  }

/-! -------------------------------------------------------------------------
    Candidate branches
------------------------------------------------------------------------- -/

/--
Compute the generic point candidate, conditionally XOR it into `selected`,
then clean the candidate and every field temporary.
-/
def genericPointBranch
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let compute :=
    genericPointCompute workStart xC yC

  let pack :=
    packFinitePoint
      (pointAddT2 workStart)
      (pointAddT4 workStart)
      (pointAddCandidate workStart)

  circuit! {
    compute;
    pack;

    controlledCopyReg
      (pointAddGenericFlag workStart)
      (pointAddCandidate workStart)
      (pointAddSelected workStart);

    pack.reverse;
    compute.reverse
  }

/--
Compute the doubling candidate, conditionally XOR it into `selected`,
then clean the candidate and every field temporary.
-/
def doublePointBranch
    (workStart : Wire) : Circuit :=
  let compute :=
    doublePointCompute workStart

  let pack :=
    packFinitePoint
      (pointAddT2 workStart)
      (pointAddT4 workStart)
      (pointAddCandidate workStart)

  circuit! {
    compute;
    pack;

    controlledCopyReg
      (pointAddDoubleFlag workStart)
      (pointAddCandidate workStart)
      (pointAddSelected workStart);

    pack.reverse;
    compute.reverse
  }

/--
If the input point is infinity, the answer is the classical constant `C`.

The candidate register is loaded with `C`, conditionally copied, and
immediately cleared.
-/
def infinityPointBranch
    (workStart : Wire)
    (C : Point) : Circuit :=
  let candidate := pointAddCandidate workStart
  let load := loadConst candidate (encode C).val
  circuit! {
    load;

    controlledCopyReg
      (pointAddInfinityFlag workStart)
      candidate
      (pointAddSelected workStart);

    load
  }

/-! -------------------------------------------------------------------------
    Complete finite-constant computation
------------------------------------------------------------------------- -/

/-! -------------------------------------------------------------------------
    PointAdd finite computation: proof-oriented decomposition
------------------------------------------------------------------------- -/

-- The setup stage:

-- 1. copy the public x-coordinate into the padded arithmetic x-register;
-- 2. copy the public y-coordinate into the padded arithmetic y-register;
-- 3. compute the branch flags.

-- It does not touch `selected`.

def pointAddCopyX
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  Arithmetic.copyReg
    (PointRegister.x pointReg)
    ((pointAddX workStart).take 256)

def pointAddCopyY
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  Arithmetic.copyReg
    (PointRegister.y pointReg)
    ((pointAddY workStart).take 256)

def pointAddCoordinateCopies
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  pointAddCopyX pointReg workStart ++
    pointAddCopyY pointReg workStart

def pointAddSetup
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) :
    Circuit :=
  pointAddCoordinateCopies pointReg workStart ++
    pointAddFlags pointReg workStart xC yC
/--
The branch stage.

The flags computed by `pointAddSetup` determine which, if any,
candidate is XORed into `selected`.

* genericFlag = 1  -> generic affine addition
* doubleFlag  = 1  -> doubling
* infinityFlag = 1 -> C
* all zero          -> O
-/
def pointAddBranches
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    Circuit :=
  circuit! {
    genericPointBranch workStart xC yC;
    doublePointBranch workStart;
    infinityPointBranch workStart (.some hC)
  }

/--
The portion of PointAdd scratch used by the three candidate branches.

`pointAddX` and `pointAddY` are deliberately not included: they contain
the copied input coordinates rather than zero.
-/
def pointAddBranchWork (workStart : Wire) : List Wire :=
  pointAddT0 workStart ++
  pointAddT1 workStart ++
  pointAddT2 workStart ++
  pointAddT3 workStart ++
  pointAddT4 workStart ++
  pointAddCandidate workStart ++
  pointAddSelected workStart ++
  pointAddArithmeticWork workStart

/--
The finite computation is exactly setup followed by the candidate branches.
-/
def pointAddFiniteCompute
    (pointReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    Circuit :=
  pointAddSetup pointReg workStart xC yC ++
    pointAddBranches workStart hC

/-! -------------------------------------------------------------------------
    Public PointAdd operation
------------------------------------------------------------------------- -/

/--
Clean out-of-place addition by a classical point.

For `C = O`, addition is just a register copy.

For finite `C`, first compute `R + C` into the private `selected` register,
copy it to `outReg`, and reverse the complete computation.

Thus the intended action is

    |R⟩ |0_out⟩ |0_work⟩
      ↦
    |R⟩ |R+C⟩ |0_work⟩.
-/
def pointAdd
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C : Point) :
    Circuit :=
  match C with
  | .zero =>
      Arithmetic.copyReg pointReg outReg

  | @WeierstrassCurve.Affine.Point.some _ _ _ _xC _yC hC =>
      let compute :=
        pointAddFiniteCompute pointReg workStart hC
      circuit! {
        compute;

        Arithmetic.copyReg
          (pointAddSelected workStart)
          outReg;

        compute.reverse
      }

/-! -------------------------------------------------------------------------
    Correctness proof decomposition

There are three genuinely different proof obligations.

1. `pointAddFiniteCompute_correct`
   Prove the actual elliptic-curve arithmetic: after the forward computation,
   `selected` contains `affineAdd R C`.

2. `pointAddFiniteCompute_structural`
   Prove that the forward circuit is a valid classical reversible computation,
   is confined to the PointAdd input/workspace, and that `selected` is part of
   that workspace.

3. `bennett_copyReg_eq_writeReg`
   A generic reversible-computing lemma: if `compute` produces a value in a
   scratch register, copying that value to a clean output and reversing
   `compute` leaves exactly that output written into the original state.

The final theorem then contains essentially no elliptic-curve arithmetic.
------------------------------------------------------------------------- -/

/--
Exact register copying.

If `src` contains `value` and `dst` is a clean, disjoint register of the
same width, then CNOT-copying `src` to `dst` has exactly the same whole-state
effect as `writeReg dst value`.

This is useful both for the `C = O` case and inside the Bennett argument.
-/
theorem copyReg_eq_writeReg_of_value
    (src dst work : List Wire)
    (st : BasisState)
    (value : Nat)
    (hlen : dst.length = src.length)
    (hnodup : (src ++ dst ++ work).Nodup)
    (hclean : Clean dst st)
    (hvalue : regValue src st = value)
    (_hbound : value < 2 ^ dst.length) :
    Classical.run (Arithmetic.copyReg src dst) st =
      writeReg dst value st := by
  have aux :
      ∀ (src dst : List Wire) (st : BasisState),
        dst.length = src.length →
        (src ++ dst).Nodup →
        Clean dst st →
        Classical.run (Arithmetic.copyReg src dst) st =
          writeReg dst (regValue src st) st := by
    intro src
    induction src with
    | nil =>
        intro dst st hlen hnd hclean
        have hdst : dst = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using hlen
        subst dst
        rfl
    | cons s src ih =>
        intro dst st hlen hnd hclean
        cases dst with
        | nil =>
            simp at hlen
        | cons d dst =>
            have hlenTail : dst.length = src.length := by
              simpa using hlen

            obtain ⟨hsrcNd, hdstNd, hcross⟩ :=
              List.nodup_append.mp hnd
            obtain ⟨_, hsrcTailNd⟩ :=
              List.nodup_cons.mp hsrcNd
            obtain ⟨hdDst, hdstTailNd⟩ :=
              List.nodup_cons.mp hdstNd

            have htailNd : (src ++ dst).Nodup :=
              List.nodup_append.mpr
                ⟨hsrcTailNd, hdstTailNd,
                  fun a ha b hb =>
                    hcross a
                      (List.mem_cons_of_mem s ha)
                      b
                      (List.mem_cons_of_mem d hb)⟩

            have hdSrc : d ∉ src := by
              intro hd
              exact
                (hcross d
                  (List.mem_cons_of_mem s hd)
                  d
                  (List.mem_cons_self)) rfl

            let st₁ := Classical.applyGate (Gate.CX s d) st

            have hcleanTail : Clean dst st₁ := by
              intro w hw
              change
                st[d ↦ Bool.xor (st d) (st s)] w = false
              have hwd : w ≠ d := by
                intro h
                subst w
                exact hdDst hw
              rw [upd_other _ _ _ hwd]
              exact hclean w (List.mem_cons_of_mem d hw)

            have hsrcKeep :
                regValue src st₁ = regValue src st := by
              change
                regValue src
                    (st[d ↦ Bool.xor (st d) (st s)]) =
                  regValue src st
              exact
                regValue_upd_not_mem src st d
                  (Bool.xor (st d) (st s)) hdSrc

            have hbit :
                (regValue (s :: src) st).testBit 0 = st s := by
              rw [regValue_cons, Nat.testBit_zero]
              cases hs : st s <;>
                simp [ Nat.add_mod]

            have hdiv :
                regValue (s :: src) st / 2 =
                  regValue src st := by
              rw [regValue_cons]
              cases hs : st s <;> simp ; omega

            have hst₁ :
                st₁ =
                  st[d ↦
                    (regValue (s :: src) st).testBit 0] := by
              simp only [st₁, Classical.applyGate]
              rw [hclean d (List.mem_cons_self)]
              simp [hbit]

            have hih :=
              ih dst st₁ hlenTail htailNd hcleanTail

            rw [Arithmetic.copyReg, Classical.run_cons]
            change
              Classical.run (Arithmetic.copyReg src dst) st₁ =
                writeReg (d :: dst)
                  (regValue (s :: src) st) st
            rw [hih, hsrcKeep, writeReg, hdiv, ← hst₁]

  have hnd : (src ++ dst).Nodup :=
    (List.nodup_append.mp hnodup).1

  calc
    Classical.run (Arithmetic.copyReg src dst) st =
        writeReg dst (regValue src st) st :=
      aux src dst st hlen hnd hclean
    _ = writeReg dst value st := by rw [hvalue]


def pointAddFlagWork (workStart : Wire) : List Wire :=
  pointAddConst workStart ++
  pointAddZeroHistory workStart ++
  pointAddXDifference workStart ++
  pointAddXHistory workStart ++
  pointAddYDifference workStart ++
  pointAddYHistory workStart ++
  [
    pointAddInfinityFlag workStart,
    pointAddXEqFlag workStart,
    pointAddYNegFlag workStart,
    pointAddGenericFlag workStart,
    pointAddPairFlag workStart,
    pointAddDoubleFlag workStart
  ]

theorem pointAddCopyX_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run (pointAddCopyX pointReg workStart) st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        after := by
  dsimp

  have hlocalSizeEq : localWorkSize = 4112 := by
    norm_num [localWorkSize, selectedOffset, candidateOffset, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth, pointWidth]

  have hlocalSize : 257 ≤ localWorkSize := by omega

  have hdstEq :
      (pointAddX workStart).take 256 =
        List.range' workStart 256 := by
    simp [pointAddX, fieldWidth, Secp256k1Instance.fieldWidth,
      List.take_range'_of_length_ge]

  have hdstWork :
      ∀ w ∈ (pointAddX workStart).take 256,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [hdstEq] at hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    exact List.mem_range'_1.mpr ⟨hbounds.1, by omega⟩

  have hsrcMem :
      ∀ w ∈ PointRegister.x pointReg, w ∈ pointReg := by
    intro w hw
    change w ∈ (pointReg.drop 1).take 256 at hw
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)

  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup

  have hsrcNodup : (PointRegister.x pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 1)).trans
        (List.drop_sublist 1 pointReg))
    exact hpointNodup

  have hdstNodup : ((pointAddX workStart).take 256).Nodup := by
    rw [hdstEq]
    exact List.nodup_range'

  have hcopyNodup :
      (PointRegister.x pointReg ++
        (pointAddX workStart).take 256).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hsrcNodup, hdstNodup, ?_⟩
    intro a ha b hb
    exact hpublicWork a
      (List.mem_append_left outReg (hsrcMem a ha))
      b (hdstWork b hb)

  have hdstClean :
      Clean ((pointAddX workStart).take 256) st :=
    Arithmetic.Clean.mono hclean hdstWork

  have hcopyValue :
      regValue ((pointAddX workStart).take 256)
          (Classical.run (pointAddCopyX pointReg workStart) st) =
        regValue (PointRegister.x pointReg) st := by
    simpa only [pointAddCopyX] using
      (Arithmetic.copyReg_correct
        (PointRegister.x pointReg)
        ((pointAddX workStart).take 256)
        st
        (by
          rw [hdstEq]
          simpa using
            (PointRegister.x_length pointReg hpointLength).symm)
        hcopyNodup hdstClean)

  have hother (w : Wire)
      (hw : w ∉ (pointAddX workStart).take 256) :
      Classical.run (pointAddCopyX pointReg workStart) st w = st w := by
    simpa only [pointAddCopyX] using
      (Arithmetic.copyReg_other w
        (PointRegister.x pointReg)
        ((pointAddX workStart).take 256) st hw)

  have hpointAgree :
      AgreesOn pointReg st
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    apply hother
    intro hdst
    exact
      (hpublicWork w (List.mem_append_left outReg hw)
        w (hdstWork w hdst)) rfl

  have hhighNotDst :
      workStart + 256 ∉ (pointAddX workStart).take 256 := by
    rw [hdstEq]
    simp [List.mem_range'_1]

  have hhighWork : workStart + 256 ∈ pointAddWork workStart := by
    rw [pointAddWork]
    apply List.mem_append_left
    exact List.mem_range'_1.mpr ⟨by omega, by omega⟩

  have hhighClean :
      Clean [workStart + 256]
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    rw [hother (workStart + 256) hhighNotDst]
    exact hclean (workStart + 256) hhighWork

  have hpointAddXShape :
      pointAddX workStart =
        PointRegister.padCoordinate
          ((pointAddX workStart).take 256)
          (workStart + 256) := by
    rw [PointRegister.padCoordinate, hdstEq]
    change
      List.range' workStart 257 =
        List.range' workStart 256 ++ [workStart + 256]
    simpa using
      (List.range'_concat (s := workStart) (n := 256) (step := 1))

  have hxValue :
      regValue (pointAddX workStart)
          (Classical.run (pointAddCopyX pointReg workStart) st) =
        regValue (PointRegister.x pointReg) st := by
    rw [hpointAddXShape]
    exact
      (PointRegister.regValue_padCoordinate_of_clean
        ((pointAddX workStart).take 256)
        (workStart + 256)
        (Classical.run (pointAddCopyX pointReg workStart) st)
        hhighClean).trans hcopyValue

  have rangeBounds
      (offset len : Nat)
      {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmin : 257 ≤ offset)
      (hmax : offset + len ≤ 4112) :
      workStart + 257 ≤ w ∧ w < workStart + 4112 := by
    constructor
    · exact (Nat.add_le_add_left hmin workStart).trans hw.1
    · apply hw.2.trans_le
      simpa [Nat.add_assoc] using
        (Nat.add_le_add_left hmax workStart)

  have wireBounds
      (offset : Nat)
      {w : Wire}
      (hw : w = workStart + offset)
      (hmin : 257 ≤ offset)
      (hmax : offset < 4112) :
      workStart + 257 ≤ w ∧ w < workStart + 4112 := by
    subst w
    exact
      ⟨Nat.add_le_add_left hmin workStart,
        Nat.add_lt_add_left hmax workStart⟩

  have hremainingFacts :
      ∀ w ∈
          (pointAddY workStart ++
            pointAddFlagWork workStart ++
            pointAddBranchWork workStart),
        workStart + 257 ≤ w ∧ w ∈ pointAddWork workStart := by
    intro w hw
    rcases List.mem_append.mp hw with hyFlag | hbranch
    · rcases List.mem_append.mp hyFlag with hy | hflag
      · have hyRaw :
            workStart + 257 ≤ w ∧ w < workStart + 257 + 257 := by
          simpa [pointAddY, fieldWidth,
            Secp256k1Instance.fieldWidth] using
            (List.mem_range'_1.mp hy)
        have hbounds :=
          rangeBounds 257 257 hyRaw (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
      · have hbounds :
            workStart + 257 ≤ w ∧ w < workStart + 4112 := by
          simp only [pointAddFlagWork, pointAddConst,
            pointAddZeroHistory, pointAddXDifference,
            pointAddXHistory, pointAddYDifference,
            pointAddYHistory, pointAddInfinityFlag,
            pointAddXEqFlag, pointAddYNegFlag,
            pointAddGenericFlag, pointAddPairFlag,
            pointAddDoubleFlag, List.mem_append,
            List.mem_cons,
            List.mem_range'_1] at hflag
          norm_num [localWorkSize, selectedOffset, candidateOffset,
            flagOffset, yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth, pointWidth] at hflag
          rcases hflag with
              (((((h0 | h1) | h2) | h3) | h4) | h5) |
                (h6 | h7 | h8 | h9 | h10 | h11)
          · exact rangeBounds 1799 256 h0 (by omega) (by omega)
          · exact wireBounds 2055 h1 (by omega) (by omega)
          · exact rangeBounds 2056 256 h2 (by omega) (by omega)
          · exact rangeBounds 2312 256 h3 (by omega) (by omega)
          · exact rangeBounds 2568 256 h4 (by omega) (by omega)
          · exact rangeBounds 2824 256 h5 (by omega) (by omega)
          · exact wireBounds 3080 h6 (by omega) (by omega)
          · exact wireBounds 3081 h7 (by omega) (by omega)
          · exact wireBounds 3082 h8 (by omega) (by omega)
          · exact wireBounds 3083 h9 (by omega) (by omega)
          · exact wireBounds 3084 h10 (by omega) (by omega)
          · exact wireBounds 3085 h11 (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
    · rcases List.mem_append.mp hbranch with hlocal | harithmetic
      · have hbounds :
            workStart + 257 ≤ w ∧ w < workStart + 4112 := by
          simp only [pointAddT0, pointAddT1,
            pointAddT2, pointAddT3, pointAddT4,
            pointAddCandidate, pointAddSelected,
            List.mem_append, List.mem_range'_1] at hlocal
          norm_num [localWorkSize, selectedOffset, candidateOffset,
            flagOffset, yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth, pointWidth] at hlocal
          rcases hlocal with
              (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
          · exact rangeBounds 514 257 h0 (by omega) (by omega)
          · exact rangeBounds 771 257 h1 (by omega) (by omega)
          · exact rangeBounds 1028 257 h2 (by omega) (by omega)
          · exact rangeBounds 1285 257 h3 (by omega) (by omega)
          · exact rangeBounds 1542 257 h4 (by omega) (by omega)
          · exact rangeBounds 3086 513 h5 (by omega) (by omega)
          · exact rangeBounds 3599 513 h6 (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
      · have hshifted :
            ∃ a ∈ Secp256k1Instance.secpLayout.allWires,
              pointAddArithmeticOffset workStart + a = w := by
          simpa only [pointAddArithmeticWork, shiftWires,
            List.mem_map] using harithmetic
        rcases hshifted with ⟨a, ha, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [pointAddArithmeticOffset]
          exact
            (Nat.add_le_add_left hlocalSize workStart).trans
              (Nat.le_add_right (workStart + localWorkSize) a)
        · rw [pointAddWork]
          exact List.mem_append_right _ harithmetic

  have hremainingClean :
      Clean
        (pointAddY workStart ++
          pointAddFlagWork workStart ++
          pointAddBranchWork workStart)
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    have hwFacts := hremainingFacts w hw
    have hwGe : workStart + 257 ≤ w := hwFacts.1
    have hwNotDst : w ∉ (pointAddX workStart).take 256 := by
      intro hdst
      rw [hdstEq] at hdst
      have hbounds : workStart ≤ w ∧ w < workStart + 256 :=
        List.mem_range'_1.mp hdst
      have hwLt : w < workStart + 257 :=
        hbounds.2.trans_le
          (Nat.add_le_add_left (by omega : 256 ≤ 257) workStart)
      exact (Nat.not_lt_of_ge hwGe) hwLt
    rw [hother w hwNotDst]
    exact hclean w hwFacts.2

  exact ⟨hpointAgree, hxValue, hremainingClean⟩

theorem pointAddCopyY_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        st) :
    let after :=
      Classical.run (pointAddCopyY pointReg workStart) st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after := by
  sorry

theorem pointAddCoordinateCopies_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddCoordinateCopies pointReg workStart)
        st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp
  rw [pointAddCoordinateCopies, Classical.run_append]

  let mid :=
    Classical.run (pointAddCopyX pointReg workStart) st

  have hx :=
    pointAddCopyX_correct
      pointReg outReg workStart st
      hpointLength hnodup hclean

  change
    AgreesOn pointReg st mid ∧
      regValue (pointAddX workStart) mid =
        regValue (PointRegister.x pointReg) st ∧
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        mid
    at hx

  rcases hx with ⟨hpointX, hxValue, hcleanAfterX⟩

  have hy :=
    pointAddCopyY_correct
      pointReg outReg workStart mid
      hpointLength hnodup hcleanAfterX

  let after :=
    Classical.run (pointAddCopyY pointReg workStart) mid

  change
    AgreesOn pointReg mid after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) mid ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) mid ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after
    at hy

  rcases hy with
    ⟨hpointY, hxKeep, hyValue, hflagClean, hbranchClean⟩

  have hpointFinal : AgreesOn pointReg st after := by
    intro w hw
    calc
      after w = mid w := hpointY w hw
      _ = st w := hpointX w hw

  have hyPublic :
      regValue (PointRegister.y pointReg) mid =
        regValue (PointRegister.y pointReg) st := by
    exact Arithmetic.AgreesOn.regValue
      (fun w hw => hpointX w (by
        rw [← PointRegister.tag_x_y pointReg hpointLength]
        simp [hw]))

  change
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after

  refine ⟨hpointFinal, ?_, ?_, hflagClean, hbranchClean⟩
  · exact hxKeep.trans hxValue
  · exact hyValue.trans hyPublic

theorem pointAddFlags_semantics
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hcleanFlags :
      Clean (pointAddFlagWork workStart) st)
    (hcleanBranch :
      Clean (pointAddBranchWork workStart) st) :
    let after :=
      Classical.run
        (pointAddFlags pointReg workStart xC yC)
        st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) st ∧
      regValue (pointAddY workStart) after =
        regValue (pointAddY workStart) st ∧
      after (pointAddInfinityFlag workStart) =
        decide (regValue (PointRegister.tag pointReg) st = 0) ∧
      after (pointAddGenericFlag workStart) =
        decide (
          regValue (PointRegister.tag pointReg) st ≠ 0 ∧
          regValue (PointRegister.x pointReg) st ≠ xC.val) ∧
      after (pointAddDoubleFlag workStart) =
        decide (
          regValue (PointRegister.tag pointReg) st ≠ 0 ∧
          regValue (PointRegister.x pointReg) st = xC.val ∧
          regValue (PointRegister.y pointReg) st ≠ (-yC).val) ∧
      Clean (pointAddBranchWork workStart) after := by
  sorry

/--
If the input is O, setup detects exactly the infinity branch.

The branch workspace remains clean because setup only writes the coordinate
copies and flag/predicate workspace.
-/
theorem pointAddSetup_zero_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat (0 : Point))
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddSetup pointReg workStart xC yC)
        st
    after (pointAddInfinityFlag workStart) = true ∧
      after (pointAddGenericFlag workStart) = false ∧
      after (pointAddDoubleFlag workStart) = false ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp
  rw [pointAddSetup, Classical.run_append]

  let copied :=
    Classical.run
      (pointAddCoordinateCopies pointReg workStart)
      st

  have hcopy :
      AgreesOn pointReg st copied ∧
        regValue (pointAddX workStart) copied =
          regValue (PointRegister.x pointReg) st ∧
        regValue (pointAddY workStart) copied =
          regValue (PointRegister.y pointReg) st ∧
        Clean (pointAddFlagWork workStart) copied ∧
        Clean (pointAddBranchWork workStart) copied := by
    simpa [copied] using
      pointAddCoordinateCopies_correct
        pointReg outReg workStart st
        hpointLength hnodup hclean

  rcases hcopy with
    ⟨hpointAgree, _, _, hflagClean, hbranchClean⟩

  have hpointCopied :
      regValue pointReg copied = encodeNat (0 : Point) := by
    calc
      regValue pointReg copied = regValue pointReg st :=
        Arithmetic.AgreesOn.regValue hpointAgree
      _ = encodeNat (0 : Point) := hpoint

  have hslices :=
    PointRegister.slices_of_regValue_zero
      pointReg copied hpointLength hpointCopied

  rcases hslices with ⟨htag, _, _⟩

  let after :=
    Classical.run
      (pointAddFlags pointReg workStart xC yC)
      copied

  have hflags :
      AgreesOn pointReg copied after ∧
        regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied ∧
        regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied ∧
        after (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) copied = 0) ∧
        after (pointAddGenericFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied ≠ xC.val) ∧
        after (pointAddDoubleFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied = xC.val ∧
            regValue (PointRegister.y pointReg) copied ≠ (-yC).val) ∧
        Clean (pointAddBranchWork workStart) after := by
    simpa [after] using
      pointAddFlags_semantics
        pointReg outReg workStart copied
        hpointLength hnodup hflagClean hbranchClean

  rcases hflags with
    ⟨_, _, _, hinfinity, hgeneric, hdouble, hcleanAfter⟩

  change
    after (pointAddInfinityFlag workStart) = true ∧
      after (pointAddGenericFlag workStart) = false ∧
      after (pointAddDoubleFlag workStart) = false ∧
      Clean (pointAddBranchWork workStart) after

  refine ⟨?_, ?_, ?_, hcleanAfter⟩
  · simpa [htag] using hinfinity
  · simpa [htag] using hgeneric
  · simpa [htag] using hdouble

/--
For a finite input R=(xR,yR), setup:

* loads xR and yR into the padded field registers;
* establishes that R is not infinity;
* computes the generic and doubling conditions;
* leaves all branch scratch clean.

The two useful branch predicates are

    generic = (xR ≠ xC)

and

    double = (xR = xC ∧ yR ≠ -yC).
-/
theorem pointAddSetup_some_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat (.some hR))
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddSetup pointReg workStart xC yC)
        st
    regValue (pointAddX workStart) after = xR.val ∧
      regValue (pointAddY workStart) after = yR.val ∧
      after (pointAddInfinityFlag workStart) = false ∧
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) ∧
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) ∧
      Clean (pointAddBranchWork workStart) after := by
  letI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩

  dsimp
  rw [pointAddSetup, Classical.run_append]

  let copied :=
    Classical.run
      (pointAddCoordinateCopies pointReg workStart)
      st

  have hcopy :
      AgreesOn pointReg st copied ∧
        regValue (pointAddX workStart) copied =
          regValue (PointRegister.x pointReg) st ∧
        regValue (pointAddY workStart) copied =
          regValue (PointRegister.y pointReg) st ∧
        Clean (pointAddFlagWork workStart) copied ∧
        Clean (pointAddBranchWork workStart) copied := by
    simpa [copied] using
      pointAddCoordinateCopies_correct
        pointReg outReg workStart st
        hpointLength hnodup hclean

  rcases hcopy with
    ⟨hpointAgree, hxCopy, hyCopy, hflagClean, hbranchClean⟩

  have hslicesBefore :=
    PointRegister.slices_of_regValue_some
      pointReg st hR hpointLength hpoint

  rcases hslicesBefore with
    ⟨_, hxBefore, hyBefore⟩

  have hpointCopied :
      regValue pointReg copied = encodeNat (.some hR) := by
    calc
      regValue pointReg copied = regValue pointReg st :=
        Arithmetic.AgreesOn.regValue hpointAgree
      _ = encodeNat (.some hR) := hpoint

  have hslicesCopied :=
    PointRegister.slices_of_regValue_some
      pointReg copied hR hpointLength hpointCopied

  rcases hslicesCopied with
    ⟨htag, hxPublic, hyPublic⟩

  let after :=
    Classical.run
      (pointAddFlags pointReg workStart xC yC)
      copied

  have hflags :
      AgreesOn pointReg copied after ∧
        regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied ∧
        regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied ∧
        after (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) copied = 0) ∧
        after (pointAddGenericFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied ≠ xC.val) ∧
        after (pointAddDoubleFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied = xC.val ∧
            regValue (PointRegister.y pointReg) copied ≠ (-yC).val) ∧
        Clean (pointAddBranchWork workStart) after := by
    simpa [after] using
      pointAddFlags_semantics
        pointReg outReg workStart copied
        hpointLength hnodup hflagClean hbranchClean

  rcases hflags with
    ⟨_, hxKeep, hyKeep,
      hinfinity, hgeneric, hdouble, hcleanAfter⟩

  have hxFinal :
      regValue (pointAddX workStart) after = xR.val := by
    calc
      regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied := hxKeep
      _ = regValue (PointRegister.x pointReg) st := hxCopy
      _ = xR.val := hxBefore

  have hyFinal :
      regValue (pointAddY workStart) after = yR.val := by
    calc
      regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied := hyKeep
      _ = regValue (PointRegister.y pointReg) st := hyCopy
      _ = yR.val := hyBefore

  have hxVal :
      xR.val = xC.val ↔ xR = xC := by
    constructor
    · intro h
      exact ZMod.val_injective p h
    · intro h
      subst xC
      rfl

  have hyVal :
      yR.val = (-yC).val ↔ yR = -yC := by
    constructor
    · intro h
      exact ZMod.val_injective p h
    · intro h
      subst yR
      rfl

  have hinfinity' :
      after (pointAddInfinityFlag workStart) = false := by
    simpa [htag] using hinfinity

  have hgeneric' :
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) := by
    simpa [htag, hxPublic, hxVal] using hgeneric

  have hdouble' :
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) := by
    simpa [htag, hxPublic, hyPublic, hxVal, hyVal] using hdouble

  change
    regValue (pointAddX workStart) after = xR.val ∧
      regValue (pointAddY workStart) after = yR.val ∧
      after (pointAddInfinityFlag workStart) = false ∧
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) ∧
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) ∧
      Clean (pointAddBranchWork workStart) after

  exact
    ⟨hxFinal, hyFinal, hinfinity',
      hgeneric', hdouble', hcleanAfter⟩

/--
When only the infinity branch is enabled, the branch stage writes C into
`selected`.

The generic and doubling circuits still execute, but because their controls
are false their candidates are computed and uncomputed without changing
`selected`.
-/
theorem pointAddBranches_infinity_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = true)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (.some hC) := by
  sorry

/--
When all three branch controls are false, nothing is XORed into `selected`.

Since `selected` starts clean, it stays zero, which is exactly the canonical
encoding of the point at infinity.
-/
theorem pointAddBranches_inverse_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (0 : Point) := by
  sorry

/--
When the generic flag is the unique active branch, the branch circuit
computes the generic affine point

    genericAdd hR hC hx

and writes its canonical encoding into `selected`.

This is the lemma that must prove the correctness of
`genericPointCompute`.
-/
theorem pointAddBranches_generic_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (hC : curve.toAffine.Nonsingular xC yC)
    (hx : xR ≠ xC)
    (st : BasisState)
    (hxReg :
      regValue (pointAddX workStart) st = xR.val)
    (hyReg :
      regValue (pointAddY workStart) st = yR.val)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = true)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (genericAdd hR hC hx) := by
  sorry

/--
When the doubling flag is the unique active branch, the branch circuit
computes the secp256k1 doubling formulas and writes that point into
`selected`.
-/
theorem pointAddBranches_double_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (hC : curve.toAffine.Nonsingular xC yC)
    (hx : xR = xC)
    (hinv : yR ≠ -yC)
    (st : BasisState)
    (hxReg :
      regValue (pointAddX workStart) st = xR.val)
    (hyReg :
      regValue (pointAddY workStart) st = yR.val)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = true)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat
        (doublePoint hR
          (self_not_inverse_of_x_eq_of_not_inverse
            hR hC hx hinv)) := by
  sorry

theorem pointAddFiniteCompute_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat R)
    (hclean :
      Clean (pointAddWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddFiniteCompute pointReg workStart hC)
          st) =
      encodeNat (affineAdd R (.some hC)) := by

  rw [pointAddFiniteCompute, Classical.run_append]

  let setupState :=
    Classical.run
      (pointAddSetup pointReg workStart xC yC)
      st

  change
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          setupState) =
      encodeNat (affineAdd R (.some hC))

  cases R with

  | zero =>
      have hsetup :=
        pointAddSetup_zero_correct
          pointReg outReg workStart
          (xC := xC) (yC := yC)
          st hpointLength hnodup hpoint hclean

      change
        setupState (pointAddInfinityFlag workStart) = true ∧
          setupState (pointAddGenericFlag workStart) = false ∧
          setupState (pointAddDoubleFlag workStart) = false ∧
          Clean (pointAddBranchWork workStart) setupState
        at hsetup

      rcases hsetup with
        ⟨hinfinity, hgeneric, hdouble, hbranchClean⟩

      have hbranches :=
        pointAddBranches_infinity_correct
          workStart hC setupState
          hinfinity hgeneric hdouble hbranchClean

      simpa only [affineAdd_zero_left] using hbranches

  | some hR =>
      rename_i xR yR

      have hsetup :=
        pointAddSetup_some_correct
          pointReg outReg workStart
          (xC := xC) (yC := yC)
          hR st
          hpointLength hnodup hpoint hclean

      change
        regValue (pointAddX workStart) setupState = xR.val ∧
          regValue (pointAddY workStart) setupState = yR.val ∧
          setupState (pointAddInfinityFlag workStart) = false ∧
          setupState (pointAddGenericFlag workStart) =
            decide (xR ≠ xC) ∧
          setupState (pointAddDoubleFlag workStart) =
            decide (xR = xC ∧ yR ≠ -yC) ∧
          Clean (pointAddBranchWork workStart) setupState
        at hsetup

      rcases hsetup with
        ⟨hxReg, hyReg, hinfinity,
         hgeneric, hdouble, hbranchClean⟩

      by_cases hx : xR = xC

      · by_cases hinv : yR = -yC

        ·
          have hgeneric' :
              setupState
                (pointAddGenericFlag workStart) = false := by
            simpa [hx] using hgeneric

          have hdouble' :
              setupState
                (pointAddDoubleFlag workStart) = false := by
            simpa [hx, hinv] using hdouble

          have hbranches :=
            pointAddBranches_inverse_correct
              workStart hC setupState
              hinfinity hgeneric' hdouble' hbranchClean

          rw [affineAdd_inverse hR hC hx hinv]

          exact hbranches

        ·
          have hgeneric' :
              setupState
                (pointAddGenericFlag workStart) = false := by
            simpa [hx] using hgeneric

          have hdouble' :
              setupState
                (pointAddDoubleFlag workStart) = true := by
            simpa [hx, hinv] using hdouble

          have hbranches :=
            pointAddBranches_double_correct
              workStart hR hC hx hinv setupState
              hxReg hyReg
              hinfinity hgeneric' hdouble'
              hbranchClean

          have haff :
              affineAdd (.some hR) (.some hC) =
                doublePoint hR
                  (self_not_inverse_of_x_eq_of_not_inverse
                    hR hC hx hinv) := by
            unfold affineAdd
            simp [hx, hinv]

          rw [haff]

          exact hbranches

      ·
        have hgeneric' :
            setupState
              (pointAddGenericFlag workStart) = true := by
          simpa [hx] using hgeneric

        have hdouble' :
            setupState
              (pointAddDoubleFlag workStart) = false := by
          simpa [hx] using hdouble

        have hbranches :=
          pointAddBranches_generic_correct
            workStart hR hC hx setupState
            hxReg hyReg
            hinfinity hgeneric' hdouble'
            hbranchClean

        rw [affineAdd_generic hR hC hx]

        exact hbranches

/--
Structural facts needed to reverse `pointAddFiniteCompute`.

Unlike `pointAddFiniteCompute_correct`, this theorem contains no curve
arithmetic.  Its proof is obtained by composing the `HPFree`,
`wellFormed`, and `usesOnly` theorems for:

* `copyReg`,
* `loadConst`,
* `zeroFlag`,
* `equalFlag`,
* `fieldAdd`,
* `fieldSub`,
* `fieldMul`,
* `fieldInv`,
* `controlledCopyReg`.

The last conjunct records that `selected` really belongs to the declared
PointAdd workspace.
-/
theorem pointAddFiniteCompute_structural
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup) :
    let compute :=
      pointAddFiniteCompute pointReg workStart hC
    Classical.HPFree compute ∧
      CircuitWellFormed compute ∧
      CircuitUsesOnly
        (pointReg ++ pointAddWork workStart)
        compute ∧
      (∀ w ∈ pointAddSelected workStart,
        w ∈ pointAddWork workStart) := by
  sorry

/--
Generic Bennett copy-out lemma.

Suppose `compute`

    |input⟩ |0_work⟩
        ↦
    |history⟩

and the register `src`, which lies inside `work`, contains `value` after
the forward computation.

If we do

    compute;
    copyReg src out;
    compute.reverse

then the forward history is erased while the copied value survives in
the disjoint public output register.

Hence the complete state is exactly

    writeReg out value st.

This theorem is completely independent of elliptic curves.
-/
theorem bennett_copyReg_eq_writeReg
    (compute : Circuit)
    (input src out work : List Wire)
    (st : BasisState)
    (value : Nat)
    (hfree : Classical.HPFree compute)
    (hwf : CircuitWellFormed compute)
    (huses :
      CircuitUsesOnly (input ++ work) compute)
    (hsrc :
      ∀ w ∈ src, w ∈ work)
    (hnodup :
      (input ++ out ++ work).Nodup)
    (hlen :
      out.length = src.length)
    (hclean :
      Clean out st)
    (hvalue :
      regValue src (Classical.run compute st) = value)
    (hbound :
      value < 2 ^ out.length) :
    Classical.run
        (circuit! {
          compute;
          Arithmetic.copyReg src out;
          compute.reverse
        })
        st =
      writeReg out value st := by
  sorry

/-! -------------------------------------------------------------------------
    Final PointAdd correctness
------------------------------------------------------------------------- -/

theorem pointAdd_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C R : Point)
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (houtLength :
      outReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat R)
    (hclean :
      Clean (outReg ++ pointAddWork workStart) st) :
    Classical.run
        (pointAdd pointReg outReg workStart C)
        st =
      writeReg
        outReg
        (encode (R + C)).val
        st := by
  cases C with
  | zero =>
      have hlen : outReg.length = pointReg.length := by
        calc
          outReg.length = pointWidth := houtLength
          _ = pointReg.length := hpointLength.symm

      have hcleanOut : Clean outReg st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_left _ hw)

      have hbound : encodeNat R < 2 ^ outReg.length := by
        rw [houtLength]
        exact encodeNat_lt R

      have hcopy :=
        copyReg_eq_writeReg_of_value
          pointReg
          outReg
          (pointAddWork workStart)
          st
          (encodeNat R)
          hlen
          hnodup
          hcleanOut
          hpoint
          hbound

      change
        Classical.run (Arithmetic.copyReg pointReg outReg) st =
          writeReg outReg (encode (R + 0)).val st
      have henc : (encode (R + 0)).val = encodeNat R := by
        rw [add_zero, encode_val]
      rw [henc]
      exact hcopy

  | some hC =>
      rename_i xC yC

      let compute :=
        pointAddFiniteCompute pointReg workStart hC

      have hcleanWork :
          Clean (pointAddWork workStart) st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_right outReg hw)

      have hcleanOut : Clean outReg st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_left _ hw)

      have hforward :
          regValue
              (pointAddSelected workStart)
              (Classical.run compute st) =
            encodeNat (affineAdd R (.some hC)) := by
        simpa [compute] using
          pointAddFiniteCompute_correct
            pointReg
            outReg
            workStart
            hC
            R
            st
            hpointLength
            hnodup
            hpoint
            hcleanWork

      obtain ⟨hfree, hwf, huses, hselected⟩ :=
        pointAddFiniteCompute_structural
          pointReg
          outReg
          workStart
          hC
          hnodup

      have hlen :
          outReg.length =
            (pointAddSelected workStart).length := by
        simp [pointAddSelected, houtLength, pointWidth]

      have hbound :
          encodeNat (affineAdd R (.some hC)) <
            2 ^ outReg.length := by
        rw [houtLength]
        exact encodeNat_lt (affineAdd R (.some hC))

      have hbennett :=
        bennett_copyReg_eq_writeReg
          compute
          pointReg
          (pointAddSelected workStart)
          outReg
          (pointAddWork workStart)
          st
          (encodeNat (affineAdd R (.some hC)))
          hfree
          hwf
          huses
          hselected
          hnodup
          hlen
          hcleanOut
          hforward
          hbound

      rw [affineAdd_correct] at hbennett
      change
        Classical.run
            (circuit! {
              compute;
              Arithmetic.copyReg
                (pointAddSelected workStart)
                outReg;
              compute.reverse
            })
            st =
          writeReg outReg (encode (R + .some hC)).val st
      have henc :
          (encode (R + .some hC)).val =
            encodeNat (R + .some hC) := by
        rw [encode_val]
      rw [henc]
      simpa only [compute] using hbennett

end Secp256k1
end ShorECDLP
