import Lean

/-! Run ONLY from the evaluator's protected installation with trusted dependencies.
The optional path argument is an evaluator-created overlay containing only
Entrant compiled artifacts. No entrant is imported while this file elaborates.
Runtime imports do not load extensions or execute initializers. -/
open Lean

private def checked (result : Except Kernel.Exception α) : IO α :=
  match result with
  | .ok a => pure a
  | .error _ => throw <| IO.userError "REJECT: kernel check or reduction failed"

private def checkType (env : Environment) (value expected : Expr) : IO Unit := do
  let actual ← checked (Kernel.check env {} value)
  let _ ← checked (Kernel.check env {} expected)
  unless ← checked (Kernel.isDefEq env {} actual expected) do
    throw <| IO.userError "REJECT: certificate or entry has wrong kernel type"

private def checkAxioms (env : Environment) (name : Name) : IO Unit := do
  let (_, state) := ((CollectAxioms.collect name).run env).run {}
  for ax in state.axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throw <| IO.userError s!"REJECT: non-allowlisted axiom {ax}"

private partial def natValue (env : Environment) (value : Expr) : IO Nat := do
  match ← checked (Kernel.whnf env {} value) with
  | .lit (.natVal n) => pure n
  | .const ``Nat.zero _ => pure 0
  | .app (.const ``Nat.succ _) n => return (← natValue env n) + 1
  | _ => throw <| IO.userError "REJECT: metric did not kernel-reduce to a natural number"

private def field (name : Name) (arg : Expr) : Expr := mkApp (mkConst name) arg

unsafe def main (args : List String) : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    match args with
    | [] => pure ()
    | [overlay] => searchPathRef.modify (System.FilePath.mk overlay :: ·)
    | _ => throw <| IO.userError "usage: trusted judge.lean [sealed entrant artifact overlay]"
    let env ← importModules #[{ module := `ShorECDLP.Judge.Main },
      { module := `ShorECDLP.Submission.Entrant.Main }] {} (loadExts := false)
    let entry := mkConst `ShorECDLP.Entrant.entry
    let layout := mkConst `ShorECDLP.Entrant.layout
    let bounds := mkConst `ShorECDLP.Entrant.bounds
    checkType env entry (mkConst `ShorECDLP.Challenge.StraightEntry)
    checkType env layout (mkConst `ShorECDLP.Challenge.DecodeLayout)
    checkType env bounds (mkConst `ShorECDLP.Challenge.Bounds)
    let target := mkAppN (mkConst `ShorECDLP.Judge.acceptance) #[entry, layout, bounds]
    checkType env (mkConst `ShorECDLP.Entrant.certificate) target
    for name in [`ShorECDLP.Entrant.entry, `ShorECDLP.Entrant.layout,
        `ShorECDLP.Entrant.bounds, `ShorECDLP.Entrant.certificate] do
      checkAxioms env name
    let t ← natValue env (field `ShorECDLP.Challenge.Bounds.tModel bounds)
    let qubits ← natValue env (field `ShorECDLP.Challenge.Bounds.qubits bounds)
    let measurements ← natValue env (field `ShorECDLP.Challenge.Bounds.measurements bounds)
    let limits := mkConst `ShorECDLP.Challenge.officialLimits
    let slots ← natValue env (field `ShorECDLP.Challenge.Limits.gateSlots limits)
    let rows ← natValue env (field `ShorECDLP.Challenge.Limits.coefficientRows limits)
    let candidates ← natValue env (field `ShorECDLP.Challenge.Limits.candidateChecks limits)
    let derived := mkAppN (mkConst `ShorECDLP.Judge.derive_diagnostics)
      #[entry, layout, bounds, mkConst `ShorECDLP.Entrant.certificate]
    let derivedBounds := mkAppN (mkConst `ShorECDLP.Challenge.ExtendedBounds.mk)
      #[mkNatLit (t / 7), mkNatLit slots]
    checkType env derived
      (mkAppN (mkConst `ShorECDLP.Judge.extendedAcceptance) #[entry, layout, bounds, derivedBounds])
    let mut toffoli := t / 7
    let mut nonClifford := slots
    let extraName := `ShorECDLP.Entrant.extendedBounds
    let certName := `ShorECDLP.Entrant.extendedCertificate
    if (env.find? extraName).isSome || (env.find? certName).isSome then
      let extra := mkConst extraName
      checkType env extra (mkConst `ShorECDLP.Challenge.ExtendedBounds)
      checkType env (mkConst certName)
        (mkAppN (mkConst `ShorECDLP.Judge.extendedAcceptance) #[entry, layout, bounds, extra])
      checkAxioms env extraName
      checkAxioms env certName
      toffoli ← natValue env (field `ShorECDLP.Challenge.ExtendedBounds.toffoli extra)
      nonClifford ← natValue env (field `ShorECDLP.Challenge.ExtendedBounds.nonClifford extra)
    let report := Json.mkObj [
      ("accepted", toJson true), ("score_tModel", toJson t),
      ("qubits", toJson qubits), ("measurements", toJson measurements),
      ("toffoli_derived_upper_bound", toJson toffoli),
      ("nonClifford_derived_upper_bound", toJson nonClifford),
      ("gateSlots_limit", toJson slots), ("coefficientRows_limit", toJson rows),
      ("candidateChecks_limit", toJson candidates)]
    IO.println report.compress
    return (0 : UInt32)
  catch e =>
    IO.eprintln e.toString
    return (1 : UInt32)
