#!/usr/bin/env python3
"""Own benign fixtures only. This is not a sandbox for arbitrary submissions."""
from pathlib import Path
import subprocess
import tempfile
import gate

PREFIX = "import ShorECDLP.Challenge.Contract\n"
ENTRY = "_root_.ShorECDLP.Challenge.StraightEntry"
LAYOUT = "_root_.ShorECDLP.Challenge.DecodeLayout"
COORDINATE_COPY = 'open ShorECDLP.Challenge\n\ndef copyCoordinateBits : (n start : Nat) → Straight 1 start (start+n)\n  | 0, start => by simpa using (Straight.done : Straight 1 start start)\n  | n+1, start => .gate (.whenBit ⟨0, if n < 256 then .x else .y, Fin.ofNat 256 n⟩ true (.X n))\n      (.measure n (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using copyCoordinateBits n (start+1)))\n\ndef copiedEntry : StraightEntry := ⟨[⟨⟨0, by decide⟩,⟨1, by decide⟩⟩],512,copyCoordinateBits 512 0⟩\n'
CASES = {
    "Valid": (f"def submitted : {ENTRY} := ⟨[], 0, .done⟩\n", ENTRY, True),
    "EditableCounter": (
        f"def submitted : {ENTRY} := {{ coefficients := [], finalCursor := 0, program := .done, counter := 0 }}\n",
        ENTRY, False),
    "DecoderReadsQ": (
        "def submitted := fun (Q : ShorECDLP.Secp256k1.Point) => Q\n", LAYOUT, False),
    "GeneratorReadsQ": (
        f"def submitted := fun (_Q : ShorECDLP.Secp256k1.Point) => (⟨[], 0, .done⟩ : {ENTRY})\n",
        ENTRY, False),
    "ValidCoordinateCopy": (COORDINATE_COPY + f"def submitted : {ENTRY} := copiedEntry\n", ENTRY, True),
    "CopiedCoordinatesDecoder": (
        COORDINATE_COPY + "noncomputable def submitted := fun (_history : List Bool) =>\n"
        "  Classical.choose (show ∃ d : Nat, d = 0 from ⟨0, rfl⟩)\n", LAYOUT, False),
    "BranchLookup": (
        f"def submitted : {ENTRY} := ⟨[], 1, .measure 0 .done .done⟩\n", ENTRY, False),
    "FutureRecord": (
        f"def submitted : {ENTRY} := ⟨[], 0, .recordGate ⟨0, by omega⟩ true (.X 0) .done⟩\n",
        ENTRY, False),
    "NamespaceShadow": (
        "namespace Entrant.ShorECDLP.Challenge\n"
        "abbrev StraightEntry := Nat\n"
        "end Entrant.ShorECDLP.Challenge\n"
        "open Entrant\n"
        "def submitted : Entrant.ShorECDLP.Challenge.StraightEntry := 0\n", ENTRY, False),
    "FalseScore": (
        "def submitted : (ShorECDLP.Challenge.resources\n"
        "  (.unitary (List.replicate 7 (.P .forward 3 0)) .done)).tModel = 0 := by decide\n",
        "(ShorECDLP.Challenge.resources (.unitary (List.replicate 7 (.P .forward 3 0)) .done)).tModel = 0", False),
}
FORGED = """import Lean
set_option debug.skipKernelTC true
open Lean Elab Command
elab "forgeFalse" : command => do
  liftCoreM <| addDecl (.thmDecl {
    name := `forgedFalse
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro })
forgeFalse
"""

def main():
    lean, env = gate.environment()
    with tempfile.TemporaryDirectory(prefix="challenge-regressions-") as directory:
        root = Path(directory)
        for name, (body, expected, accept) in CASES.items():
            # The test-owned wrapper uses a fully qualified protected type.
            source = PREFIX + body + f"\ndef checked : {expected} := submitted\n"
            gate.reject_disabled_kernel(source)
            path = root / f"{name}.lean"
            path.write_text(source)
            result = subprocess.run(
                [str(lean), "--root=" + str(root), "-o", str(root / f"{name}.olean"), str(path)],
                cwd=gate.ROOT, env=env, text=True, capture_output=True, timeout=120)
            if (result.returncode == 0) != accept:
                raise AssertionError(f"{name}: unexpected compiler result\n{result.stdout}\n{result.stderr}")
            if not accept and (result.returncode != 1 or "error:" not in result.stdout):
                raise AssertionError(f"{name}: rejection was not a Lean diagnostic: {result.stdout} {result.stderr}")
            if accept:
                replay = gate.replay(name, extra_path=root)
                if replay.returncode:
                    raise AssertionError(f"{name}: replay failed\n{replay.stderr}")
            print(f"{name}: {'accepted + replayed' if accept else 'rejected'}", flush=True)
        # Check the explicit policy separately from the independent kernel.
        try:
            gate.reject_disabled_kernel(FORGED)
        except ValueError:
            print("SkipKernelTC: source policy rejected", flush=True)
        else:
            raise AssertionError("kernel-disable policy did not reject fixture")
        # Deliberately bypass the text policy for this known, local fixture:
        # prove that replay catches the actual forged .olean, not just a string.
        forged = root / "Forged.lean"
        forged.write_text(FORGED)
        result = subprocess.run(
            [str(lean), "--root=" + str(root), "-o", str(root / "Forged.olean"), str(forged)],
            cwd=gate.ROOT, env=env, text=True, capture_output=True, timeout=120)
        if result.returncode:
            raise AssertionError("forge fixture did not exercise skipped kernel checking:\n" + result.stdout + result.stderr)
        replay = gate.replay("Forged", extra_path=root)
        if replay.returncode == 0:
            raise AssertionError("independent replay accepted forged False")
        if "leanchecker found a problem" not in replay.stderr:
            raise AssertionError("replay failed for an unrelated reason:\n" + replay.stderr)
        print("Forged artifact: independent kernel replay rejected", flush=True)

if __name__ == "__main__":
    main()
