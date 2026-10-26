"""Trusted Expr-level acceptance tests, including imported syntax and native overrides."""
import json
import shutil
from pathlib import Path
import subprocess
import tempfile
import gate

PREFIX = '''import ShorECDLP.Submission.Naive.Challenge.NumericCertificate
import ShorECDLP.Challenge.Official
import ShorECDLP.Challenge.ExtendedContract
open ShorECDLP.Challenge ShorECDLP.NaiveChallenge
'''
REAL_CERT = '''theorem certificate : Certificate officialLimits layout entry bounds :=
  have h := naiveRepeatedEntry_numeric_certificate
  { h with
    gateBudget := h.gateBudget.trans (by simp [naiveNumericLimits, officialLimits])
    recordBudget := h.recordBudget.trans (by simp [naiveNumericLimits, officialLimits])
    tableBudget := h.tableBudget.trans (by simp [naiveNumericLimits, officialLimits])
    candidateBudget := h.candidateBudget.trans
      (by simp [naiveNumericLimits, officialLimits, budget55]) }
'''
ENTRY = '''namespace ShorECDLP.Entrant
noncomputable section
def entry : StraightEntry := naiveRepeatedEntry
def layout : DecodeLayout := repeatedDecodeLayout
'''
END = '\nend\nend ShorECDLP.Entrant\n'
MACRO = '''macro_rules
  | `(term| _root_.ShorECDLP.Challenge.Certificate $_ $_ $_ $_) => `(True)
'''
CASES = [
    ('ValidCertificate', PREFIX + ENTRY + 'def bounds : Bounds := naiveNumericBounds\n' + REAL_CERT + END, True),
    ('MacroZeroScore', PREFIX + MACRO + ENTRY +
     'def bounds : Bounds := ⟨0, 0, 0⟩\ntheorem certificate : True := True.intro\n' + END +
     'theorem legacyAccepted : _root_.ShorECDLP.Challenge.Certificate '
     'ShorECDLP.Challenge.officialLimits ShorECDLP.Entrant.layout '
     'ShorECDLP.Entrant.entry ShorECDLP.Entrant.bounds := ShorECDLP.Entrant.certificate\n', False),
    ('AxiomCertificate', PREFIX + ENTRY + 'def bounds : Bounds := ⟨0, 0, 0⟩\n' +
     'axiom certificate : Certificate officialLimits layout entry bounds\n' + END, False),
    ('NativeMetricOverride', PREFIX + '''namespace ShorECDLP.Entrant
def fakeBounds : Bounds := ⟨0, 0, 0⟩
@[implemented_by fakeBounds] def bounds : Bounds := naiveNumericBounds
end ShorECDLP.Entrant
''' + ENTRY + REAL_CERT + END, True),
    ('ValidTighterDiagnostics', PREFIX.replace('Naive.Challenge.NumericCertificate',
        'Naive.Challenge.ExtendedCertificate') + ENTRY +
     'def bounds : Bounds := naiveNumericBounds\n' + REAL_CERT +
     'def extendedBounds : ExtendedBounds := naiveExtendedBounds\n' +
     'theorem extendedCertificate : ExtendedCertificate officialLimits layout entry bounds extendedBounds :=\n'
     '  ⟨certificate, naiveRepeatedEntry_extended_certificate.diagnostics⟩\n' + END, True),
    ('WrongExtendedCertificate', PREFIX + ENTRY + 'def bounds : Bounds := naiveNumericBounds\n' +
     REAL_CERT + 'def extendedBounds : ExtendedBounds := ⟨0, 0⟩\n'
     'theorem extendedCertificate : True := True.intro\n' + END, False),
]


def main():
    lean, env = gate.environment()
    judge = Path(__file__).with_name('judge.lean').resolve()
    for name, source, accepted in CASES:
        with tempfile.TemporaryDirectory(prefix='challenge-judge-regression-') as directory:
            root = Path(directory)
            shutil.copytree(gate.ROOT / '.lake/build/lib/lean', root, dirs_exist_ok=True)
            shutil.rmtree(root / 'ShorECDLP/Submission/Entrant', ignore_errors=True)
            path = root / 'ShorECDLP/Submission/Entrant/Main.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            result = subprocess.run([str(lean), '--root=' + str(root), '-o',
                                     str(path.with_suffix('.olean')), str(path)],
                                    cwd=gate.ROOT, env=env, capture_output=True, text=True, timeout=120)
            if result.returncode:
                raise AssertionError(f'{name}: fixture did not compile\n{result.stdout}\n{result.stderr}')
            replay = gate.replay('ShorECDLP.Submission.Entrant', extra_path=root)
            if replay.returncode:
                raise AssertionError(f'{name}: valid kernel fixture did not replay\n{replay.stdout}\n{replay.stderr}')
            if name == 'NativeMetricOverride':
                runtime_env = env.copy()
                runtime_env['LEAN_PATH'] = str(root) + ':' + env['LEAN_PATH']
                native = subprocess.run([str(lean), '--stdin'],
                    input='import ShorECDLP.Submission.Entrant.Main\n#eval ShorECDLP.Entrant.bounds.tModel\n',
                    cwd=gate.ROOT, env=runtime_env, capture_output=True, text=True, timeout=120)
                if native.returncode or native.stdout.strip() != '0':
                    raise AssertionError(f'native override fixture not active: {native.stdout} {native.stderr}')
            result = subprocess.run([str(lean), '--run', str(judge), str(root)],
                                    cwd=gate.ROOT, env=env, capture_output=True, text=True, timeout=120)
            if accepted:
                if result.returncode:
                    raise AssertionError(f'{name}: rejected\n{result.stdout}\n{result.stderr}')
                data = json.loads(result.stdout)
                assert data['accepted'] is True
                assert data['score_tModel'] == 8918039383771648, data
                assert data['qubits'] == 206624, data
                assert data['measurements'] == 5385536, data
                assert data['toffoli_derived_upper_bound'] == 1274005626253092, data
                assert data['nonClifford_derived_upper_bound'] == (3620864829523968 if name == 'ValidTighterDiagnostics' else 4000000000000000), data
            else:
                expected = 'wrong kernel type' if name in ('MacroZeroScore', 'WrongExtendedCertificate') else 'non-allowlisted axiom'
                if result.returncode != 1 or expected not in result.stderr:
                    raise AssertionError(f'{name}: wrong rejection\n{result.stdout}\n{result.stderr}')
            print(f'{name}: kernel acceptance check ' + ('accepted true metrics' if accepted else 'rejected'))


if __name__ == '__main__':
    main()
