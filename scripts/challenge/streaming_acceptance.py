"""Organizer-only Streaming acceptance adapter; no producer proof is synthesized.

Default mode requires the completed ChallengeMigration.StreamingCertificate
exports. Until that module exists this command fails, rather than substituting
an older circuit or assuming the missing certificate. --self-test-naive tests
only this adapter against the shipped Naive entrant; it is NOT Streaming evidence.
"""
import argparse
import json
import subprocess
import tempfile
from pathlib import Path
import gate
from artifacts import stage

SOURCE = '''import ShorECDLP.Submission.«2607_13816».Challenge.StreamingCertificate
import ShorECDLP.Challenge.Official
namespace ShorECDLP.Entrant
open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
def entry : StraightEntry := streamingEntry
def layout : DecodeLayout := streamingDecodeLayout
def bounds : Bounds := streamingBounds
theorem certificate : Certificate officialLimits layout entry bounds := streamingCertificate
end
end ShorECDLP.Entrant
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test-naive', action='store_true')
    args = parser.parse_args()
    source_text = ((gate.ROOT / 'ShorECDLP/Submission/Entrant/Main.lean').read_text()
                   if args.self_test_naive else SOURCE)
    lean, env = gate.environment()
    with tempfile.TemporaryDirectory(prefix='shor-streaming-acceptance-') as directory:
        root = Path(directory)
        candidate = root / 'candidate'
        source = candidate / 'ShorECDLP/Submission/Entrant/Main.lean'
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(source_text)
        artifact = candidate / '.lake/build/lib/lean/ShorECDLP/Submission/Entrant/Main.olean'
        artifact.parent.mkdir(parents=True)
        result = subprocess.run([str(lean), '--root=' + str(candidate), '-o',
                                 str(artifact), str(source)],
                                cwd=gate.ROOT, env=env, capture_output=True, text=True, timeout=120)
        if result.returncode:
            raise RuntimeError('Entrant compilation failed (no acceptance claimed):\n' +
                               result.stdout + result.stderr)
        root = root / 'sealed'
        root.mkdir()
        stage(candidate, root, gate.ROOT / '.lake/build/lib/lean')
        replay = gate.replay('ShorECDLP.Submission.Entrant', extra_path=root)
        if replay.returncode:
            raise RuntimeError(replay.stdout + replay.stderr)
        result = subprocess.run([str(lean), '--run', str(Path(__file__).with_name('judge.lean').resolve()),
                                 str(root)], cwd=gate.ROOT, env=env,
                                capture_output=True, text=True, timeout=600)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        metrics = json.loads(result.stdout)
        if metrics.get('accepted') is not True:
            raise RuntimeError('judge did not report acceptance')
        print(json.dumps({'mode': 'adapter-self-test-naive' if args.self_test_naive else 'streaming',
                          'judge': metrics}, sort_keys=True))


if __name__ == '__main__':
    main()
