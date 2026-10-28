#!/usr/bin/env python3
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent


def load(path):
    spec = importlib.util.spec_from_file_location('boundary_fixture', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class RunnerBoundary(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.candidate = self.root / 'candidate'
        self.candidate.mkdir()

    def test_source_gate_uses_explicit_candidate(self):
        (self.candidate / 'ShorECDLP.lean').write_text('-- debug.skipKernelTC\n')
        result = subprocess.run([sys.executable, str(HERE / 'gate.py'), '--root',
                                 str(self.candidate), '--source-only'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn('skipKernelTC is forbidden', result.stderr)

    def test_print_axioms_runs_in_candidate(self):
        module = load(HERE.parent / 'print-axioms.py')
        roots = []
        def run(*args, **kwargs):
            roots.append(kwargs['cwd'])
            return subprocess.CompletedProcess(args, 0, '', '')
        with mock.patch.dict(os.environ, SHORECDLP_ROOT=str(self.candidate)), \
             mock.patch.object(sys, 'stdin', io.StringIO('import ShorECDLP\n#print axioms ShorECDLP.test\n')), \
             mock.patch.object(module.subprocess, 'run', side_effect=run), \
             contextlib.redirect_stdout(io.StringIO()):
            module.main()
        self.assertTrue(roots)
        self.assertEqual(set(roots), {self.candidate})

    def test_import_layers_block_both_directions(self):
        with mock.patch.dict(os.environ, SHORECDLP_ROOT=str(self.candidate)):
            module = load(HERE.parent / 'check-source.py')
        for relative, source in [
                ('Submission/Entrant/Bad.lean', 'import ShorECDLP.Judge.Main\n'),
                ('Judge/Bad.lean', 'import ShorECDLP.Submission.Entrant.Main\n')]:
            path = self.candidate / 'ShorECDLP' / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            with self.assertRaisesRegex(ValueError, 'forbidden textual import'):
                module.check_textual_layering([path])

    def fixture_artifacts(self):
        prefix = Path('ShorECDLP/Submission/Entrant')
        source = self.candidate / prefix / 'Main.lean'
        source.parent.mkdir(parents=True)
        source.write_text('entrant')
        artifact = self.candidate / '.lake/build/lib/lean' / prefix / 'Main.olean'
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b'entrant-output')
        injected = self.candidate / '.lake/build/lib/lean/ShorECDLP/Challenge/Official.olean'
        injected.parent.mkdir(parents=True)
        injected.write_bytes(b'forged-protected')
        trusted = self.root / 'trusted-lib'
        protected = trusted / 'ShorECDLP/Challenge/Official.olean'
        protected.parent.mkdir(parents=True)
        protected.write_bytes(b'trusted-protected')
        overlay = self.root / 'overlay'
        overlay.mkdir()
        return artifact, trusted, overlay

    def test_only_entrant_outputs_replace_trusted_artifacts(self):
        artifact, trusted, overlay = self.fixture_artifacts()
        module = load(HERE / 'stage-entrant.py')
        self.assertEqual(module.stage(self.candidate, overlay, trusted), 1)
        self.assertEqual((overlay / 'ShorECDLP/Challenge/Official.olean').read_bytes(), b'trusted-protected')
        self.assertEqual((overlay / 'ShorECDLP/Submission/Entrant/Main.olean').read_bytes(), artifact.read_bytes())

    def test_trusted_entrant_is_removed(self):
        artifact, trusted, overlay = self.fixture_artifacts()
        stale = trusted / 'ShorECDLP/Submission/Entrant/Stale.olean'
        stale.parent.mkdir(parents=True)
        stale.write_bytes(b'stale-entrant')
        load(HERE / 'stage-entrant.py').stage(self.candidate, overlay, trusted)
        self.assertFalse((overlay / 'ShorECDLP/Submission/Entrant/Stale.olean').exists())

    def test_nonempty_overlay_rejected_before_copy(self):
        artifact, trusted, overlay = self.fixture_artifacts()
        marker = overlay / 'keep'
        marker.write_bytes(b'keep')
        with self.assertRaisesRegex(ValueError, 'empty runner-owned'):
            load(HERE / 'stage-entrant.py').stage(self.candidate, overlay, trusted)
        self.assertEqual(marker.read_bytes(), b'keep')

    def test_worker_artifact_symlink_rejected(self):
        artifact, trusted, overlay = self.fixture_artifacts()
        artifact.unlink()
        artifact.symlink_to(trusted / 'ShorECDLP/Challenge/Official.olean')
        with self.assertRaisesRegex(ValueError, 'symlink'):
            load(HERE / 'stage-entrant.py').stage(self.candidate, overlay, trusted)


if __name__ == '__main__':
    unittest.main()
