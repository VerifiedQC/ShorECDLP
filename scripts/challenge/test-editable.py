#!/usr/bin/env python3
"""Boundary regression tests; no Lean installation required."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

CHECK = Path(__file__).with_name('check-editable.py').resolve()
ALLOW = 'ShorECDLP/Submission/Entrant'


class BoundaryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.trusted = Path(self.tmp.name) / 'trusted'
        self.source = Path(self.tmp.name) / 'source'
        self.trusted.mkdir()
        self.git(self.trusted, 'init', '-q')
        (self.trusted / ALLOW).mkdir(parents=True)
        (self.trusted / ALLOW / 'Main.lean').write_text('original entrant\n')
        (self.trusted / 'Official.lean').write_text('protected theorem\n')
        (self.trusted / '.gitignore').write_text('ignored\n.lake/\n')
        self.git(self.trusted, 'add', '.')
        self.tree = self.git(self.trusted, 'write-tree').strip()
        shutil.copytree(self.trusted, self.source, ignore=shutil.ignore_patterns('.git'))

    def git(self, repo, *args):
        return subprocess.check_output(['git', '-C', str(repo), *args], text=True)

    def runcheck(self, expected=0, extra=(), env=None):
        result = subprocess.run([sys.executable, str(CHECK), '--repo', str(self.source),
                                 '--trusted-repo', str(self.trusted), '--trusted-tree', self.tree,
                                 *extra], capture_output=True, text=True, env=env)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)

    def test_clean_and_editable_changes(self):
        self.runcheck()
        (self.source / ALLOW / 'Main.lean').unlink()
        new = self.source / ALLOW / 'nested'
        new.mkdir()
        (new / 'new.lean').write_text('candidate\n')
        (new / 'new.lean').chmod(0o755)
        self.runcheck()

    def test_protected_content_with_same_size_and_mtime(self):
        path = self.source / 'Official.lean'
        info = path.stat()
        path.write_text('x' * info.st_size)
        os.utime(path, ns=(info.st_atime_ns, info.st_mtime_ns))
        self.runcheck(1)

    def test_protected_delete(self):
        (self.source / 'Official.lean').unlink()
        self.runcheck(1)

    def test_protected_mode(self):
        (self.source / 'Official.lean').chmod(0o755)
        self.runcheck(1)

    def test_extra_ignored_and_build_cache(self):
        for name in ('extra', 'ignored', '.lake/cache'):
            with self.subTest(name=name):
                path = self.source / name
                path.parent.mkdir(exist_ok=True)
                path.write_text('injection')
                self.runcheck(1)
                path.unlink()
        (self.source / '.lake').rmdir()
        self.runcheck()

    def test_prefix_confusion(self):
        path = self.source / (ALLOW + 'Evil')
        path.mkdir()
        (path / 'Main.lean').write_text('injection')
        self.runcheck(1)

    def test_symlinks(self):
        for name in ('Official.lean', ALLOW + '/Main.lean', ALLOW):
            with self.subTest(name=name):
                path = self.source / name
                saved = path.with_name(path.name + '.saved')
                path.rename(saved)
                path.symlink_to(saved, target_is_directory=saved.is_dir())
                self.runcheck(1)
                path.unlink()
                saved.rename(path)

    def test_special_file(self):
        os.mkfifo(self.source / ALLOW / 'fifo')
        self.runcheck(1)

    def test_nested_git(self):
        (self.source / ALLOW / '.git').mkdir()
        self.runcheck(1)

    def test_fixed_pin_and_allow_required(self):
        for extra in (('--trusted-tree', 'HEAD'), ('--trusted-tree', self.tree[:8]),
                      ('--allow', 'ShorECDLP'), ('--allow', ALLOW + '/../')):
            with self.subTest(extra=extra):
                self.runcheck(2, extra)
        result = subprocess.run([sys.executable, str(CHECK)], capture_output=True)
        self.assertEqual(result.returncode, 2)

    def test_candidate_index_flags_and_staging_ignored(self):
        self.git(self.source, 'init', '-q')
        self.git(self.source, 'add', '.')
        self.git(self.source, 'update-index', '--assume-unchanged', 'Official.lean')
        (self.source / 'Official.lean').write_text('injected')
        self.runcheck(1)
        self.git(self.source, 'update-index', '--no-assume-unchanged', 'Official.lean')
        self.git(self.source, 'add', '.')
        self.git(self.source, 'update-index', '--skip-worktree', 'Official.lean')
        self.runcheck(1)

    def test_git_environment_is_not_authority(self):
        env = os.environ.copy()
        env.update(GIT_DIR='/missing', GIT_WORK_TREE='/missing',
                   GIT_CONFIG_COUNT='1', GIT_CONFIG_KEY_0='core.fsmonitor',
                   GIT_CONFIG_VALUE_0='false')
        self.runcheck(env=env)
        (self.source / 'Official.lean').write_text('injected')
        self.runcheck(1, env=env)


if __name__ == '__main__':
    unittest.main()
