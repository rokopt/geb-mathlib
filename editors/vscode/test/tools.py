"""Exercise cold, warm and invalidated editor builds without downloading a toolchain."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

LAUNCHER = Path(__file__).resolve().parents[1] / 'tools.py'


class ToolReuse(unittest.TestCase):
    def test_selected_checkout(self):
        with tempfile.TemporaryDirectory(prefix='Geb tools λ ') as tmp:
            root = Path(tmp)
            for name in ('Geb', 'GebHost', 'bootstrap/lean', 'bin', '.lake/build/bin', 'dependency'):
                (root / name).mkdir(parents=True)
            (root / 'lake-manifest.json').write_text(
                '{"packages":[{"type":"path","dir":"dependency"}]}')
            (root / 'lean-toolchain').write_text('toolchain-A')
            for name, script in {
                'lean': 'exit 0',
                'elan': 'command -v lean',
                'lake': '''echo "$*" >> builds
                    if test -e fail; then exit 1; fi
                    test "$1" = build || exit 2
                    shift
                    for tool do
                        cp bin/tool ".lake/build/bin/$tool"
                    done''',
                'tool': 'echo "$*"',
            }.items():
                exe = root / 'bin' / name
                exe.write_text('#!/bin/sh\n' + script + '\n')
                exe.chmod(0o755)
            env = {**os.environ, 'PATH': str(root / 'bin') + os.pathsep + os.environ['PATH']}
            cmd = [sys.executable, str(LAUNCHER), 'run', 'geb-author', 'compile', 'a b']
            def run():
                return subprocess.check_output(cmd, cwd=root, env=env, text=True).strip()
            def count():
                return len((root / 'builds').read_text().splitlines())

            jobs = [subprocess.Popen(cmd, cwd=root, env=env, stdout=subprocess.PIPE, text=True)
                    for _ in range(3)]
            for job in jobs:
                output, _ = job.communicate(timeout=15)
                self.assertEqual((job.returncode, output.strip()), (0, 'compile a b'))
            self.assertEqual(count(), 1)
            (root / 'Program.geb').write_text('(def answer 0)')
            self.assertEqual(run(), 'compile a b')
            self.assertEqual(count(), 1)
            for i, name in enumerate(('GebHost/Compiler.lean', 'lean-toolchain', 'dependency/lib.c')):
                (root / name).write_text('changed')
                run()
                self.assertEqual(count(), i + 2)
            (root / 'GebHost/Compiler.lean').unlink()
            (root / 'fail').touch()
            self.assertNotEqual(subprocess.run(cmd, cwd=root, env=env, capture_output=True).returncode, 0)
            (root / 'fail').unlink()
            run()
            self.assertEqual(count(), 6)
            (root / '.lake/build/bin/geb-author').unlink()
            run()
            self.assertEqual(count(), 7)


if __name__ == '__main__':
    unittest.main()
