"""Run the selected checkout's Lake tools, reusing a successful build across editor tasks."""
from contextlib import closing
import hashlib
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import sys

TOOLS = {"geb-author", "geb-compile", "geb-defs", "geb-fmt", "geb-kernel"}


def identity(st):
    return st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns


def inputs():
    """Fingerprint the host sources, native package inputs, build configuration and toolchain."""
    digest = hashlib.sha256()

    def add(path, stat=None):
        st = stat or os.stat(path)
        digest.update(os.fsencode(path) + b'\0')
        digest.update(repr(identity(st)).encode() + b'\0')

    def tree(root, ancestors=()):
        # Follow linked source directories as Lake does, stopping at directory cycles.
        st = os.stat(root)
        key = (st.st_dev, st.st_ino)
        if key in ancestors:
            return
        with os.scandir(root) as entries:
            for entry in sorted(entries, key=lambda e: e.name):
                if entry.name in {'.git', '.jj', '.lake', 'node_modules'}:
                    continue
                if entry.is_dir():
                    tree(entry.path, (*ancestors, key))
                elif entry.is_file():
                    add(entry.path, entry.stat())

    for path in sorted(Path('.').glob('*.lean')):
        add(path)
    for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean'):
        if os.path.isfile(name):
            add(name)
    for root in ('Geb', 'GebHost', 'bootstrap/lean'):
        tree(root)
    manifest = json.loads(Path('lake-manifest.json').read_text())
    for package in manifest['packages']:
        directory = (Path(package['dir']) if package['type'] == 'path' else
                     Path(manifest['packagesDir']) / package['name'].strip('«»'))
        if directory.is_dir():
            tree(directory)
    for name in ('lake', 'lean', 'leanc', 'cc', 'c++'):
        executable = shutil.which(name)
        if executable:
            add(executable)
    if shutil.which('elan'):
        # On a new checkout Lake can install the pinned toolchain during the first build.
        selected = subprocess.run(['elan', 'which', 'lean'], capture_output=True, text=True)
        if selected.returncode == 0:
            lean = Path(selected.stdout.strip())
            add(lean)
            for name in ('lake', 'leanc', 'clang'):
                tool = lean.with_name(name + lean.suffix)
                if tool.is_file():
                    add(tool)
    env = {k: v for k, v in os.environ.items() if k.startswith(('LEAN_', 'LAKE_', 'ELAN_'))
           or k in ('CC', 'CXX', 'CFLAGS', 'LDFLAGS', 'GEB_LOADING', 'GEB_ACCELERATION')}
    digest.update(json.dumps(env, sort_keys=True).encode())
    return digest.hexdigest()


def ensure(tools):
    cache = Path('.lake/geb-editor/tools')
    cache.mkdir(parents=True, exist_ok=True)
    binaries = [Path('.lake/build/bin') / (tool + ('.exe' if os.name == 'nt' else ''))
                for tool in tools]
    # A second window or task can arrive during a build. Its freshness check must see
    # the completed build, or retry it if the builder failed or was terminated.
    with closing(sqlite3.connect(cache / 'builds.sqlite', timeout=3600)) as db, db:
        db.execute('BEGIN IMMEDIATE')
        db.execute('CREATE TABLE IF NOT EXISTS builds (tool TEXT PRIMARY KEY, stamp TEXT NOT NULL)')
        stamps = dict(db.execute('SELECT tool, stamp FROM builds'))
        while True:
            before = inputs()
            pending = [tool for tool, binary in zip(tools, binaries)
                       if not binary.is_file() or stamps.get(tool) != before + repr(identity(binary.stat()))]
            if not pending:
                break
            subprocess.run(['lake', 'build', *pending], stdout=sys.stderr, check=True)
            if inputs() == before:
                db.executemany('INSERT OR REPLACE INTO builds VALUES (?, ?)',
                               [(tool, before + repr(identity(binary.stat())))
                                for tool, binary in zip(tools, binaries) if tool in pending])
                break
    return binaries


def main(args):
    mode, *args = args
    # A program's requests resolve relative paths against its own folder, not the toolchain's.
    directory = None
    if mode == 'run' and args[:1] == ['--directory'] and len(args) >= 2:
        directory, args = args[1], args[2:]
    if mode == 'preserve':
        ensure(['geb-author', 'geb-compile', 'geb-defs', 'geb-kernel'])
        os.execv(sys.executable, [sys.executable, 'scripts/preserve.py', '--no-build', *args])
    targets = args if mode == 'ensure' else args[:1]
    if mode not in ('ensure', 'run') or not targets or not set(targets) <= TOOLS:
        raise ValueError('expected ensure TOOL..., run [--directory DIR] TOOL [ARG...] '
                         'or preserve ACTION [ARG...]')
    binaries = ensure(targets)
    if mode == 'run':
        binary = binaries[0].resolve()
        if directory is not None:
            os.chdir(directory)
        os.execv(binary, [str(binary), *args[1:]])
    print(json.dumps([identity(binary.stat()) for binary in binaries]))


if __name__ == '__main__':
    try:
        main(sys.argv[1:])
    except (OSError, ValueError, sqlite3.Error, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
