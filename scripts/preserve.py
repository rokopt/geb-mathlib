#!/usr/bin/env python3
"""Preserve Geb developments and compare them through the existing host commands.

Records are immutable directories. Creation stages every artifact before publishing
the directory; verification reads no current source and runs no compiler. Checking
and comparison use the current host and replay saved certificates without searching.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
FORMAT = "geb-development/v1"
TOOLS = ("geb-author", "geb-compile", "geb-defs", "geb-kernel")
ARTIFACTS = {
    "program.img", "program.defs", "proof.cert", "compiler.img", "authoring.lean.txt",
    "compiler.lean.txt",
    "lean-toolchain", "lake-manifest.json", "host.json",
}


def digest(path):
    with path.open("rb") as stream:
        h = hashlib.sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
        return h.hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def relative(name):
    if not isinstance(name, str):
        raise ValueError("record path is not a string")
    p = PurePosixPath(name)
    if not p.parts or p.is_absolute() or ".." in p.parts or str(p) != name:
        raise ValueError(f"not a relative record path: {name!r}")
    return Path(*p.parts)


def copy(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        raise ValueError(f"duplicate snapshot path: {target}")
    shutil.copyfile(source, target)


def command(tool, *args):
    return subprocess.run(
        [str(ROOT / ".lake/build/bin" / tool), *map(str, args)],
        check=True, stdout=subprocess.PIPE, text=True, encoding="utf-8",
    ).stdout


def build():
    subprocess.run(["lake", "build", *TOOLS], cwd=ROOT, check=True)


def sources(manifest):
    # The host parses the manifest, including layers and quoted layer names.
    names = command("geb-kernel", "sources", manifest).splitlines()
    for name in names:
        relative(name)
    if not names or len(set(names)) != len(names):
        raise ValueError("the manifest has no sources or repeats a source")
    return names


def snapshot(manifest, proofs, target):
    saved = target / "project" / manifest.name
    copy(manifest, saved)
    names = sources(saved)
    for name in names:
        copy(manifest.parent / name, target / "project" / relative(name))
    proof = target / "proofs" / proofs.name
    copy(proofs, proof)
    return saved, proof, names


def documents(manifest, proofs, names, target):
    pairs = [(manifest, Path("manifest.csexp")), (proofs, Path("proofs.csexp"))]
    pairs += [(manifest.parent / name, Path("sources") / (name + ".csexp")) for name in names]
    for source, name in pairs:
        out = target / name
        out.parent.mkdir(parents=True, exist_ok=True)
        command("geb-author", "convert", "canonical", manifest, source, out)


def compile_program(manifest, target):
    command("geb-author", "compile", manifest, target / "program.img")
    command("geb-defs", target / "program.img", target / "program.defs")


def inventory(root):
    if root.is_symlink() or not root.is_dir():
        raise ValueError("a record must be a directory, not a symbolic link")
    files = {}
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"symbolic link in record: {path}")
        if path.is_file():
            name = path.relative_to(root).as_posix()
            if name != "record.json":
                files[name] = digest(path)
        elif not path.is_dir():
            raise ValueError(f"not a regular record file: {path}")
    return files


def unique_fields(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate record field: {key}")
        result[key] = value
    return result


def verify(root):
    actual = inventory(root)
    info = json.loads((root / "record.json").read_text(encoding="utf-8"),
                      object_pairs_hook=unique_fields)
    if not isinstance(info, dict) or info.get("format") != FORMAT:
        raise ValueError("unsupported development record format")
    if set(info) != {"format", "manifest", "proofs", "sources", "files"}:
        raise ValueError("unexpected development record fields")
    manifest, proofs = relative(info["manifest"]), relative(info["proofs"])
    if manifest.parent != Path("project") or proofs.parent != Path("proofs"):
        raise ValueError("the record's manifest or proofs are outside their snapshot")
    names = info["sources"]
    if not isinstance(names, list) or not names or not all(isinstance(s, str) for s in names):
        raise ValueError("invalid record source list")
    if len(set(names)) != len(names):
        raise ValueError("duplicate record source")
    required = ARTIFACTS | {manifest.as_posix(), proofs.as_posix(),
                            "documents/manifest.csexp", "documents/proofs.csexp"}
    for name in names:
        relative(name)
        required |= {"project/" + name, "documents/sources/" + name + ".csexp"}
    expected = info["files"]
    if not isinstance(expected, dict) or not required <= expected.keys():
        raise ValueError("the record omits a required artifact")
    for name, checksum in expected.items():
        relative(name)
        if (not isinstance(checksum, str) or len(checksum) != 64
                or any(c not in "0123456789abcdef" for c in checksum)):
            raise ValueError(f"invalid SHA-256 digest: {name}")
    if actual != expected:
        changed = sorted(k for k in actual.keys() | expected.keys()
                         if actual.get(k) != expected.get(k))
        raise ValueError("record integrity differs: " + ", ".join(changed))
    return info


def tooling(target):
    for name in ("lean-toolchain", "lake-manifest.json"):
        copy(ROOT / name, target / name)
    copy(ROOT / "bootstrap/compiler.img", target / "compiler.img")
    copy(ROOT / "bootstrap/lean/GebBoot.lean", target / "compiler.lean.txt")
    # Retain the Geb source closures and the proof runner as emitted Lean, the
    # representation used by the bootstrap's existing authoring workflow.
    for manifest in ("bootstrap/stage1.manifest", "bootstrap/authoring.manifest"):
        path = ROOT / manifest
        inputs = [path, *(path.parent / name for name in sources(path))]
        for source in inputs:
            dest = target / "tooling" / source.relative_to(ROOT)
            if not dest.exists():
                copy(source, dest)
    copy(ROOT / "bootstrap/lean/GebMirror/Authoring.lean", target / "authoring.lean.txt")
    pending, seen = ["GebMirror.Authoring"], set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        source = ROOT / "bootstrap/lean" / (module.replace(".", "/") + ".lean")
        # Emitted modules have one import per line. Preserve the generated modules
        # that the runner imports, without regenerating them with another compiler.
        pending.extend(re.findall(r"(?m)^(?:(?:public|meta) )*import (GebMirror\.[\w.]+)",
                                  source.read_text(encoding="utf-8")))
        if module != "GebMirror.Authoring":
            copy(source, target / "tooling" / (source.relative_to(ROOT).as_posix() + ".txt"))
    # Native hosts are identified, not copied: their executable images are platform-specific.
    write_json(target / "host.json", {
        "format": "geb-host/v1",
        "executables": {name: digest(ROOT / ".lake/build/bin" / name) for name in TOOLS},
    })


def record(manifest, proofs, destination, certificate):
    if destination.exists() or destination.is_symlink():
        raise ValueError("record already exists; choose a new directory to retain the old record")
    destination.parent.mkdir(parents=True, exist_ok=True)
    # A rename on the same filesystem publishes all artifacts together.
    with tempfile.TemporaryDirectory(prefix=".geb-record-", dir=destination.parent) as directory:
        staged = Path(directory) / "record"
        staged.mkdir()
        saved, proof, names = snapshot(manifest, proofs, staged)
        documents(saved, proof, names, staged / "documents")
        compile_program(saved, staged)
        if certificate is None:
            command("geb-author", "prove", saved, proof, staged / "proof.cert")
        else:
            copy(certificate, staged / "proof.cert")
        command("geb-author", "replay", saved, proof, staged / "proof.cert")
        tooling(staged)
        write_json(staged / "record.json", {
            "format": FORMAT,
            "manifest": saved.relative_to(staged).as_posix(),
            "proofs": proof.relative_to(staged).as_posix(),
            "sources": names,
            "files": inventory(staged),
        })
        verify(staged)
        if destination.exists() or destination.is_symlink():
            raise ValueError("record appeared while staging; nothing replaced")
        staged.rename(destination)
    print(f"{destination}: recorded; examples checked and certificate replayed")


def check(root, info, manifest=None, proofs=None):
    compare = manifest is not None
    manifest = manifest or root / info["manifest"]
    proofs = proofs or root / info["proofs"]
    with tempfile.TemporaryDirectory(prefix="geb-preserve-") as directory:
        target = Path(directory)
        # Check a snapshot so every command observes the same source bytes.
        saved, proof, names = snapshot(manifest, proofs, target)
        documents(saved, proof, names, target / "documents")
        docs_equal = inventory(target / "documents") == inventory(root / "documents")
        if not compare and (names != info["sources"] or not docs_equal):
            raise ValueError("the current reader does not reproduce the recorded documents")
        compile_program(saved, target)
        for name in ("program.img", "program.defs"):
            if (target / name).read_bytes() != (root / name).read_bytes():
                raise ValueError(f"{name} differs: compilation changed; the record was not updated")
        command("geb-author", "replay", saved, proof, root / "proof.cert")
    status = "unchanged" if docs_equal else "changed"
    print(f"{root}: documents {status}; checked core unchanged; saved certificate replayed")


def main():
    os.environ.setdefault("LEAN_NUM_THREADS", "4")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true",
                        help="use executables already built in this checkout")
    actions = parser.add_subparsers(dest="action", required=True)
    create = actions.add_parser("record", help="create a new immutable development record")
    create.add_argument("manifest", type=Path)
    create.add_argument("proofs", type=Path)
    create.add_argument("record", type=Path)
    create.add_argument("--certificate", type=Path,
                        help="replay this certificate instead of running proof search")
    for name, help_text in (
        ("verify", "verify the record's file inventory and hashes without building"),
        ("check", "recompile archived sources and replay their saved certificate"),
        ("compare", "compare current sources with a record; allow documentation changes"),
    ):
        action = actions.add_parser(name, help=help_text)
        action.add_argument("record", type=Path)
        if name == "compare":
            action.add_argument("manifest", type=Path)
            action.add_argument("proofs", type=Path)
    args = parser.parse_args()
    try:
        if args.action == "record":
            if args.record.exists() or args.record.is_symlink():
                raise ValueError("record already exists; choose a new directory")
            if not args.no_build:
                build()
            record(args.manifest.absolute(), args.proofs.absolute(), args.record.absolute(),
                   args.certificate.absolute() if args.certificate else None)
        else:
            root = args.record.absolute()
            info = verify(root)
            if args.action == "verify":
                print(f"{root}: record integrity verified; no semantic check performed")
            else:
                if not args.no_build:
                    build()
                if args.action == "compare":
                    check(root, info, args.manifest.absolute(), args.proofs.absolute())
                else:
                    check(root, info)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"preserve: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
