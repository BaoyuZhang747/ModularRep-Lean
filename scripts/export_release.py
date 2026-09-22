"""Export exactly one Git commit as a checked, deterministic source ZIP.

Uncommitted and untracked working-tree files are never included. The export-only
MANIFEST.json records the resolved commit and does not create a commit/hash cycle.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
from check_repository import RELEASE_SCOPE, SourceTree, safe_relative, forbidden_release_path
from verify_release import RELEASE_STATUS, check_release

PREFIX = "ModularRep/"


def git(root: Path, *arguments: str) -> str:
    result = subprocess.run(["git", "-C", str(root), *arguments], check=True,
                            capture_output=True, text=True, encoding="utf-8")
    return result.stdout.strip()


def extract_archive(archive: Path, destination: Path) -> None:
    seen = set()
    with zipfile.ZipFile(archive) as bundle:
        for item in bundle.infolist():
            name = safe_relative(item.filename.rstrip("/"))
            if name.casefold() in seen:
                raise ValueError("Repeated or case-colliding Git archive entry: " + name)
            seen.add(name.casefold())
            if forbidden_release_path(name):
                raise ValueError("Git archive contains private or generated files: " + name)
            mode = item.external_attr >> 16
            if stat.S_ISLNK(mode):
                raise ValueError("Git archive contains a symbolic link: " + name)
            path = destination.joinpath(*name.split("/"))
            if item.is_dir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(bundle.read(item))


def create_manifest(root: Path, commit: str, ref: str) -> dict:
    tree = SourceTree(root, repository=False)
    if "MANIFEST.json" in tree.files:
        raise ValueError("MANIFEST.json must be export-only, not tracked in Git")
    rows = [{"path": name, "sha256": tree.digest(name), "bytes": len(tree.read(name))}
            for name in sorted(tree.files)]
    record = {"schema_version": 1, "source_commit": commit, "source_ref": ref,
              "status": RELEASE_STATUS, "release_scope": RELEASE_SCOPE, "files": rows}
    (root / "MANIFEST.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    return record


def write_zip(root: Path, output: Path) -> None:
    tree = SourceTree(root, repository=False)
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
        for name in sorted(tree.files):
            item = zipfile.ZipInfo(PREFIX + name, date_time=(1980, 1, 1, 0, 0, 0))
            item.create_system = 3
            item.external_attr = (stat.S_IFREG | 0o644) << 16
            item.compress_type = zipfile.ZIP_DEFLATED
            bundle.writestr(item, tree.read(name), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)


def export_release(root: Path, ref: str, output: Path) -> dict:
    root = Path(root).resolve()
    output = Path(output).resolve()
    if output.exists():
        raise ValueError("Refusing to overwrite an existing export: " + str(output))
    commit = git(root, "rev-parse", "--verify", "--end-of-options", ref + "^{commit}")
    if git(root, "rev-parse", "--show-toplevel") != str(root).replace("\\", "/"):
        # Path comparison is native and case-insensitive on Windows.
        if Path(git(root, "rev-parse", "--show-toplevel")).resolve() != root:
            raise ValueError("--root must identify the repository root")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="modularrep-export-") as temporary:
        temporary = Path(temporary)
        archive = temporary / "git.zip"
        git(root, "archive", "--format=zip", "--output=" + str(archive), commit)
        stage = temporary / "source"
        stage.mkdir()
        extract_archive(archive, stage)
        create_manifest(stage, commit, ref)
        checked = check_release(stage)
        # Complete the ZIP before exposing it at the requested path.
        with tempfile.NamedTemporaryFile(prefix=".modularrep-", suffix=".zip", dir=output.parent, delete=False) as stream:
            pending = Path(stream.name)
        try:
            write_zip(stage, pending)
            digest = hashlib.sha256(pending.read_bytes()).hexdigest()
            # Both paths are on the same filesystem. Linking publishes the
            # completed bytes atomically and refuses an existing destination
            # on both Windows and POSIX, including a concurrent creator.
            os.link(pending, output)
            pending.unlink()
        finally:
            if pending.exists():
                pending.unlink()
    return {"status": "exported_checked_source_archive", "source_commit": commit,
            "source_ref": ref, "output": str(output), "sha256": digest,
            "files": checked["files"], "archive_prefix": PREFIX,
            "scope": RELEASE_SCOPE,
            "validation_scope": "Exact Git export and source-inventory checks; no Lean rerun or "
                                "verification of external mathematical assumptions."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--ref", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        print(json.dumps(export_release(args.root, args.ref, args.output), indent=2))
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        detail = error.stderr.strip() if isinstance(error, subprocess.CalledProcessError) else str(error)
        parser.exit(1, f"Release export failed: {detail}\n")


if __name__ == "__main__":
    main()
