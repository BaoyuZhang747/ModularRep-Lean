"""Check the maintained source tree without invoking Lean or rebuilding documents.

The working tree may contain Git metadata, Lake caches and temporary output.
File identities describe recorded work; they do not establish the truth of the
external mathematical assumptions or repeat the recorded compilation/audits.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

sys.dont_write_bytecode = True
from check_current_package import check as check_current_package
from check_manuscript_providers import check_application_providers

EXPECTED_LEAN_SOURCE_FILES = 2003
RELEASE_STATUS = "released_checked_companion"
RELEASE_SCOPE = "Checked Lean companion under its stated external assumptions."
IGNORED_DIRECTORIES = frozenset({".git", ".lake", "tmp", "__pycache__"})
PRIVATE_DIRECTORIES = frozenset({"history", "private", "backups", "review-packages",
                                 "release-staging", "release-artifacts"})
DOCUMENT_PATHS = frozenset({"output/pdf/formalisation-report.pdf",
                            "output/pdf/library-manual.pdf",
                            "manuscript/manuscript.pdf"})
DOCUMENT_ENTRIES = frozenset({"docs/manuals/formalisation-companion.tex",
                              "docs/manuals/library-manual.tex"})


def safe_relative(name: str) -> str:
    """Accept portable file names only, including on case-insensitive Windows."""
    if not isinstance(name, str) or not name or "\\" in name or ":" in name:
        raise ValueError("Unsafe relative path: " + repr(name))
    parts = name.split("/")
    if (PurePosixPath(name).is_absolute() or any(part in {"", ".", ".."} for part in parts)
            or any(part.rstrip(" .") != part for part in parts)
            or any(ord(c) < 32 or c in '<>"|?*' for c in name)):
        raise ValueError("Unsafe relative path: " + repr(name))
    reserved = {"con", "prn", "aux", "nul"} | {f"{p}{i}" for p in ("com", "lpt") for i in range(1, 10)}
    if any(part.split(".")[0].lower() in reserved for part in parts):
        raise ValueError("Reserved relative path: " + name)
    return name


def forbidden_release_path(name: str) -> bool:
    parts = [p.lower() for p in PurePosixPath(name).parts]
    return any(p in IGNORED_DIRECTORIES or p in PRIVATE_DIRECTORIES
               or p.startswith("external-audit-") for p in parts)


def is_link(path: Path) -> bool:
    """Also reject Windows junctions/reparse points under Python 3.11."""
    return path.is_symlink() or bool(getattr(path.lstat(), "st_file_attributes", 0)
                                    & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0))


class SourceTree:
    """Walk once, reject links, and cache file bytes/hashes for this check."""

    def __init__(self, root: Path, *, repository: bool = True):
        self.root = Path(root).resolve()
        if not self.root.is_dir():
            raise ValueError("Source root is not a directory: " + str(self.root))
        self.files: dict[str, Path] = {}
        self._bytes: dict[str, bytes] = {}
        self._hashes: dict[str, str] = {}
        case_names: set[str] = set()
        for directory, dirs, files in os.walk(self.root, followlinks=False):
            parent = Path(directory)
            kept = []
            for name in sorted(dirs):
                if repository and name.lower() in IGNORED_DIRECTORIES:
                    continue
                path = parent / name
                if is_link(path):
                    raise ValueError("Directory link is not allowed: " + str(path.relative_to(self.root)))
                relative = path.relative_to(self.root).as_posix()
                safe_relative(relative)
                if forbidden_release_path(relative):
                    raise ValueError("Private or generated directory in source tree: " + relative)
                kept.append(name)
            dirs[:] = kept
            for name in sorted(files):
                if repository and (name == ".git" or name.endswith(".pyc")):
                    continue
                path = parent / name
                relative = safe_relative(path.relative_to(self.root).as_posix())
                if is_link(path) or not path.is_file():
                    raise ValueError("File link or nonregular file: " + relative)
                if relative.casefold() in case_names:
                    raise ValueError("Case-colliding file path: " + relative)
                case_names.add(relative.casefold())
                if forbidden_release_path(relative):
                    raise ValueError("Private or generated file in source tree: " + relative)
                self.files[relative] = path

    def read(self, name: str) -> bytes:
        name = safe_relative(name)
        if name not in self.files:
            raise ValueError("Missing source file: " + name)
        if name not in self._bytes:
            self._bytes[name] = self.files[name].read_bytes()
        return self._bytes[name]

    def digest(self, name: str) -> str:
        if name not in self._hashes:
            self._hashes[name] = hashlib.sha256(self.read(name)).hexdigest()
        return self._hashes[name]

    def json(self, name: str):
        return json.loads(self.read(name))

    def require_hash(self, name: str, expected: str) -> None:
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("Invalid recorded SHA-256: " + name)
        if self.digest(name) != expected:
            raise ValueError("File identity differs: " + name)


def check_documents(tree: SourceTree) -> dict:
    actual_pdfs = {name for name in tree.files if name.lower().endswith(".pdf")}
    if actual_pdfs != DOCUMENT_PATHS:
        raise ValueError("Expected only the current report, manual and reference manuscript PDFs; found: "
                         + ", ".join(sorted(actual_pdfs)))
    if any(name.startswith("packages/ModularRep/docs/manuals/") for name in tree.files):
        raise ValueError("Superseded library manual sources are present")
    source_names = {PurePosixPath(name).name for name in DOCUMENT_ENTRIES}
    if any(PurePosixPath(name).name in source_names and name not in DOCUMENT_ENTRIES
           for name in tree.files):
        raise ValueError("A second report or manual source entry point is present")
    entries = set()
    for name in tree.files:
        if name.lower().endswith(".tex"):
            text = tree.read(name).decode("utf-8-sig")
            if re.search(r"(?m)^\s*\\documentclass(?:\[.*?\])?\{", text):
                if name == "manuscript/current/main.tex":
                    continue
                entries.add(name)
    if entries != DOCUMENT_ENTRIES:
        raise ValueError("Expected exactly the two canonical document entry points")
    shared = tree.read("docs/manuals/bibliography-entries.tex").decode("utf-8-sig")
    if "\\DeclareManualReference{" not in shared:
        raise ValueError("Shared bibliography entry definitions are missing")
    for selector in ("bibliography-companion.tex", "bibliography-library.tex"):
        text = tree.read("docs/manuals/" + selector).decode("utf-8-sig")
        if "\\bibitem" in text or "\\DeclareManualReference{" in text or "\\ManualReference{" not in text:
            raise ValueError("Bibliography selector contains separate entry definitions: " + selector)
    record = tree.json("verification/documents.json")
    documents = record.get("documents", [])
    if len(documents) != 3 or {row.get("path") for row in documents} != DOCUMENT_PATHS:
        raise ValueError("Document verification record does not identify the canonical three PDFs")
    covered_sources = set()
    for row in documents:
        tree.require_hash(row["path"], row["sha256"])
        if not tree.read(row["path"]).startswith(b"%PDF-"):
            raise ValueError("Document is not a PDF: " + row["path"])
        source_files = row.get("source_files")
        if not isinstance(source_files, dict) or not source_files:
            raise ValueError("Document source identities missing: " + row["path"])
        for name, digest in source_files.items():
            tree.require_hash(name, digest)
            covered_sources.add(name)
    manual_sources = {name for name in tree.files if name.startswith("docs/manuals/")
                      and name.lower().endswith((".tex", ".bib"))}
    if not manual_sources <= covered_sources:
        raise ValueError("Manual sources absent from current document identities: "
                         + ", ".join(sorted(manual_sources - covered_sources)))
    return {"pdfs": sorted(DOCUMENT_PATHS), "source_files": len(covered_sources)}


def check_source_identities(tree: SourceTree) -> dict:
    record = tree.json("verification/source-identity.json")
    rows = record.get("files", [])
    names = [row.get("path") for row in rows]
    actual = {name for name in tree.files if name.lower().endswith(".lean")}
    if (len(rows) != EXPECTED_LEAN_SOURCE_FILES or len(set(names)) != len(names)
            or set(names) != actual or record.get("source_files") != EXPECTED_LEAN_SOURCE_FILES):
        raise ValueError("Lean source inventory differs from the recorded 2,003 source and audit files")
    for row in rows:
        tree.require_hash(row["path"], row["source_sha256"])
    tree.require_hash("manuscript/current/main.tex", record["manuscript_sha256"])
    return {"lean_source_files": len(rows), "manuscript_sha256": record["manuscript_sha256"]}


def check_computations(tree: SourceTree) -> int:
    base = "packages/ModularRep/data/computations/"
    record = tree.json(base + "assets.json")
    checked = set()
    for row in record["assets"]:
        for kind in ("program", "output"):
            relative = safe_relative(row[kind])
            name = base + relative
            tree.require_hash(name, row[kind + "_sha256"])
            checked.add(name)
    return len(checked)


def check_release_scope(tree: SourceTree) -> None:
    record = tree.json("STATUS.json")
    if (record.get("status") != RELEASE_STATUS or record.get("release_ready") is not True
            or record.get("release_scope") != RELEASE_SCOPE):
        raise ValueError("The checked-companion release scope is missing or has changed")
    if not tree.read("SCOPE.md").strip():
        raise ValueError("The checked-companion scope document is empty")
    for field in ("external_assumptions", "limitations"):
        entries = record.get(field)
        if (not isinstance(entries, list) or not entries
                or any(not isinstance(entry, str) or not entry.strip() for entry in entries)):
            raise ValueError("STATUS.json " + field + " must state nonempty mathematical scope entries")
    library = tree.json("packages/ModularRep/verification-status.json")
    if (library.get("release_ready") is not True or any(library.get(field) != record[field]
            for field in ("status", "release_ready", "release_scope", "external_assumptions", "limitations"))):
        raise ValueError("Library status differs from the checked-companion release scope")
    tree.require_hash("manuscript/current/main.tex", record["manuscript_sha256"])
    references = [record.get("source_identity"), record.get("assertion_summary")]
    references += list(record.get("verification", {}).values())
    for reference in references:
        if isinstance(reference, dict) and "path" in reference and "sha256" in reference:
            tree.require_hash(reference["path"], reference["sha256"])
    if record.get("documents") != tree.json("verification/documents.json")["documents"]:
        raise ValueError("STATUS.json document identities differ from verification/documents.json")


def check_repository(root: Path, *, tree: SourceTree | None = None) -> dict:
    tree = tree or SourceTree(root)
    check_release_scope(tree)
    sources = check_source_identities(tree)
    documents = check_documents(tree)
    computations = check_computations(tree)
    configuration = check_current_package(tree.root, False)
    providers = check_application_providers(tree.root)
    return {"status": "passed_repository_checks", **sources, "documents": documents,
            "computational_inputs": computations, "dependencies": configuration["dependencies"],
            "provider_checks": providers["counts"],
            "scope": "Current source and document identities, pinned dependency configurations, "
                     "computation files, lexical provider associations and checked-companion release scope. "
                     "These checks do not rerun Lean, verify external mathematical assumptions or render PDFs."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        print(json.dumps(check_repository(args.root), indent=2))
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(1, f"Repository check failed: {error}\n")


if __name__ == "__main__":
    main()
