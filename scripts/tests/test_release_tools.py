"""Focused tests for maintained-tree versus pristine-export verification.

Small synthetic source fixtures isolate packaging behavior. Existing dependency
and provider checkers are mocked here; real repository/export checks exercise
them against the complete 2,003-file package separately.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_repository as repository
import export_release as exporter
import verify_release as release


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


class ReleaseToolsTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.root = self.base / "repo"
        self.root.mkdir()
        for target, replacement in (
            ("EXPECTED_LEAN_SOURCE_FILES", 2),
            ("check_current_package", lambda *args: {"dependencies": {"fixture": True}}),
            ("check_application_providers", lambda *args: {"counts": {"fixture": True}}),
        ):
            mocker = patch.object(repository, target, replacement)
            mocker.start()
            self.addCleanup(mocker.stop)
        self.write("ManuscriptIBAW.lean", "import ManuscriptIBAW.Main\n")
        self.write("ManuscriptIBAW/Main.lean", "theorem fixture : True := True.intro\n")
        self.write("manuscript/current/main.tex", "Fixture manuscript\n")
        self.write("docs/manuals/formalisation-companion.tex", "\\documentclass{article}\n\\input{preamble}\n")
        self.write("docs/manuals/library-manual.tex", "\\documentclass{article}\n\\input{preamble}\n")
        self.write("docs/manuals/preamble.tex", "\\input{bibliography-entries}\n")
        self.write("docs/manuals/bibliography-entries.tex", "\\DeclareManualReference{one}{A reference.}\n")
        for selector in ("companion", "library"):
            self.write(f"docs/manuals/bibliography-{selector}.tex", "\\ManualReference{one}\n")
        manuals = {p.relative_to(self.root).as_posix(): sha(p.read_bytes())
                   for p in (self.root / "docs/manuals").rglob("*.tex")}
        documents = []
        for name in sorted(repository.DOCUMENT_PATHS):
            self.write(name, b"%PDF-1.7\nSynthetic test fixture\n")
            sources = ({"manuscript/current/main.tex": self.hash("manuscript/current/main.tex")}
                       if name.startswith("manuscript/") else manuals)
            documents.append({"path": name, "sha256": self.hash(name), "source_files": sources})
        self.write_json("verification/documents.json", {"documents": documents})
        lean = sorted(p.relative_to(self.root).as_posix() for p in self.root.rglob("*.lean"))
        self.write_json("verification/source-identity.json", {
            "source_files": 2, "manuscript_sha256": self.hash("manuscript/current/main.tex"),
            "files": [{"path": name, "source_sha256": self.hash(name)} for name in lean],
        })
        self.write("SCOPE.md", "Synthetic packaging fixture under stated external assumptions.\n")
        status = {
            "status": "released_checked_companion", "release_ready": True,
            "release_scope": "Checked Lean companion under its stated external assumptions.",
            "external_assumptions": ["Synthetic external input; this fixture does not test its mathematical truth."],
            "limitations": ["This fixture tests packaging, not mathematical correctness."],
            "manuscript_sha256": self.hash("manuscript/current/main.tex"),
            "source_identity": {"path": "verification/source-identity.json",
                                "sha256": self.hash("verification/source-identity.json")},
            "documents": documents,
        }
        self.write_json("STATUS.json", status)
        self.write_json("packages/ModularRep/verification-status.json", status)
        data = "packages/ModularRep/data/computations/"
        self.write(data + "code/fixture.g", "Print(1);\n")
        self.write(data + "outputs/fixture.out", "1\n")
        self.write_json(data + "assets.json", {"assets": [{
            "program": "code/fixture.g", "program_sha256": self.hash(data + "code/fixture.g"),
            "output": "outputs/fixture.out", "output_sha256": self.hash(data + "outputs/fixture.out"),
        }]})

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(value.encode() if isinstance(value, str) else value)

    def write_json(self, name, value):
        self.write(name, json.dumps(value, indent=2) + "\n")

    def hash(self, name):
        return sha((self.root / name).read_bytes())

    def manifest(self):
        exporter.create_manifest(self.root, "a" * 40, "v0.1.0-test")

    def test_repository_tolerates_git_lake_and_temporary_files(self):
        for name in (".git/config", ".lake/packages/Fake/Fake.lean", "tmp/manual.pdf",
                     "packages/ModularRep/.lake/build/cache.lean", "scripts/__pycache__/x.pyc"):
            self.write(name, "local cache\n")
        before = {p.relative_to(self.root).as_posix(): p.read_bytes()
                  for p in self.root.rglob("*") if p.is_file()}
        self.assertEqual(repository.check_repository(self.root)["lean_source_files"], 2)
        after = {p.relative_to(self.root).as_posix(): p.read_bytes()
                 for p in self.root.rglob("*") if p.is_file()}
        self.assertEqual(before, after)

    def test_repository_rejects_duplicate_manual_pdf(self):
        self.write("output/pdf/standalone-library-manual.pdf", "%PDF-1.7\n")
        with self.assertRaisesRegex(ValueError, "only the current"):
            repository.check_repository(self.root)

    def test_repository_rejects_superseded_source_tree(self):
        self.write("packages/ModularRep/docs/manuals/old.tex", "old\n")
        with self.assertRaisesRegex(ValueError, "Superseded"):
            repository.check_repository(self.root)

    def test_repository_rejects_unrecognized_document_entry_point(self):
        self.write("docs/old-report.tex", "\\documentclass{article}\n")
        with self.assertRaisesRegex(ValueError, "two canonical document entry"):
            repository.check_repository(self.root)

    def test_repository_rejects_separate_bibliography_definitions(self):
        self.write("docs/manuals/bibliography-companion.tex", "\\bibitem{old} Outdated.\n")
        with self.assertRaisesRegex(ValueError, "separate entry definitions"):
            repository.check_repository(self.root)

    def test_repository_rejects_modified_lean_source(self):
        self.write("ManuscriptIBAW/Main.lean", "axiom fixture : False\n")
        with self.assertRaisesRegex(ValueError, "File identity differs"):
            repository.check_repository(self.root)

    def test_repository_rejects_unscoped_release_readiness(self):
        record = json.loads((self.root / "STATUS.json").read_bytes())
        for field, value in (("status", "ready"), ("release_ready", False), ("release_ready", 1),
                             ("release_scope", None), ("release_scope", "Unconditional proof.")):
            with self.subTest(field=field, value=value):
                self.write_json("STATUS.json", dict(record, **{field: value}))
                with self.assertRaisesRegex(ValueError, "release scope"):
                    repository.check_repository(self.root)

    def test_repository_requires_scope_document(self):
        (self.root / "SCOPE.md").unlink()
        with self.assertRaisesRegex(ValueError, "Missing source file: SCOPE.md"):
            repository.check_repository(self.root)
        self.write("SCOPE.md", " \n\t")
        with self.assertRaisesRegex(ValueError, "scope document is empty"):
            repository.check_repository(self.root)

    def test_repository_requires_external_assumptions_and_limitations(self):
        record = json.loads((self.root / "STATUS.json").read_bytes())
        for field in ("external_assumptions", "limitations"):
            for value in (None, [], [" "], ["A scope entry", None], "A scope entry"):
                with self.subTest(field=field, value=value):
                    self.write_json("STATUS.json", dict(record, **{field: value}))
                    with self.assertRaisesRegex(ValueError, field + " must state"):
                        repository.check_repository(self.root)

    def test_library_and_root_release_scope_must_agree(self):
        name = "packages/ModularRep/verification-status.json"
        record = json.loads((self.root / name).read_bytes())
        for field, value in (("status", "ready"), ("release_ready", 1),
                             ("release_scope", "Unconditional proof."),
                             ("external_assumptions", ["A different assumption"]),
                             ("limitations", ["A different limitation"])):
            with self.subTest(field=field):
                self.write_json(name, dict(record, **{field: value}))
                with self.assertRaisesRegex(ValueError, "Library status differs"):
                    repository.check_repository(self.root)

    def test_clean_release_verifies(self):
        self.manifest()
        checked = release.check_release(self.root)
        self.assertEqual(checked["status"], "passed_release_checks")
        self.assertEqual(checked["source_commit"], "a" * 40)
        self.assertEqual(checked["release_scope"], repository.RELEASE_SCOPE)

    def test_release_manifest_requires_companion_scope(self):
        self.manifest()
        record = json.loads((self.root / "MANIFEST.json").read_bytes())
        for field, value in (("status", "ready"), ("release_scope", None),
                             ("release_scope", "Unconditional proof.")):
            with self.subTest(field=field, value=value):
                self.write_json("MANIFEST.json", dict(record, **{field: value}))
                with self.assertRaisesRegex(ValueError, "manifest.*release scope"):
                    release.check_release(self.root)

    def test_release_rejects_tampering(self):
        self.manifest()
        self.write("output/pdf/library-manual.pdf", b"%PDF-1.7\nTampered\n")
        with self.assertRaisesRegex(ValueError, "File identity differs"):
            release.check_release(self.root)

    def test_release_rejects_missing_file(self):
        self.manifest()
        (self.root / "ManuscriptIBAW/Main.lean").unlink()
        with self.assertRaisesRegex(ValueError, "Missing source file"):
            release.check_release(self.root)

    def test_release_rejects_unexpected_file(self):
        self.manifest()
        self.write("unexpected.txt", "Extra file\n")
        with self.assertRaisesRegex(ValueError, "unexpected files"):
            release.check_release(self.root)

    def test_release_rejects_cache_directories(self):
        self.manifest()
        self.write(".lake/cache", "cache")
        with self.assertRaisesRegex(ValueError, "Private or generated"):
            release.check_release(self.root)

    def test_manifest_rejects_traversal_and_duplicate_names(self):
        self.manifest()
        original = json.loads((self.root / "MANIFEST.json").read_bytes())
        for name in ("../outside.txt", "/absolute.txt", "C:/absolute.txt", "folder\\name", "CON.txt"):
            with self.subTest(name=name):
                record = dict(original, files=[dict(original["files"][0], path=name)])
                self.write_json("MANIFEST.json", record)
                with self.assertRaisesRegex(ValueError, "relative path"):
                    release.check_release(self.root)
        duplicate = dict(original, files=original["files"] + [original["files"][0]])
        self.write_json("MANIFEST.json", duplicate)
        with self.assertRaisesRegex(ValueError, "Repeated"):
            release.check_release(self.root)

    def test_archive_extraction_rejects_traversal(self):
        archive = self.base / "hostile.zip"
        with zipfile.ZipFile(archive, "w") as bundle:
            bundle.writestr("../escaped.txt", "escape")
        with self.assertRaisesRegex(ValueError, "Unsafe relative path"):
            exporter.extract_archive(archive, self.base / "extract")
        self.assertFalse((self.base / "escaped.txt").exists())

    def test_archive_extraction_rejects_symbolic_links(self):
        archive = self.base / "link.zip"
        with zipfile.ZipFile(archive, "w") as bundle:
            item = zipfile.ZipInfo("link.txt")
            item.create_system = 3
            item.external_attr = (stat.S_IFLNK | 0o777) << 16
            bundle.writestr(item, "../outside.txt")
        with self.assertRaisesRegex(ValueError, "symbolic link"):
            exporter.extract_archive(archive, self.base / "extract")

    @unittest.skipUnless(shutil.which("git"), "Git is required for export integration")
    def test_export_does_not_overwrite_concurrent_output(self):
        for args in (("init",), ("config", "user.name", "Packaging test"),
                     ("config", "user.email", "packaging-test@example.invalid"),
                     ("config", "core.autocrlf", "false"), ("add", "."),
                     ("commit", "-m", "Synthetic release fixture")):
            subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True)
        output = self.base / "concurrent.zip"
        original_write = exporter.write_zip

        def create_competing_output(root, pending):
            original_write(root, pending)
            output.write_bytes(b"Created by another exporter")

        with patch.object(exporter, "write_zip", side_effect=create_competing_output):
            with self.assertRaises(FileExistsError):
                exporter.export_release(self.root, "HEAD", output)
        self.assertEqual(output.read_bytes(), b"Created by another exporter")
        self.assertEqual(list(self.base.glob(".modularrep-*.zip")), [])

    @unittest.skipUnless(shutil.which("git"), "Git is required for export integration")
    def test_export_is_exact_ref_and_deterministic(self):
        def git(*args):
            return subprocess.run(["git", "-C", str(self.root), *args], check=True,
                                  capture_output=True, text=True).stdout.strip()
        git("init")
        git("config", "user.name", "Packaging test")
        git("config", "user.email", "packaging-test@example.invalid")
        git("config", "core.autocrlf", "false")
        git("add", ".")
        git("commit", "-m", "Synthetic release fixture")
        git("tag", "v0.1.0-test")
        commit = git("rev-parse", "HEAD")
        # A dirty tracked source and an untracked file must not enter the export.
        self.write("ManuscriptIBAW/Main.lean", "dirty working-tree source\n")
        self.write("untracked.txt", "Not part of the selected commit\n")
        first = self.base / "first.zip"
        second = self.base / "second.zip"
        result = exporter.export_release(self.root, "v0.1.0-test", first)
        exporter.export_release(self.root, "v0.1.0-test", second)
        self.assertEqual(first.read_bytes(), second.read_bytes())
        self.assertEqual(result["source_commit"], commit)
        with zipfile.ZipFile(first) as bundle:
            self.assertTrue(all(name.startswith("ModularRep/") for name in bundle.namelist()))
            self.assertNotIn("ModularRep/untracked.txt", bundle.namelist())
            self.assertNotIn("dirty", bundle.read("ModularRep/ManuscriptIBAW/Main.lean").decode())
            record = json.loads(bundle.read("ModularRep/MANIFEST.json"))
            self.assertEqual(record["source_commit"], commit)
        with self.assertRaisesRegex(ValueError, "overwrite"):
            exporter.export_release(self.root, "v0.1.0-test", first)


if __name__ == "__main__":
    unittest.main()
