"""Verify a pristine exported source release, without invoking Lean.

This checks the manifest and content of an unpacked export. The manifest is an
inventory, not a cryptographic signature or an independent proof of origin.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
from check_repository import RELEASE_SCOPE, RELEASE_STATUS, SourceTree, check_repository, safe_relative


def check_release(root: Path) -> dict:
    tree = SourceTree(root, repository=False)
    record = tree.json("MANIFEST.json")
    if (record.get("schema_version") != 1 or record.get("status") != RELEASE_STATUS
            or record.get("release_scope") != RELEASE_SCOPE):
        raise ValueError("Unexpected source release manifest schema, status or release scope")
    if not re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", record.get("source_commit", "")):
        raise ValueError("Missing or invalid source commit")
    if not isinstance(record.get("source_ref"), str) or not record["source_ref"]:
        raise ValueError("Missing source reference")
    rows = record.get("files")
    if not isinstance(rows, list) or not rows:
        raise ValueError("Missing release inventory")
    names = set()
    folded = set()
    for row in rows:
        name = safe_relative(row["path"])
        if name == "MANIFEST.json" or name in names or name.casefold() in folded:
            raise ValueError("Repeated, case-colliding or self-referential inventory path: " + name)
        names.add(name)
        folded.add(name.casefold())
        tree.require_hash(name, row["sha256"])
        if type(row.get("bytes")) is not int or row["bytes"] != len(tree.read(name)):
            raise ValueError("File length differs: " + name)
    actual = set(tree.files)
    if actual != names | {"MANIFEST.json"}:
        raise ValueError("Release inventory differs; unexpected files: "
                         + ", ".join(sorted(actual - names - {"MANIFEST.json"})))
    result = check_repository(tree.root, tree=tree)
    return {"status": "passed_release_checks", "source_commit": record["source_commit"],
            "source_ref": record["source_ref"], "manifest_entries": len(names),
            "files": len(actual), "repository": result,
            "release_scope": RELEASE_SCOPE,
            "scope": "Exact export inventory and repository checks for the stated companion scope. "
                     "The manifest is not signed. These checks do not rerun Lean or verify external "
                     "mathematical assumptions."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        print(json.dumps(check_release(args.root), indent=2))
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(1, f"Release check failed: {error}\n")


if __name__ == "__main__":
    main()
