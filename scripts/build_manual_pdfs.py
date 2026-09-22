"""Build the two mathematical manuals and render every page for visual review.

Run with a Python installation containing Pillow, pypdf and pdfplumber.
LuaLaTeX and Poppler's pdftoppm must be on PATH. Compilation intermediates,
page images, contact sheets and the build report go under tmp/pdfs. Only
the two resulting PDFs are written to output/pdf. A successful run is a
document build, not a verification of the mathematical package.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from PIL import Image, ImageDraw
from pypdf import PdfReader, PdfWriter
import pdfplumber


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "docs" / "manuals"
SCRATCH = ROOT / "tmp" / "pdfs"
OUTPUT = ROOT / "output" / "pdf"
DOCUMENTS = ("formalisation-companion", "library-manual")
PUBLIC_NAMES = {"formalisation-companion": "formalisation-report",
                "library-manual": "library-manual"}
DOCUMENT_ALIASES = {"formalisation-report": "formalisation-companion"}


def resolve_document(name: str) -> str:
    """Keep source and scratch identifiers stable behind the public name."""
    resolved = DOCUMENT_ALIASES.get(name, name)
    if resolved not in DOCUMENTS:
        raise ValueError(f"Unknown document: {name}")
    return resolved


def select_documents(names: list[str]) -> list[str]:
    """Resolve all arguments before building, preserving order without repeats."""
    return list(dict.fromkeys(resolve_document(name) for name in names or DOCUMENTS))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_snapshot() -> dict[str, str]:
    return {path.relative_to(ROOT).as_posix(): digest(path)
            for path in sorted(SOURCE.rglob("*.tex"))}


def run(command: list[str], cwd: Path, log: Path) -> None:
    result = subprocess.run(command, cwd=cwd, text=True,
                            encoding="utf-8", errors="replace",
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(result.stdout, encoding="utf-8")
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}), see {log}\n"
                           + result.stdout[-5000:])


def build(name: str, render: bool = True) -> dict:
    name = resolve_document(name)
    stage = SCRATCH / name
    stage.mkdir(parents=True, exist_ok=True)
    for pass_number in range(1, 4):
        run(["lualatex", "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", "-recorder", f"-output-directory={stage}",
             f"{name}.tex"], SOURCE, stage / f"compile-{pass_number}.txt")
    tex_log = (stage / f"{name}.log").read_text(encoding="utf-8", errors="replace")
    warnings = [line for line in tex_log.splitlines()
                if re.search(r"Warning|Overfull|Underfull|Missing character", line)]
    fatal_warnings = [line for line in warnings
                      if re.search(r"undefined|Missing character", line)]
    if fatal_warnings:
        raise RuntimeError("Unresolved document errors: " + "\n".join(fatal_warnings))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    pdf_path = OUTPUT / f"{PUBLIC_NAMES[name]}.pdf"
    # Keep document metadata while removing software and timestamp metadata.
    original = PdfReader(stage / f"{name}.pdf")
    writer = PdfWriter()
    writer.clone_document_from_reader(original)
    writer.metadata = None
    writer.add_metadata({key: str(value) for key, value in (original.metadata or {}).items()
                         if key in {"/Title", "/Author", "/Subject"}})
    if "/Metadata" in writer.root_object:
        del writer.root_object["/Metadata"]
    with pdf_path.open("wb") as destination:
        writer.write(destination)
    reader = PdfReader(pdf_path)
    bounds_issues = []
    with pdfplumber.open(pdf_path) as pdf:
        for page_number, page in enumerate(pdf.pages, 1):
            for char in page.chars:
                if (char["x0"] < -0.5 or char["x1"] > page.width + 0.5
                        or char["top"] < -0.5 or char["bottom"] > page.height + 0.5):
                    bounds_issues.append({"page": page_number, "text": char["text"]})
    (stage / "extracted-text.txt").write_text(
        "\n\n".join(f"PAGE {i}\n{page.extract_text()}"
                      for i, page in enumerate(reader.pages, 1)), encoding="utf-8")
    if render:
        render_dir = stage / "pages"
        render_dir.mkdir(exist_ok=True)
        for previous in render_dir.glob("page-*.png"):
            previous.unlink()
        for previous in stage.glob("overview-*.jpg"):
            previous.unlink()
        run(["pdftoppm", "-r", "110", "-png", str(pdf_path), str(render_dir / "page")],
            ROOT, stage / "render.txt")
        pages = sorted(render_dir.glob("page-*.png"),
                       key=lambda path: int(path.stem.split("-")[-1]))
        if len(pages) != len(reader.pages):
            raise RuntimeError(f"Expected {len(reader.pages)} rendered pages, found {len(pages)}")
        # Four-page overviews retain a separate full-resolution PNG for each page.
        for start in range(0, len(reader.pages), 4):
            selected = pages[start:start + 4]
            thumbs = []
            for page in selected:
                with Image.open(page) as im:
                    thumb = im.convert("RGB")
                    thumb.thumbnail((744, 1053))
                    thumbs.append(thumb.copy())
            sheet = Image.new("RGB", (1508, 2176), "#d4d4d4")
            draw = ImageDraw.Draw(sheet)
            for offset, im in enumerate(thumbs):
                x = 10 + (offset % 2) * 754
                y = 30 + (offset // 2) * 1083
                draw.text((x, y - 21), f"{name}: PDF page {start + offset + 1}", fill="black")
                sheet.paste(im, (x, y))
            sheet.save(stage / f"overview-{start + 1:03d}-{start + len(selected):03d}.jpg",
                       quality=92)
    report = {"document": name, "pdf": pdf_path.relative_to(ROOT).as_posix(),
              "source": (SOURCE / f"{name}.tex").relative_to(ROOT).as_posix(),
              "sha256": digest(pdf_path), "pages": len(reader.pages),
              "warnings": warnings, "page_bounds_issues": bounds_issues,
              "rendered": render, "visual_review": "pending"}
    if name == "formalisation-companion":
        report["title"] = "Formalisation report"
    (stage / "build-report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report), flush=True)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("documents", nargs="*", metavar="DOCUMENT",
                        help="formalisation-report or library-manual (default: both)")
    parser.add_argument("--no-render", action="store_true")
    args = parser.parse_args()
    SCRATCH.mkdir(parents=True, exist_ok=True)
    sources = source_snapshot()
    reports = [build(name, not args.no_render) for name in select_documents(args.documents)]
    if sources != source_snapshot():
        raise RuntimeError("Documentation sources changed during the build; rebuild before use")
    manifest = {"scope": "Documentation build only; does not verify the mathematical package",
                "builder_sha256": digest(Path(__file__)),
                "metadata_policy": "Only Title, Author and Subject retained; software and dates removed",
                "sources": sources,
                "documents": reports}
    (SCRATCH / "manual-build.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
