# Mathematical documentation

This is the single maintained source tree for the formalisation report and
the mathematical library manual. Both documents use `bibliography-entries.tex`.
The two bibliography selection files contain only ordered reference keys, so
each document retains its own citation numbering.

Install Python 3.11 or later and the pinned Python dependencies:

```sh
python -m pip install -r scripts/documentation-requirements.txt
```

Install LuaLaTeX with the packages used in `preamble.tex`, the TeX Gyre and
Latin Modern fonts, and Poppler's `pdftoppm`. TeX Live 2026 was used for the
included PDFs. With `lualatex` and `pdftoppm` on `PATH`, run from the repository
root:

```sh
python -B scripts/build_manual_pdfs.py
```

The outputs are `output/pdf/formalisation-report.pdf` and
`output/pdf/library-manual.pdf`. Intermediates, page images, contact sheets
and source/PDF hash records are written to `tmp/pdfs/`. Use `--no-render` to
compile without making preview images, or give one document name to build
only that document. The report's source filename remains
`formalisation-companion.tex`.

The builder removes software and timestamp metadata from the PDFs, retaining
their title, author and subject fields. A successful documentation build
checks the documents; it does not establish the external mathematical hypotheses.
