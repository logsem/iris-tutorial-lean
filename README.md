# The Iris Tutorial in Lean

A Lean 4 port of the [Iris tutorial](https://github.com/logsem/iris-tutorial),
originally developed as a Rocq tutorial, based on
[iris-lean](https://github.com/leanprover-community/iris-lean).

The book is written in [Verso](https://github.com/leanprover/verso):
prose and Lean proofs live together in the same `.lean`
files, and every proof is elaborated (type-checked) by the same toolchain
that renders the book. 

The build produces two outputs from one source:
- the rendered **HTML book**, and
- a downloadable **`code.zip`** of the extracted, compilable example modules.

## Porting status

This is a work in progress. The following chapters are fully ported and
type-checked:

- **Basics**
- **Pure**
- **Lang**
- **Specifications**
- **Persistently**
- **Linked Lists**
- **Later**

The remaining chapters are stubs ("This chapter has not yet been ported")
pending translation from their Rocq sources.

## Building

The Lean toolchain is pinned in `lean-toolchain` (`leanprover/lean4:4.30.0`).
`verso` and `iris-lean` are pinned in `lakefile.toml`; the three versions
must stay in lockstep.

| Command | What it does |
| --- | --- |
| `lake exe textbook` | Build the book: elaborate every chapter (type-checking all proofs) and write HTML to `_out/html-multi/` plus extracted example code to `_out/example-code/`. |
| `make` / `make out` | Build, then assemble `out/html-multi/` and `out/code.zip` for publishing. |
| `make serve` | Build and serve the HTML locally (`PORT=8000` by default; override with `make serve PORT=9000`). |
| `make clean` | Remove `out/` and `_out/`. |

## Repository layout

- `IrisTutorialBook.lean` — the `#doc` book root: front matter, authors, and
  the `{include}` directives that order the chapters.
- `IrisTutorial/*.lean` — one file per chapter, aggregated by
  `IrisTutorial.lean`.
- `BookGen/`, `BookGenMain.lean` — book-generation infrastructure inherited
  from the Verso textbook template (the `textbook` executable and the custom
  `savedLean` / `savedImport` / `savedComment` code-block elaborators that
  make a block both type-checked inline *and* extracted to a file).

## License and attribution

The Lean port is released under the [MIT License](LICENSE), matching the
upstream tutorial. It derives from the Iris Tutorial originally written by
Lars Birkedal, Simon Gregersen, Mathias Adam Møller, Mathias Pedersen, and
Amin Timany (Aarhus University). Lean port by Zongyuan Liu.

The files under `BookGen/` and `BookGenMain.lean` are
inherited from the Verso textbook template and remain under their original
copyright (Lean FRO LLC, Apache 2.0).
