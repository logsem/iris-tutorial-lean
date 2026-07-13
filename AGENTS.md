# AGENTS.md

## What this is

A Lean 4 port of the [Iris separation-logic tutorial]( https://github.com/logsem/iris-tutorial/tree/master). It is authored as a **Verso manual-genre textbook**: the prose and the Lean proofs live together in `.lean` files, and the proofs are elaborated (type-checked) by the same Lean toolchain that builds the book. The build also *extracts* the example code into standalone modules.

The repo serves two outputs from one source: the rendered HTML book, and a downloadable `code.zip` of the extracted, compilable examples.

## Commands

- `lake exe textbook` — build the book. Elaborates every chapter (so this also type-checks all Iris proofs) and writes HTML to `_out/html-multi/` plus extracted example code to `_out/example-code/`.
- `make` / `make out` — build, then assemble `out/html-multi/` and `out/code.zip` for publishing.
- `make serve` — build and serve the HTML locally (`PORT=8000` by default; `make serve PORT=9000`).
- `make clean` — remove `out/` and `_out/`.
- `lake build IrisTutorial.Basics` — elaborate a single chapter module without rendering HTML. **Use this to iterate on one chapter's proofs** — much faster than a full `lake exe textbook`.

The Lean toolchain is pinned in `lean-toolchain` (`leanprover/lean4:4.30.0`); `verso` and `iris-lean` are both pinned to `v4.30.0` in `lakefile.toml`. These three versions must stay in lockstep.

## Architecture

### Three layers

1. **Book root and generation infrastructure.**
   - `IrisTutorialBook.lean` — the `#doc` book root: front matter, authors, and the `{include}` directives that order the chapters into the rendered book. **This is the book itself**; edit it to change front matter or chapter ordering.
   - `BookGenMain.lean` — the `textbook` executable (its lakefile `root`). Its `buildExercises` traverse step walks the whole book *before* HTML generation, collecting saved code blocks into files under `example-code/`, and `main` renders the book root via `%doc IrisTutorialBook`.
   - `BookGen/Meta/Lean.lean` — defines the custom `savedLean` / `savedImport` / `savedComment` code-block elaborators (in `namespace BookGen`) and their backing `Block.savedLean` / `Block.savedImport` extensions. This is the mechanism that lets a code block be both type-checked inline *and* extracted to a file.
   - `BookGen/` and `BookGenMain.lean` are inherited from the Verso textbook template and remain under their original copyright (Lean FRO LLC, Apache 2.0) — usually leave them alone.

2. **Tutorial content** — `IrisTutorial/*.lean`, one file per chapter, aggregated by `IrisTutorial.lean`. Each chapter is a `#doc (Manual) "Title" => ...` document mixing Verso prose with elaborated Lean/Iris proofs.

3. **Dependencies** — `verso` (the documentation/genre framework) and `iris-lean` (the Lean port of Iris that provides `IProp`, the BI connectives, and the Iris Proof Mode tactics like `iintro`, `iapply`, `iexact`, `ipure_intro`).

### Code-block conventions inside chapters

The block *language tag* determines how a fenced block is treated:

- ```` ```savedLean ```` — elaborated inline (type-checked as part of the build) **and** appended to the extracted example file for that chapter. This is the workhorse for definitions, theorems, `namespace`/`variable`/`open`/`end` lines.
- ```` ```savedImport ```` — an `import` line. Suppressed in the rendered output, but hoisted to the *top* of the extracted file (`buildExercises` *prepends* `savedImport` blocks while *appending* `savedLean` blocks; see `BookGenMain.lean`).
- ```` ```savedComment ```` — prose wrapped as a `/-! ... -/` module docstring in the extracted file.

Because saved blocks are concatenated in source order into one module per chapter, the `namespace`/`open`/`variable`/`end` blocks must bracket the theorems correctly *as a sequence* — the extracted file is exactly the saved blocks joined with newlines.

## Lean MCP / search

`.mcp.json` wires the `lean-lsp` MCP server with a **local Loogle instance** (`LOOGLE_URL=http://localhost:8088`) and disables the hosted natural-language search tools (`lean_leansearch`, `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise`). Prefer `lean_local_search`, `lean_loogle`, `lean_goal`, and `lean_hover_info`; the disabled tools will not be available.
