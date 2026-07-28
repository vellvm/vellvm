# Makefile: available targets

Run from `src/`.

| Target | What it does |
|---|---|
| `make` / `make all` | Default. Build the `vellvm` executable (compiles all Rocq, extracts OCaml, links). |
| `make rocq` | Rocq-only build: compile every file in `_RocqProject` (no extraction, no executable). |
| `make vellvm` | Build the `vellvm` executable (equivalent to `make all`). |
| `make interp` | Faster executable-only build: compiles just the Rocq files extraction depends on (`Syntax`/`Semantics`/`Handlers`) — skips `rocq/Theory` entirely, unlike `make all`. |
| `make extracted` | Run the Coq-to-OCaml extraction step if the Rocq sources it depends on changed (a dependency of `vellvm`, rarely invoked directly). |
| `make frontend` | Build only the parser/pretty-printer (`frontend` executable), skipping `Semantics`/`Theory` — the fast path for syntax-only work. |
| `make frontend_exe` | Just the `dune build` step of `frontend`, assuming its Rocq files are already compiled. |
| `make test` / `make check` | Run the differential test suite over `../tests` against `clang`/`llc` (builds `vellvm` first). |
| `make test-full` | Same, but the full corpus (`-test` instead of `-test-dir ../tests`). |
| `make perf` | Run the interpreter performance stress tests (`../tests/perf/run.sh`); see `../tests/perf/README.md`. |
| `make timing` | Print per-file Rocq compile times and a summary table sorted by duration (`make clean-rocqmakefile` first to time the whole library from scratch). |
| `make clean` | Remove all build artifacts: compiled Rocq (`.vo`/`.glob`/`.aux`), extracted OCaml, the `vellvm`/`frontend` executables, and dune's build directory. |
| `make extractedclean` | Remove just the extracted OCaml files and extraction stamps (keeps compiled Rocq). |
| `make clean-rocqmakefile` | Run the generated `RocqMakefile`'s own `clean` target. |
| `make opam` | Install opam dependencies into the current switch (**clobbers the switch**; run `eval $(opam env)` after). |
| `make print-includes` | Print the `-R` include flags passed to `rocq`/`rocqdep` (useful for calling `rocq` by hand). |
| `make c2rust-tests` | Delegate to `../tractor/c2rust-tests`. |
| `make rocq/path/File.vo` (or any other target not listed above, e.g. `make html`, `make install`) | Forwarded to the generated `RocqMakefile`, scoped to that specific target — the fastest way to rebuild just one file while iterating. |
