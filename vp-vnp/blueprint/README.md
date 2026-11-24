# Blueprint

The blueprint of this folder: a site that sets the paper's statements beside the Lean
declarations that state them, with the dependency graph of the Lean development. It is written
with [Verso Blueprint](https://github.com/leanprover/verso-blueprint) in the version of the fork
[eric-vergo/verso-blueprint](https://github.com/eric-vergo/verso-blueprint) (branch `v4.36.0`,
for Lean `v4.36.0`), which `lakefile.toml` pins together with the forks of Verso and SubVerso.
The proof does not depend on the blueprint: `lake build` does not build it.

## Layout

| File | Role |
|---|---|
| `BlueprintMain.lean` (folder `vp-vnp`) | generator entry point; `lake exe vbp build` finds it there |
| `informal-claims.json` (folder `vp-vnp`) | the paper's statements of the five judged theorems, shown as the author's claim |
| `blueprint/VpVnpBlueprint.lean` | the front page and the list of parts |
| `blueprint/VpVnpBlueprint/Parts/*.lean` | one file per part: its introduction and its chapters |
| `blueprint/VpVnpBlueprint/Chapters/*.lean` | one file per chapter, each citing the sections and pages of the paper it follows |
| `blueprint/VpVnpBlueprint/GraphCommand.lean` | `{vpvnp_graph}`: the dependency graph, opened on its group view |
| `blueprint/scripts/GenerateNodes.lean` | writes `blueprint/VpVnpBlueprint/Generated/` from the compiled code |
| `blueprint/VpVnpBlueprint/Generated/` | generated, ignored by git: one chapter per Lean library, one section per module, one node per declaration that no written chapter discusses |
| `scripts/ci-pages.sh` | the whole build, as the site's workflow runs it |

## Building

From the folder `vp-vnp`, after `lake exe cache get` and `lake build`:

```bash
lake env lean --run blueprint/scripts/GenerateNodes.lean  # the generated chapters
lake exe vbp build            # writes the site to _out/site/html-multi/
lake exe vbp build --serve    # the same, then serves it
lake exe vbp check            # checks the generated site
```

Run the generator again whenever a written chapter starts or stops naming a declaration in
`(lean := "...")`, so that each declaration appears once. To elaborate one chapter while writing
it, build its module, for example `lake build VpVnpBlueprint.Paper.AppendixA`.

`_out/` is ignored by git. The site needs no network access when it is viewed, and every link
inside it is relative, so it also works under the sub-path of its GitHub Pages address.

## Publishing

`../.github/workflows/vp-vnp-blueprint.yml` runs `scripts/ci-pages.sh` on every push to the
branch `blueprint` and publishes the site with GitHub Pages. The script builds the development,
checks that the five theorems rest on no axiom beyond Lean's standard three, checks the layout of
the Comparator challenge, generates the chapters from the compiled code, builds the site, and
fails when `lake exe vbp check` reports a problem or the Project Stats page does not show every
judged theorem as proved with both kernel checkers accepting the replay.

## Licence

Apache 2.0, as the rest of the folder; see `../LICENSE` and `../NOTICE`.
