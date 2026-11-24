# VP ≠ VNP over every field

For every field, circuits for the Hamiltonian cycle polynomial, and for the permanent outside characteristic 2, need more than m^(c (log m)^(1/3)) gates for all large m. The same holds for approximating circuits. So VP is a proper subset of VNP, and VNP is not contained in the closure of VP. This does not settle P vs NP.

The result was discovered by an internal research Claude model. This folder holds the paper and its Lean 4 formalization. Both were written by AI models, and no human mathematician has checked the proof.

Research artifact. Not maintained and not accepting contributions.

## Proof cleanup

Eric Vergo and GPT-6.2 (OpenAI) revised the Lean proofs and accompanying blueprint on this fork. The paper and its original attribution are preserved. The cleanup starts at the Lean 4.36 port, commit `9fd368ad`. It preserves the bytes of `Statement.lean`, the Comparator challenge, solution and configuration, and the original PDF. From this directory, check those files against the port with:

    git diff --exit-code 9fd368ad HEAD -- Statement.lean Comparator paper.pdf

The real permanent bound now specializes the all-fields theorem. The qualitative flat-case bound follows from the quantitative bound. The blueprint distinguishes these Lean proofs from the paper's original arguments. The [measurement guide](comparison/inventory-method.md) describes the compiled dependency traversal and source measurements.

## Lean 4.36 port at `9fd368ad`

The port was prepared on the branch `blueprint` of a fork of [anthropics/formal-math](https://github.com/anthropics/formal-math), made from its branch `vp-vnp`. It is not part of the upstream repository and nothing on it has been reviewed there; the cautions above apply to it unchanged. It differs from upstream `vp-vnp` in four points:

- **Toolchain.** Lean `v4.36.0` and Mathlib at the tag `v4.36.0` (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`), with the revisions of its dependencies that Mathlib pins; upstream uses Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- **The spelling of the coefficient.** Mathlib no longer has `MvPolynomial.coeff`: the coefficient of the monomial `d` in `p`, which upstream writes `coeff d p`, is written `p.coeff d`. This changes one line of `Statement.Approximates` and three theorems of `Paper` (`def_approx`, `approx_rate_closed`, `lem_transfer_approx`), and nothing else in any statement. [scripts/StatementSpelling.lean](scripts/StatementSpelling.lean) proves that every function with the defining laws of the coefficient is `p.coeff d`; [PORTING.md](PORTING.md) gives the four statements before and after, and the argument. Statement.lean therefore differs from the file printed in Section 3 of the paper in that line.
- **Proof repairs.** 28 repairs in 27 Lean files, for renamed Mathlib lemmas and changed definitions and elaboration, each listed with its reason in [PORTING.md](PORTING.md). No `sorry`, axiom or `native_decide` was added and no `maxHeartbeats` raised.
- **The Comparator files.** `Challenge.lean`, `Solution.lean` and `comparator.json` moved to [Comparator/VpVnp/](Comparator/VpVnp/), as the modules `Comparator.VpVnp.Challenge` and `Comparator.VpVnp.Solution` of the library `Comparator`, the layout the blueprint site generator this branch is prepared for accepts (a folder `Comparator/<Name>/` per challenge, its configuration without the key `enable_nanoda`). The two Lean files are unchanged, and the judged theorems keep their names (`Solution.mainTheorem` and so on: a namespace) and statements. The repository's `../.github/scripts/comparator-check.sh` looks for `comparator*.json` next to the lakefile and does not find this layout; [scripts/comparator-check.sh](scripts/comparator-check.sh) is that script with the search changed to `Comparator/<Name>/comparator.json` (Linux only; not run on this branch).

To build and check, in this folder:

    lake exe cache get
    lake build
    lake env lean scripts/PrintAxioms.lean
    lake env lean scripts/StatementSpelling.lean

`lake build` prints the five sorry warnings of Comparator/VpVnp/Challenge.lean and, besides them, deprecation and linter warnings from the new toolchain and Mathlib ([PORTING.md](PORTING.md)). `scripts/PrintAxioms.lean` names `propext`, `Classical.choice` and `Quot.sound` for each of the five theorems, and no other axiom; `scripts/StatementSpelling.lean` prints nothing.

To check the statements against upstream, with a Git remote `upstream` for anthropics/formal-math fetched:

    python3 -I scripts/statement-diff.py 918c8e2 9fd368ad

It compares every declaration of Statement.lean, the challenge, the solution, Paper.lean and Paper/ (theorems up to `:=`, definitions and structures in full, comments removed) and reports 733 entries the same (declarations, and for each file its other top-level commands) and the four above as changed only in the spelling of the coefficient (exit status 2; 0 means no change, 1 any other change).

At the port baseline `9fd368ad`, the five theorems were also checked outside Lean's kernel: the toolchain's exporter `leanexport` wrote them with every constant they depend on (61,815 declarations), and the two checkers that ship with Lean 4.36.0, `con-leche --verified` and `con-ron --verified`, each accepted the export.

## Paper

**[paper.pdf](paper.pdf)**: *VP ≠ VNP over every field*, by Claude (Anthropic). The full proof is its appendix.

## Lean proof

**1. Read the statement.** [Statement.lean](Statement.lean) states all of the above and imports only Mathlib. Lean checks the proofs, but no machine checks that this file says what is claimed. Appendix Q of [paper.pdf](paper.pdf) lists the Lean counterparts of the numbered statements (Table 3) and says where they differ.

**2. Check the proofs.** With [elan](https://github.com/leanprover/elan) installed, in this folder:

    lake exe cache get
    lake build
    lake env lean scripts/PrintAxioms.lean

The build prints sorry warnings from Challenge.lean only, which states the theorems without proofs for the fuller check. The last command should name no axiom other than propext, Classical.choice and Quot.sound.

For the original upstream development, Appendix Q.1 reports a Linux Comparator run with the independent kernel nanoda. The fork's [Linux script](scripts/comparator-check.sh) uses the port's directory layout. The blueprint's Project Stats page gives the checks performed for its own build.

## License

Apache 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
