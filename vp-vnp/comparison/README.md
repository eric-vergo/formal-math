# VP versus VNP proof cleanup

The baseline is the Lean 4.36 port at `9fd368ad`. The after revision `eeff2161cb51c2ac871ffba3afccdee7028e56e4` names the cleaned proof and the revised blueprint. Both use the same pinned Lean, Mathlib, and blueprint dependencies. The measured after revision precedes the generated comparison tables and data, so the tracked-size comparison excludes those reporting outputs. It includes the measurement code already present at the pinned revision.

| Proof-library measure | Before | After |
| --- | ---: | ---: |
| Lean files | 320 | 313 |
| Physical lines | 72,739 | 70,286 |
| Code lines | 58,774 | 56,398 |
| Total named theorem and lemma body lines | 46,110 | 43,822 |
| Median body lines | 7 | 6 |
| Longest body lines | 340 | 275 |
| Bodies over 200 lines | 7 | 4 |
| Exact matches among normalized bodies, groups of at least five lines | 12 | 4 |

The local build samples and full-site verification are in progress. The source measurements below use the measured revision.

[All measurements](data.md) · [Disposition of every baseline module](modules.md) · [Source counting rules](inventory-method.md) · [Benchmark procedure](benchmark-method.md) · [Related proofs and forks](related-proofs.md)

## How the proof changed

- The real permanent bound `Paper.thm_main` specializes the all-fields theorem at characteristic zero. The exact bound maps each gate to Laurent series with unchanged size and applies `Paper.border_rate_allfields`. The shared lemma absorbs the separate exact-rate dispatch. The printed exact flat-case, contracting and transfer lemmas remain formalized and documented. `Paper.common_family_threshold` combines the Hamiltonian-cycle threshold and, away from characteristic two, the permanent threshold. The real class-separation corollary still uses permanent membership via Ryser's formula.
- `Paper.thm_flat_simple` follows from the quantitative `Paper.thm_flat_rate`. The lemma `Paper.excludes_poly_size` uses the growing exponent to handle any fixed polynomial budget. The separate sharper estimate `Paper.prop_flat_lower` remains a distinct geometric argument.
- `Paper.exists_thinTrees` assembles the network specification, construction and estimates in separate modules. A shared estimate gives both the per-node power saving and the total packet bound used to choose the final tree. Separating those obligations shortens the assembly body and leaves the numerical estimates visible at their own statements.
- `Paper.thm_onecut` fixes a uniform evaluator bound over every admissible symbol code before choosing the scale. Separate lemmas give the common law-role alphabet bound and show that the universal evaluation fits within the rounded block budget.
- Machine proofs now use `NS1.Fm.codeShape_of_decode` to obtain the opcode and operands from one inversion theorem. For dealing, `Nc.Grp.GroupOK` gives the producer's group evaluator specification and both callers use that cost model. Code reuse respects the separate obligations for machine state, value and acceptance.
- `Nc.Hc.mem_VNP_of_quartic_witness` supplies the common VNP packaging for Hamiltonian cycles and the permanent. Each polynomial still has its own witness circuit and its own proof that summing the witness produces that polynomial.

The named proof comparison gives body sizes and source locations. [Selected proof rewrites](data.md#selected-proof-rewrites). The one-cut body goes from 340 to 275 code lines. Its whole module goes from 578 to 585 physical lines and from 523 to 520 code lines. The piece-bound proof grows by 12 body lines against baseline and succeeds at the default heartbeat limit after expressing the bounds explicitly. The adaptations credit Helen Kwok’s work and the independent research comparison credits OpenAI’s proof. [Related proofs and forks](related-proofs.md).

The full five-export closure drops from 63,353 to 63,231 constants, including a drop from 10,291 to 10,145 project constants. Sharing the coefficientwise argument has a cost when checking an exact result on its own. The real permanent closure grows from 58,716 to 63,120 constants. The closures of both border exports shrink by 78 each. The local Comparator import DAG drops from 321 to 314 modules and from 508 to 488 edges. Its longest path grows from 38 to 39 edges. [All five closures](data.md#kernel-dependency-closures).

The authored blueprint directly cites 47 source theorems outside the five export closures, up from 33. The paper concordance separates principal statements from supporting declarations and records the compiled routes. The source inventory also identifies 21 theorems outside both the judged and authored blueprint closures. The late shared border route added none to this list. Examples retained for exposition include the Meixner generating-series equations, mean-norm homogeneity, and the loop-free spelling of the thin-tree formula. Several other entries are public simplification rules. [Exposition-only proofs](data.md#named-exposition-proofs-outside-all-five-exports) · [Paper concordance routes](paper-routes.tsv).

## What was checked

The public statement, whole Comparator directory and `paper.pdf` match the baseline byte for byte. All five solution exports have only `propext`, `Classical.choice` and `Quot.sound` in their kernel dependencies. The five challenge proofs intentionally use `sorry`. They contribute explicit warning lines and written declarations in the project totals. The solution closure and proof-size distribution exclude them.

The render comparison tracks graph nodes and edges, Lean-backed progress, and external checker coverage separately. A node can have a checked Lean declaration and an informal statement. An informal statement's correspondence to the declaration is a human claim. The blueprint keeps those claims and the paper's meaning audit visible. The graph renderer omits a neighbourhood drawing when it exceeds 150 nodes or would exceed the 192 MiB drawing budget. The full graph node and edge totals still count the underlying graph. The compiled dependency inventory counts named source theorems separately from compiler-generated constants, and tracks authored exposition outside the judged export closures. Generated listings cover whatever source the generator sees.

The integrated proof build, the five kernel axiom checks and the paper concordance route audit passed at the after revision.

## Hosted workflow timings

These are single GitHub Actions observations. The hosted project-and-site step combines operations outside the local proof-only benchmark and is reported separately.

| Hosted phase | Before | After |
| --- | ---: | ---: |
| Build job | 27m 52s | Pending |
| Project and site step | 21m 56s | Pending |
| Deploy job | 20s | Pending |

[Baseline GitHub Actions run](https://github.com/eric-vergo/formal-math/actions/runs/45355758423)

## Independent source reviews

The module ledger accounts for all 319 baseline modules in four review cohorts. Independent reviews covered the ten longest bodies, repeated proof patterns, and the public and paper specifications. [Longest proofs](reviews/longest.md) · [Duplication review](reviews/duplicates.md) · [Specification review](reviews/specification.md).

## Regenerating the tables

```bash
cd vp-vnp/comparison
python3 compare.py --before inventory-baseline.json.gz --after inventory-after.json.gz > data.md
python3 module-disposition.py --before inventory-baseline.json.gz --after inventory-after.json.gz \
  --reviews reviews > modules.md
```

The local measurement host was an Apple M2 Ultra with 64 GiB of unified memory, 16 performance cores and eight efficiency cores. The raw rows record host load at the start of each sample.

The two inventories hold the per-file, per-proof and compiled-export inputs. [Baseline inventory](inventory-baseline.json.gz) · [After inventory](inventory-after.json.gz).
