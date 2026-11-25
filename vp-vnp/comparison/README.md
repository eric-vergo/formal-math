# VP versus VNP proof cleanup

The Lean 4.36 port at `9fd368ad` has 72,739 physical lines in its four proof libraries. The frozen cleanup at `34a07262` has 67,960, a reduction of 4,779 lines (6.57%) across eight fewer files. The five public theorem statements, Comparator directory and original paper match the port byte for byte. All five solution proofs use exactly `propext`, `Classical.choice` and `Quot.sound`. Both external checkers accepted a fresh export of all five results together. Some intermediate paper claims have a different proof, weaker coverage or no standalone Lean counterpart. [Source by round](source-rounds.md) · [Review of mathematical changes](reviews/final-rounds.md) · [Paper concordance](paper-routes.tsv).

| Proof-library measure | Port | Frozen proof | Difference |
| --- | ---: | ---: | ---: |
| Lean files | 320 | 312 | −8 |
| Physical lines | 72,739 | 67,960 | −4,779 |
| Code lines including mixed lines | 58,774 | 54,026 | −4,748 |
| Comment lines including mixed lines | 11,415 | 11,010 | −405 |
| Mixed code/comment lines | 5,010 | 4,600 | −410 |
| Blank lines | 7,560 | 7,524 | −36 |
| Source bytes | 3,419,272 | 3,212,736 | −206,536 |
| Written declaration commands | 4,631 | 4,641 | +10 |
| Written imports | 557 | 561 | +4 |
| Direct imports of the Mathlib umbrella | 27 | 24 | −3 |

## Changes across rounds

Eric Vergo and GPT-6.2 (OpenAI) removed 2,453 physical proof lines in the first round. The real permanent theorem specializes the all-fields result, and exact circuits enter the shared border proof by lifting constants at the same size. The real class-separation corollary still uses permanent membership via Ryser’s formula. The machine decoder uses one opcode inversion theorem. Common VNP packaging serves Hamiltonian cycles and the permanent, each with its own witness. The tree assembly separates specification, construction and quantitative bounds. [Source by round](source-rounds.md) · [Initial review ledgers](modules.md).

Claude Fable 5.2 (Anthropic) directed the next round and Claude Opus 5.5 agents made its edits. It removed a further 1,089 physical proof lines and one module, reaching 69,197 lines. Exact flat and contracting bounds follow from the border bounds. The approximate scale-up carries a predicate on the constants, allowing exact recovery for K.6. Coverage changed for E.5’s explicit configuration and sharper 1/6 bound, K.3’s exact accelerator, K.5’s standalone exact scale-up, and H.2(c)’s layer count. The retained flat route gives the logarithmic estimate with divisor 14 and E.10’s printed bound with divisor 16. [Claim-by-claim review](reviews/final-rounds.md).

The final Codex rounds removed a further 1,237 physical proof lines. The scale induction uses 3α cuts and an explicit larger intermediate budget. The cut theorem consumes the exact block count. Finite joint laws give the random price extension directly. Finite Laurent circuits persist through field transfer, affine projection and both rate branches. Balanced hubs work over commutative semirings. The finite circuit has the same gate budget as its arbitrary-series counterpart. Affine projection has a separate factor-five simulation. [Quantifiers, constants and lost intermediates](reviews/final-rounds.md).

An assisted tactic search selected 441 short live proof bodies in 42 files across six machine, group, tower and flag directories. It favored files with multiple short tactic proofs and tried short scripts derived from the existing proof. Eighteen bodies in 13 files passed the review and replacement, with 20 inserted and 123 deleted physical lines at `1a93f42`. The other 423 have no accepted replacement from this search. The yield measures this selected sample and tactic family. It cannot predict the percentage of all proofs admitting simplification. [All probe outcomes](reviews/proof-probes.tsv) · [Accepted patch](https://github.com/eric-vergo/formal-math/commit/1a93f42).

## Kernel dependencies and external replay

| Checked root | Port constants | Frozen constants | Change |
| --- | ---: | ---: | ---: |
| Exact all-fields lower bound | 61,727 | 57,576 | −4,151 |
| Exact class separation | 61,823 | 57,669 | −4,154 |
| Border all-fields lower bound | 63,277 | 57,650 | −5,627 |
| Closure separation | 63,281 | 57,654 | −5,627 |
| Real permanent | 58,716 | 57,576 | −1,140 |
| Union of the five | 63,353 | 57,687 | −5,666 |
| Project-owned constants in that union | 10,291 | 9,969 | −322 |

The intermediate Fable handback used 63,091 distinct constants and 10,007 project constants across the five roots. At an earlier checkpoint, sharing the border argument enlarged the real permanent root from 58,716 to 63,120 constants. At the freeze it fell below baseline. In a focused component comparison the closure of `Paper.prop_random_finite` fell from 36,409 to 29,183 constants. That local difference of 7,226 cannot be added to differences at other roots. The final whole-graph walk independently confirms that `PMF.ofFintype` and `MeasureTheory.integral` disappeared from the union. The fully general measurable price theorem remains available. [Measurement definitions](inventory-method.md) · [Finite-law construction](../Paper/Prices.lean).

The fresh five-root export fell from 61,815 declaration records (629,490,907 bytes) to 56,219 (573,775,162 bytes). Both `con-leche --verified` and `con-ron --verified` accepted the full export in each run. The final export SHA-256 is `bfc31ba34d18983778a7bf88107f20fb79cdd059cbb8737c2d21c029a76e9175`. Lean's graph walk counts reachable constant names, including names that the export format does not enumerate as individual declaration records. The site replay includes a wider selection of blueprint roots and is measured separately. [Benchmark procedure](benchmark-method.md).

## Imports and build measurements

Narrowing imports can increase the number of explicit import commands. In focused module checks the Mathlib-prefixed module count fell from the umbrella’s 8,713 to 1,111 at `Nc.LowDegree` and 960 at `Nc.Tape.Rep`. Along the sum-machine chain, the total imported-module environment fell from 11,126 to 2,502 at `NS1.Machine`, from 11,129 to 2,526 at `NS1.Eval`, from 11,135 to 2,787 at `NS1.Comp`, from 11,137 to 3,507 at `NS1.Main`, and from 11,138 to 3,569 at `NS1.ApproxOrd`. These counts use different filters, recorded for the affected module environments. Other roots still import Mathlib. Neither the local environment count nor the kernel constant count measures compile time. [Proof source by round](source-rounds.md) · [Build protocol](benchmark-method.md).

## Authorship and reproduction

The original paper and formalization are by Claude (Anthropic). The port and initial fork blueprint are by Eric Vergo and Claude. Helen Kwok’s Apache-2.0 adaptations appear in six credited files. Comparison with OpenAI’s independent manuscript informed an intermediate square calculation that was subsequently removed. OpenAI’s published Lean comparator has its own scope. [Attribution, source pins and licenses](related-proofs.md) · [Notice](../NOTICE).

The source-round table can be regenerated with `python3 -B comparison/source-rounds.py` from the project directory. The complete inventory and runtime reports use separate compiled and rendered inputs. [Source inventory method](inventory-method.md) · [Build, site and replay method](benchmark-method.md).
