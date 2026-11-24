# Group evaluation and dealing review

The baseline is 9fd368ad. The cohort consists of all 28 Nc/Grp files plus the 14 selected Nc/Dl files. “Body read” means the source definitions, statements and proof terms have been inspected. Elaboration and diff inspection are separate checks.

## Body reads

- Grp/PutDef, PutSum — inspected the branch when keys are exhausted, padding of the final packet, the positive-width hypothesis in division and the distinct-key lookup argument.
- Grp/Script, GroupThm — inspected the order of base, role and endpoint instructions, reversed inputs, the duplicate diagonal key and the accepting-run evidence used by the final GROUP theorem.
- Grp/Steps, SumPut — inspected the disjoint-write induction, its dependency on earlier cells, and the distinct-key guarantee for several stored strings.
- Grp/SumRole — inspected the accumulator in the channel sum and removed two list-index wrappers. Focused Lean elaboration passed.
- Dl/Names, GrpCost, Tab — inspected path injection, finite-name lookup, bounds for trie updates and the generated constructor equivalence for counting units. The group cost bound uses the same count and time definitions as its producer.
- Dl/Total — inspected the intermediate deterministic-state facts, preservation of named cells and the nine-phase sum over accepting executions.
- Dl/SizeScript — inspected the base, role and ending instruction estimates and the cubic bound, including the extra word-length charge for cut endpoints.

- Dl/SizeDeal, Inst, DealThm, Run, Run2, Scr — checked encoded names and lists, each script-template size estimate, continuation composition, cost accumulation and the assembled certificate for one cut.
- Grp/Role, RoleProg, StepRole, Trans, Lang, SumSim, SumBase, StepBase, BaseProg, Put — checked the finite simulations, typed-to-tree translation, absorbing branches for unavailable units, access to the diagonal entry, reversal of encoded words and agreement of bounded programs with the list semantics.
- Grp/Seg, SegSum, SumSeg — checked separator consumption and the decrease on remaining flags and tape; final segments are indexed by suffix length, including the empty suffix.
- Grp/GrpSteps, GrpVal, Facts — checked instruction ordering and disjoint writes, value aggregation, and the independent integer count recording acceptance when coefficients may cancel.
- Grp/GroupProg, GrpTime — checked binary-to-unary conversion, all five instruction dispatches, preservation of the bounded-trie invariant and the script fold. The time proof counts base, role and endpoint instructions independently; the last two use injections into the group’s cells.

## Independent comparison

The 4ae2954 diff preserves GROUP's inputs and three conclusions when unfolded. Its resource sums use the same two filtered finite sets and summands; removing the two transport proofs is valid. The relocated group evaluator budget uses the same formula.

## Checks

- 3fefdf0 — SumRole.lean passed standalone Lean checking.
- a2fe7af — NS1/Lists, Dl/SizeScript, Dl/SizeDeal and Dl/Inst elaborated sequentially in a private overlay using the network changes. This verifies both consumers of the shared encoded-list bound and the one-cut theorem that imports both.

- Dl/Bd1, Bd2, Bd3 — inspected the bounded readable-name invariant, the separation of the last content-guessing phase, all per-template costs and the length charge for concatenation. The first eight phases of Total and Bd2 were enumerated twice. Total now specializes the first eight phases to a continuation for phase nine. Checked Total, Cut and Bd2 in order against fresh focused artifacts.
- Grp/Base, Group, Pack — inspected tape segmentation, empty stores, positive packet width, agreement at boundary units and the two passes for writing/reading the packets.
- e95d65a — focused elaboration of Names and GrpCost passed. The trie update size proof uses the sum of child sizes; the unit-name cardinality follows directly from its constructor equivalence.

- Independently inspected 652e2fd and 27666e1 against the earlier definitions. Optional packet decoding sends absent to the empty word and present to the fixed-width bit word. Its positive-width hypothesis distinguishes these cases. The uniform length bound also holds for width zero.
- 7999713 — individually checked Lang after deriving the quoted-program case from runT.
- Every current source in the 42-module cohort passed individual Lean elaboration with focused dependencies. The individual results are in .lake/focused-groups/overall.log. These were source checks against compiled imports, separate from the owner's clean end-to-end build.
