# Network and machine proof review

The baseline assignment covers 183 files. A structural scan is not a full proof-body review. The full file list below distinguishes those checks. Entries are updated as more files are read.

- Cut/Facts and Dl/Facts define the same three estimates. The former now supplies both constructions. The retained finite-sum division proof uses induction, the concatenation identity unfolds list length, and the unit estimate sums these bounds over parties. The Dl-specific weight and initialization arguments remain in Dl/Facts.
- RunWord uses emit_none through simplification in the proofs for length and existence of an emission. The inverse to reading a separated list of words uses strong induction to identify earlier offsets. Retain the simp rule and both directions of the encoding.
- FinDom's one-hot equivalence needs both failure cases, for a missing value and two values at one point. Remove the empty projection section.
- RunOne transports emissions, matching, and weights under a permutation of input names. Retain the explicit inverse witness in the matching argument.
- RunPerm counts letters, transition records and assignments separately, with distinct polynomial bounds. Remove its empty section.
- Tape/Loop bounds the series of a single word by peeling off the first letter. Replace the double finite-sum rewriting of the zero tail with a single zero-sum proof; remove the empty Phases section.
- Tow/FromPriceK restricts a law to a subring; Tree/Network maps in the other direction. Their identity proofs differ. Both share the original combinatorial fields.
- Tree/Network retains cutUnits_id_cur: the main theorem's written statement explicitly cites it to recover the printed formula without self-loops.
- Uni/EvThm, EvThm2, EvThm3 and TopU now use a single invariant for all eleven formula constructors and a common register-load step. The parsing and evaluation return modes call the same lemma. Their recursive witnesses still have different meanings.
- Tree split separates network specification, tree construction, quantitative bounds and assembly. The internal tree load lemma isolates the real-power saving from choosing tree data.

## Baseline files

- Nc/Cut/Blocks.lean — full proof-body read (zero-step path is a single state; positive paths split first vertex, and emitted blocks are grouped by fibers)
- Nc/Cut/Codes.lean — full proof-body read
- Nc/Cut/Defs.lean — full proof-body read
- Nc/Cut/Exact.lean — full proof-body read
- Nc/Cut/Facts.lean — full proof-body read
- Nc/Cut/Groups.lean — full proof-body read (group factorization glues consistent boundary assignments; a move separates agreement on retained units from new units)
- Nc/Cut/Play.lean — full proof-body read (explicit split of contents and reconstruction supply both directions of the bijection)
- Nc/Cut/Rows.lean — full proof-body read (induction on rows fixes earlier endpoint maximum, and injectivity of coded segments uses the first delimiter)
- Nc/Cut/Slp.lean — full proof-body read
- Nc/Cut/StartA.lean — structural scan only
- Nc/Cut/StartB.lean — full proof-body read
- Nc/Cut/Units.lean — full proof-body read (padding recovers original length, equal fixed-width encodings force equal numbers of letters)
- Nc/Dl/Bd1.lean — structural scan only
- Nc/Dl/Bd2.lean — structural scan only
- Nc/Dl/Bd3.lean — structural scan only
- Nc/Dl/Code.lean — full proof-body read
- Nc/Dl/Cost.lean — full proof-body read
- Nc/Dl/Cut.lean — structural scan only
- Nc/Dl/DealThm.lean — structural scan only
- Nc/Dl/Does.lean — full proof-body read
- Nc/Dl/Facts.lean — full proof-body read
- Nc/Dl/GrpCost.lean — structural scan only
- Nc/Dl/Inst.lean — structural scan only
- Nc/Dl/Last.lean — full proof-body read
- Nc/Dl/Names.lean — structural scan only
- Nc/Dl/Num0.lean — full proof-body read
- Nc/Dl/Phases.lean — full proof-body read
- Nc/Dl/Run.lean — structural scan only
- Nc/Dl/Run2.lean — structural scan only
- Nc/Dl/Scr.lean — structural scan only
- Nc/Dl/SizeDeal.lean — structural scan only
- Nc/Dl/SizeScript.lean — structural scan only
- Nc/Dl/Tab.lean — structural scan only
- Nc/Dl/Total.lean — structural scan only
- Nc/FinDom.lean — full proof-body read
- Nc/Flag/Act.lean — full proof-body read
- Nc/Flag/Avg.lean — full proof-body read
- Nc/Flag/Block.lean — full proof-body read
- Nc/Flag/Blow.lean — full proof-body read
- Nc/Flag/Cases.lean — full proof-body read
- Nc/Flag/Exchange.lean — full proof-body read
- Nc/Flag/Len.lean — full proof-body read
- Nc/Flag/Main.lean — full proof-body read
- Nc/Flag/Num.lean — full proof-body read
- Nc/Flag/Para.lean — full proof-body read
- Nc/Flag/Rank.lean — full proof-body read
- Nc/Flag/Transversal.lean — full proof-body read
- Nc/Flag/Uni.lean — full proof-body read
- Nc/Flag/Walk.lean — full proof-body read
- Nc/Flag/Window.lean — full proof-body read
- Nc/Flag/Words.lean — full proof-body read
- Nc/G/Contract.lean — full proof-body read (injective channel codes and connectivity reconstruct one global index; power commutes the two finite products)
- Nc/G/Defs.lean — full proof-body read (proxy equivalence decomposes the sum over initial and newly produced units; remaining constructions are definitions)
- Nc/G/Exact.lean — full proof-body read (nonzero local factors guarantee each held initial or channel unit is present, including the extra-party exclusion)
- Nc/G/Move.lean — full proof-body read (role table contraction, empty role case, unique channel outcome, and the slot equality indicator)
- Nc/G/PlayThm.lean — full proof-body read (causality of outcomes, seen and consumed units, and bijective prefix extension in the move induction)
- Nc/G/RouteFacts.lean — full proof-body read
- Nc/G/Start.lean — full proof-body read (row/column packet equality recovers each segment in the map from initial positions; factored the unrestricted position sum)
- Nc/Grp/Base.lean — structural scan only
- Nc/Grp/BaseProg.lean — structural scan only
- Nc/Grp/Facts.lean — structural scan only
- Nc/Grp/Group.lean — structural scan only
- Nc/Grp/GroupProg.lean — structural scan only
- Nc/Grp/GroupThm.lean — full proof-body read
- Nc/Grp/GrpSteps.lean — structural scan only
- Nc/Grp/GrpTime.lean — structural scan only
- Nc/Grp/GrpVal.lean — structural scan only
- Nc/Grp/Lang.lean — structural scan only
- Nc/Grp/Pack.lean — structural scan only
- Nc/Grp/Put.lean — structural scan only
- Nc/Grp/PutDef.lean — full proof-body read
- Nc/Grp/PutSum.lean — full proof-body read
- Nc/Grp/Role.lean — structural scan only
- Nc/Grp/RoleProg.lean — structural scan only
- Nc/Grp/Script.lean — structural scan only
- Nc/Grp/Seg.lean — structural scan only
- Nc/Grp/SegSum.lean — structural scan only
- Nc/Grp/StepBase.lean — structural scan only
- Nc/Grp/StepRole.lean — structural scan only
- Nc/Grp/Steps.lean — structural scan only
- Nc/Grp/SumBase.lean — structural scan only
- Nc/Grp/SumPut.lean — structural scan only
- Nc/Grp/SumRole.lean — full proof-body read
- Nc/Grp/SumSeg.lean — structural scan only
- Nc/Grp/SumSim.lean — structural scan only
- Nc/Grp/Trans.lean — structural scan only
- Nc/RunGood.lean — full proof-body read (path expansion, input delimiters, blank writes and unique reached configuration)
- Nc/RunMn.lean — full proof-body read (one-hot constraints, valid-code uniqueness, line restriction and degree via products)
- Nc/RunOne.lean — full proof-body read
- Nc/RunPerm.lean — full proof-body read
- Nc/RunSum.lean — full proof-body read (hard clauses for overflows, blanks and separators, and soft transition factors)
- Nc/RunWord.lean — full proof-body read
- Nc/SlpCalc.lean — full proof-body read (straight-line normalization, variable sets and indicator gate evaluation)
- Nc/Sort/Radix.lean — full proof-body read (stable bitwise radix order and checking each key against its table entry)
- Nc/Sort/RunVal.lean — full proof-body read
- Nc/Sort/Runs.lean — full proof-body read (product disjointness and strict suffix-length decrease for finite Kleene-star fibers)
- Nc/Sort/Words.lean — full proof-body read
- Nc/Tape/Hat.lean — full proof-body read (channel length bounds fibers; cutting a word identifies two projected fibers; star excludes empty prefixes)
- Nc/Tape/Loop.lean — full proof-body read
- Nc/Tape/ProgRun.lean — full proof-body read (unique nonzero split for padding, normalization and bounded projection fibers)
- Nc/Tape/Rat.lean — full proof-body read (the new terminal state has zero diagonal entry on nonempty words in both branches)
- Nc/Tape/Refine.lean — full proof-body read (staircase gives the first joint cell and uniqueness by deleting its first letter; pullback along Fin.succ preserves updates)
- Nc/Tape/Rep.lean — full proof-body read (Cauchy multiplication and positive-factor star share the one-letter split of the prefix sum)
- Nc/Tape/Run.lean — full proof-body read
- Nc/Tape/Task.lean — full proof-body read
- Nc/Tow/Cap.lean — full proof-body read (isolated single-level algebraic gain before powering; ceilings and endpoint estimates bound the move capacity)
- Nc/Tow/CapOk.lean — full proof-body read
- Nc/Tow/Cards.lean — structural scan only
- Nc/Tow/Cst.lean — full proof-body read. Retain the explicit target-type equivalence, whose sigma and product cardinalities supply the three separate polynomial estimates in card_Tg_le. The real-to-natural ceilings for capacity and the final-level power estimate use different bounds.
- Nc/Tow/Defs.lean — full proof-body read
- Nc/Tow/EndA.lean — structural scan only
- Nc/Tow/EndB.lean — structural scan only
- Nc/Tow/EndC.lean — full proof-body read
- Nc/Tow/Ends.lean — full proof-body read
- Nc/Tow/Ever1.lean — full proof-body read
- Nc/Tow/Ever2.lean — full proof-body read
- Nc/Tow/Ever3.lean — structural scan only
- Nc/Tow/Ever4.lean — full proof-body read
- Nc/Tow/Ever6.lean — full proof-body read
- Nc/Tow/Ever7.lean — full proof-body read
- Nc/Tow/Flow.lean — full proof-body read
- Nc/Tow/FromPrice.lean — full proof-body read
- Nc/Tow/FromPriceK.lean — full proof-body read
- Nc/Tow/Load.lean — full proof-body read
- Nc/Tow/Load0.lean — structural scan only
- Nc/Tow/Load2.lean — full proof-body read by blueprint agent (shared final middle-relay bound with Ever2; endpoint sum separates its two endpoints from the complement)
- Nc/Tow/Load3.lean — structural scan only
- Nc/Tow/Load4.lean — structural scan only
- Nc/Tow/Net.lean — full proof-body read
- Nc/Tow/Ok.lean — full proof-body read
- Nc/Tow/Path.lean — full proof-body read
- Nc/Tow/PlaceE.lean — full proof-body read
- Nc/Tow/Plan.lean — full proof-body read
- Nc/Tow/Rank.lean — full proof-body read
- Nc/Tow/Relay.lean — full proof-body read
- Nc/Tow/Slp0.lean — full proof-body read
- Nc/Tow/Slp1.lean — full proof-body read
- Nc/Tow/Slp2.lean — full proof-body read
- Nc/Tow/Slp3.lean — full proof-body read (five choice stages followed by an eight-stage recurrence, then loads at terminal time)
- Nc/Tow/Slp4.lean — full proof-body read (rank and consumption cardinalities, both unit constructors, final nine-stage circuit)
- Nc/Tow/Slp5.lean — full proof-body read
- Nc/Tow/Tree.lean — full proof-body read
- Nc/Tower/Base.lean — full proof-body read
- Nc/Tower/Chain.lean — full proof-body read
- Nc/Tower/Coord.lean — full proof-body read
- Nc/Tower/Diam.lean — full proof-body read
- Nc/Tower/Grp.lean — full proof-body read
- Nc/Tower/Inst.lean — full proof-body read
- Nc/Tower/Layer.lean — full proof-body read
- Nc/Tower/Ring.lean — full proof-body read
- Nc/Tower/Tower.lean — full proof-body read
- Nc/Tower/UT.lean — full proof-body read
- Nc/Tower/Words.lean — full proof-body read
- Nc/Uni/Alpha.lean — full proof-body read
- Nc/Uni/Bin.lean — full proof-body read (word inversion via bounded tails, binary increment and uniqueness of the trailing run)
- Nc/Uni/Bounds.lean — full proof-body read
- Nc/Uni/CmpU.lean — full proof-body read (both record projections establish the adjacent-pair witness)
- Nc/Uni/Det.lean — full proof-body read (shared special-rule exclusion in deterministic and stuck branches)
- Nc/Uni/EvThm.lean — full proof-body read (constructor invariant for quote, id and failures, including nil quotes and oversized opcodes)
- Nc/Uni/EvThm2.lean — full proof-body read (frame and register invariants for head, tail, ordered cons and two distinct conditional branches)
- Nc/Uni/EvThm3.lean — full proof-body read (nested bill-free totals under three evaluations; two distinct guess successors; mul and theta have distinct halt and name semantics)
- Nc/Uni/EvalU.lean — full proof-body read (opcode scanner advances via one forced rule in both accepted and overflowing cases; prefix length controls name reading)
- Nc/Uni/Exist.lean — full proof-body read (counter cuts and binary register projections reconstruct a matched run from the trace)
- Nc/Uni/LenU.lean — full proof-body read (sum all eight tape lengths via their exact projections)
- Nc/Uni/PM.lean — full proof-body read (closed heaps force lookups from previous allocations and finite trace sums split by first step)
- Nc/Uni/Prog.lean — full proof-body read (tape-by-tape program emissions for counters, input, transitions, halt and appended records)
- Nc/Uni/Rules.lean — full proof-body read (retain the rule table and explicit record-kind enumeration; load register depends only on source mode)
- Nc/Uni/SortU.lean — full proof-body read (radix redistribution, collecting buckets and the final record monitor)
- Nc/Uni/SpecU.lean — full proof-body read (first delimiter recovers a block, monitor emissions match per bucket and named channel)
- Nc/Uni/SpecU2.lean — full proof-body read (delimiter-free blocks, unique radix pass witnesses, and final table equivalence for nonempty input)
- Nc/Uni/TopU.lean — full proof-body read (bracket parsing uses two frames, parser return sets up evaluator; zero-address and elapsed-cost invariants verified)
- Nc/Uni/Trace.lean — full proof-body read (column recovery, freshness chains, binary-width bounds, and reconstructing unique machine traces)
- Nc/Uni/Vals.lean — full proof-body read (derive all fifteen tape-projection formulas directly, then invert the mode, bits and self-delimiting word encodings)
- Paper/Cuts.lean — structural scan only
- Paper/Groups.lean — structural scan only
- Paper/Heavy.lean — structural scan only
- Paper/HeavyProg.lean — structural scan only
- Paper/Laws.lean — selected proof bodies
- Paper/Lengths.lean — structural scan only
- Paper/Pieces.lean — structural scan only
- Paper/Runnet.lean — full proof-body read (network equality then nonzero-table summand yields the incidence bound)
- Paper/Tower.lean — full proof-body read (assembled fibre, free action, generation and word length bounds)
- Paper/Tree.lean — selected proof bodies

The short interface files Flag/Cases, Cut/Slp, Grp/PutDef, Dl/Cost, and Tape/Run define the data or predicates their callers use. Flag/Num applies convergence at L+1. Cut/Exact propagates nonzero local tables to each endpoint. Tow/PlaceE numbers the original nodes before their complement. Dl/Last constructs its finite-support table from algebra generators. Flag/Main proves translation preserves squared distance. Cut/StartB contained only two Mathlib special cases.

The entire RouteFacts module duplicates membership lemmas in G.Move and G.PlayThm; its one external caller can use Plan.mem_seenAt_end directly. Uni/Bounds.tU_le compares polynomials with natural coefficients, so normalization plus linear arithmetic suffices. Tower/Chain uses Sylow and dependent recursion; retain the recursion as it supplies compatible subgroups. Sort/RunVal needs both directions of Mt.eq_tup and Mt.of_tup. Flag/Avg separates zero radius to justify cancellation. Grp/GroupThm combines plain evaluation with the necessary counting obligation. Tow/CapOk turns real estimates into natural packet capacities. Cut/Codes controls HEq of dependent codeword widths.

Tow/Rank counts ranks by injectivity within each fiber. Tow/Tree uses the least minimizer to define the parent; keep this tie-breaking rule. Sort/Words uses prefix cancellation, and UnI/Alpha builds record symbols and runs over words on several tapes. Grp/SumRole carries the output accumulator through its induction. Cut/Defs and Tow/Defs supply distinct interfaces. Dl/Does ties together three resource estimates and the enabled templates. Grp/PutSum handles both the final short packet and exact multiples of the packet width. Dl/Code can derive the finite enumeration of seventeen constructors and obtain code injectivity from decoding the numeric value.

The dealing estimates use monotonicity and polynomial normalization after shifting the variables by their lower bounds. The setup time and size estimates are now private lemmas. The relay endpoint proof distinguishes initial, interior, mid-stage and final relays; the law endpoint proof uses the tower numbering bijection. The relay sum equivalence is used for both cardinality and summation.

Tower.UT proved matrix multiplication closure twice while constructing its group of upper unitriangular matrices. Tower.Coord can choose the previous cyclic index directly. Tower.Base bounds the lift in the polynomial diameter proof; the matrix-generation argument uses transvections from the standard diagonal decomposition.

Flag.Words and Tower.Coord established the same generator involution independently. Hoist it beside the matrix generator. The word proof builds a column inductively and obtains the row via antidiagonal reflection. Tower.Ring accounts for the possible zero quotient at level zero, so an unconditional CharP 2 instance would be incorrect.

Flag.Uni proves that the two disjoint window projections sum to the identity by partitioning rows into the two intervals. Factor out the common projection-row calculation. Flag.Exchange separately handles paired and triple transversality of row and column spaces and uses the binary field for the span of one vector.

Tow.Load keeps separate bounds for middle segments and end segments, then applies the stage contraction. Flag.Walk proves monotonicity under truncation by classifying the generators killed by truncation.

Flag.Act uses barycentre uniqueness for projection equivariance and fixedness; angle_num derives the scalar bound from the quadrangle inequality at the chosen interpolation parameters. Flag.Transversal builds independent columns first and transports the argument to rows by transposition.

Flag.Window and Flag.Uni had the same orthogonality calculation for disjoint windows. Use the arbitrary disjoint-window theorem for the two adjacent blocks. Flag.Blow extends the nonunital blow-up by its complementary idempotent before reindexing average displacement.

Flag.Block uses the strict upper-right support twice, for entries below and on the diagonal. Factoring the support calculation proves both in one place.

Tower.Layer obtains injectivity and the trace-zero condition from the same nonvanishing of the top coefficient, and surjectivity at level zero is a special case of the general surjectivity theorem.

Tower.Diam decomposes trace-zero matrices into elementary layers and then lifts generator words. The two product identities for the diagonal layer use the square-zero coefficient and are algebraically distinct.

Tower.Words repeats the adjacent-generator construction in both cases of the induction on the gap. Tower.Grp checks shifted-root generator identities separately at and away from the wraparound index.

Tower.Tower constructs routes from generator words. Its factor of two comes from the two starting chambers for one edge; the separate factor of two for near pairs comes from reversing orientations. Use the library subtype sum for the chosen orientations.

Tower.Inst constructs hosts fibrewise and proves the edge and coset covering bounds from the same chamber fibre. Its near-pair bijection uses the unique chosen orientation to resolve a possible flip in the injectivity proof.

Tow.Flow proves causal agreement of prefix loads and outcomes. A nonzero prefix count places its move strictly before the cutoff, directly by contraposition of numS_zero_of_le.

Tow.Ever2 splits the per-node relay estimate into the inner, middle, and final relay bounds. All three count endpoint loads using the same filtered identity. Tow.Ever1 handles the boundary cases for level zero and the last stage separately.

Tow.Plan and Tow.Ever4 both hand-wrote the unit-name equivalence to split a sum into initial and channel units. Move the generic sum rule to the inductive type and reuse its generated equivalence. Tow.Path derives the endpoint and nonloop properties from one walk_step witness. Tow.Slp5 separately certifies host indicators and chamber loads.

Tow.EndC distinguishes full units from their last partial unit via the blocksize and the squared channel bounds. Tow.Ever4 sums their two possible holders; Tow.Ever6 specializes the estimate to base, higher, and root chambers.

Tow.Ever7 and Ever4 independently bounded the sum over valid relays by the same total. The full node estimate sums the channel, relay, and zero-padding contributions.

Tow.Slp0 lifts ordinary instruction counts to powers of the alphabet-size parameter; all unary instructions and all binary instructions reuse two numerical inequalities. Tow.Slp1 bounds the search for a law that fits using the local norm.

Tow.Slp2 repeated the cardinal bound on all units having a specified initial target. Reuse the same bound for bt and for sizing the program’s intermediate range.
