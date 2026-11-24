# Contracting proof review

Each entry records the source declarations inspected and the change or retention decision. Focused Lean checks exercise edited modules; independent whole-project validation is coordinated separately.

The proof lists below are a declaration inventory, not evidence that each body was read. I scanned all 47 files for repeated source blocks and independently inspected the edited proof blocks. Complete body-by-body reading is now underway.

Full-file body reads so far: NS1/{Accel,ApproxAdd,ApproxMain,ApproxScale,ApproxOrd,Budget,Deal,Diag,Eval,Finite,Interp,Main,Parts,Picks,Scale,Step,Util}, Nc/Acc/{ApproxMain,Line,LowDeg,Main,Trie}, Paper/{Postpone,Scales,Universal,UniversalSteps}. Other files have only selected bodies or source-index coverage at this stage.

## NS1/Accel.lean

Plain.mono belongs beside Plain. Kept the direct evaluation of the universal formula and the postponed instance; each converts an actual evaluation witness to size and weight facts.

Proofs: `Plain.mono`, `IsAccT.pre`, `IsPre.mono`, `IsAccT.mono`, `bill_le`, `UF_ev`, `val_plain`, `UF_pre`, `zq_plain`.

## NS1/ApproxAdd.lean

Retained the distinct carry cases. The induction on binary words establishes length, arithmetic value and deterministic execution at different levels.

Proofs: `length_addc`, `val_addc`, `addBr_dt`, `AD_dt`.

## NS1/ApproxBack.lean

Extraction first checks the exponent, then invokes the interpreter. Size bounds for the syntax of xF depend on each trie constructor and are not the evaluation invariant.

Proofs: `KV.app_rel`, `finF_kv`, `nds_coefK`, `ht_coefK`, `extF_kv`, `xcst_def`, `size_chT`, `size_xF`, `size_extF`.

## NS1/ApproxExtract.lean

Kept the coefficient projection, residue-class wrap and xF evaluation separate. The two choices in chT_ev inspect distinct halves of the coefficient trie.

Proofs: `RelX.mono`, `chT_ev`, `length_expBits`, `cast_val_expBits`, `mark_addc`, `wrap_apply`, `coeff_wrap_zero`, `sum_words_range`, `sum_words_split`, `sum_terms`, `length_xL`, `bt_xL`, `sum_xL`, `combF_dt`, `xF_ev`.

## NS1/ApproxMain.lean

The final accelerator predicate and logarithm estimate are already small.

Proofs: `le_lg_four`.

## NS1/ApproxOrd.lean

Order, exponent span and number of terms of a power are distinct invariants. Kept their closure proofs and the rescaling support argument.

Proofs: `coeff_algebraMap`, `exists_coeff_mul_ne_zero`, `OrdGE.zero`, `OrdGE.mono`, `OrdGE.add`, `OrdGE.mul`, `OrdGE.list_sum`, `OrdGE.of_algebraMap`, `OrdGE.prod_sub`, `Span.mono`, `Span.ordGE`, `Span.zero`, `Span.of_algebraMap`, `Span.one`, `Span.add`, `Span.mul`, `Span.pow`, `Span.card_support`, `coeff_rescale_ne_zero`, `OrdGE.rescale`, `Span.rescale`, `card_support_rescale`, `Span.thin`, `Thin.rescale`, `All.imp`, `All.map`, `All.expand`, `exists_bound`, `exists_span`, `span_budg`.

## NS1/ApproxRound.lean

Rebilling requires translating names through the right subtree and rescaling the coefficient. The corresponding exact evaluator has no comparable error statement.

Proofs: `gt_map`, `nds_expand_map`, `rebF_kv`, `rebill_kv`, `stepA_kv`, `IsAccA.pre`, `IsAccA.mono`, `UF_preA`.

## NS1/ApproxScale.lean

The round-size estimate counts concrete syntax, and the span estimate composes power and budget bounds. Both proofs are short.

Proofs: `size_roundA`, `span_expand_budg`.

## NS1/Budget.lean

One structural induction proves preservation of height and node count. A general invariant lemma transports each through a list of decrements.

Proofs: `length_decw`, `size_enc`, `measures_dec`, `ht_dec`, `nds_dec`, `decAll_append`, `invariant_decAll`, `ht_decAll`, `nds_decAll`.

## NS1/Comp.lean

Extracted the singleton-output fact and merged conditional evaluation. Kept run distinct from application because the program itself is computed.

Proofs: `wsum_nil`, `wsum_cons`, `wsum_append`, `wsum_congr`, `wsum_bindW`, `mem_bindW`, `mem_bindW_of`, `Gives.output_of_mem`, `mono`, `congr`, `hl`, `evl`, `plain`, `of_dt`, `cons`, `app`, `lett`, `letk`, `run`, `ite_of_gives`, `ite_true`, `ite_false`, `either`, `fail`, `theta`, `hd`, `tl`, `mono`, `id`, `quote`, `hd`, `tl`, `cons`, `app`, `lett`, `letk`, `run`, `ite_true`, `ite_false`, `after`, `Does.of_gives`.

## NS1/Compose.lean

Composition tracks a list of outputs and multiplies the weights of their possible decompositions. Kept the fold invariant separate from the composed program bound.

Proofs: `CutD.cutProg`, `wsum_foldW_pvs`, `mem_foldW`, `_root_.Paper.thm_cut_compose`, `size_compC`.

## NS1/DSteps.lean

The executor handles different store updates for each instruction. The sequence proof translates weighted lists into execAll and accumulates program cost.

Proofs: `gets_nil`, `gets_tset`, `gets_assign`, `len_ofBits`, `dstepF_does`, `sum_execAll_cons`, `execAll_append`, `dstepsF_does`, `tmRec_gives`, `tmB_gives`, `tmF_gives`, `tmsF_gives`.

## NS1/Deal.lean

Store representation lemmas already factor the update steps. The bit-selection witness includes a multiplicity condition absent from deterministic assignment.

Proofs: `RepW.set`, `RepW.assign`, `assignF_gives`, `bitsB_does`, `bitsF_does`.

## NS1/Diag.lean

The single evaluator lemma proves the two branches of the diagonal program by the corresponding run semantics.

Proofs: `diagF_ev`.

## NS1/Eval.lean

The relation on lists is factored over appends, maps and flatMaps. The selection evaluator uses a distinct induction on the dispatch list.

Proofs: `forall₂_flatMap`, `forall₂_exists`, `lett_rel`, `selF_ev`, `Dt.fX`, `Dt.fS`, `Dt.fO`, `Dt.fA`, `rec_ev`, `mem_simS`, `simS_map`, `simS_append`, `simS_flatMap`.

## NS1/EvalThm.lean

Kept the interpreter proof by evaluation constructor. Its recursive call lemmas separate one and two carried state arguments.

Proofs: `Run.seq_assoc`, `Fm.ofTree_cases`, `IF_case`, `call0`, `call1_rel`, `call2_rel`, `flatMap_single`, `interp`.

## NS1/Finite.lean

The Jacobson-ring argument and the finite residue-field argument establish different algebraic facts used in specialization.

Proofs: `isJacobsonRing_int`, `finite_of_finiteType_int`.

## NS1/Guess.lean

Factored the expanded-trie cost into a bound valid over arbitrary coefficient rings. Retained separate proofs for lookup values and permitted names.

Proofs: `Leaf.inB`, `pw_succ`, `combVal_pw`, `Leaf.lk`, `lookup_comb`, `lookup_expand`, `InB.mono`, `nds_comb`, `nds_pos`, `nds_expand`, `expand_cost_le`, `ht_comb`, `ht_expand`, `length_words`, `ht_budg`, `nds_budg`, `gbit_ev`, `gw_ev`, `node_rel`, `gcomb_ev`, `gt_ev`, `size_num`, `size_gw`, `size_gcomb`, `size_gt`.

## NS1/Interp.lean

Success and failure of a decrement have different result lists. The wrappers on empty runs fix the outcomes needed by the interpreter.

Proofs: `Dt.ite_true`, `Dt.ite_false`, `Dt.run`, `Ev.ite_true_nil`, `Ev.ite_false_nil`, `Ev.run_nil`, `Ev.cons_nil_left`, `Ev.cons_nil_right`, `DW_some`, `DW_none`, `DC_some`, `DC_none`, `AW_ev`, `AZ_ev`.

## NS1/Lists.lean

Moved the bit-list concatenation specialization next to appF_gives and removed the duplicate group implementation.

Proofs: `toList_listT`, `listT_toList`, `listT_ofBits`, `Does.runW`, `foldB_does`, `foldF_does`, `foldW_det`, `foldF_gives`, `foldl_rev`, `rev_gives`, `appF_gives`, `appBits_gives`, `mapB_gives`, `mapF_gives`, `eqB_gives`, `eqF_gives`, `pickB_does`, `pickF_does`, `tget_nil`, `tget_tset`, `getB_gives`, `getF_gives`, `setB_gives`, `setF_gives`, `WE.does`, `WE.exists_of_adjoin`.

## NS1/Machine.lean

The foundational constructor proofs directly establish evaluation determinism and the relationship with the chosen evaluation list.

Proofs: `hd_cons`, `tl_cons`, `hd_nil`, `tl_nil`, `len_num`, `size_pos`, `size_hd_le`, `size_tl_le`, `path_ofBits`, `bit_ne_nil`, `size_ofBits`, `ofTree_code`, `Ev.unique`, `Hl.ev`, `Ev.hl`, `Ev.evl`, `Ev.run'`, `Dt.quote`, `Dt.id`, `Dt.hd`, `Dt.tl`, `Dt.cons`, `Ev.ite_true`, `Ev.ite_false`, `Ev.run_det`, `Ev.lett`.

## NS1/Main.lean

Kept trie homomorphism lemmas and the ring-lifting theorem separate from logarithm bounds used across scale proofs.

Proofs: `nds_map`, `ht_map`, `combVal_map`, `lk_map`, `inB_map`, `consts_finite`, `exists_lift`, `val_map`, `IsAccT.map`, `IsAccT.of_map`, `lt_two_pow_lg`, `lg_mono`, `lg_pow_le`, `le_lg_pow`, `le_lg_of_two_pow_le`, `two_pow_lg_le`, `poly_lg`, `lg_ge_two`.

## NS1/OneCut.lean

Separated the terminal choice of branching factor from the induction that repeatedly cuts by v^63. Moved the duplicate Plain monotonicity result to its definition.

Proofs: `CutD.mono`, `OneCutAt.finalCut`, `_root_.Paper.thm_cut_iterate`, `OneCutAt.mono`, `le_lg_of_lg_pow_le`, `polylog_loss_le`.

## NS1/Parts.lean

The accumulator invariant connects one partition step to list folding. The outer evaluation also accounts for the size of its input formula.

Proofs: `partStep_gives`, `foldl_partFun`, `partsF_gives`.

## NS1/Picks.lean

Retained separate positive and negative checks. The sum over choices distinguishes words differing on an unassigned coordinate.

Proofs: `funs_eq_of_not_mem`, `sum_funs`, `execAll_choices`, `execAll_det`, `execAll_checks_pos`, `execAll_checks_neg`.

## NS1/Postpone.lean

Budget partitioning proves the plain weight identity. Filtering by successful budgets and evaluation of WF are independent obligations.

Proofs: `ok_nil`, `ok_cons`, `all_not_iff`, `decw_val`, `ok_leaf`, `part_cons`, `length_part_le`, `ok_node`, `ok_none`, `sum_words`, `sum_flatMap_map`, `prod_lookup_node`, `sum_budg`, `simS_cons`, `map_simS`, `sum_filter_th`, `WF_ev`, `val_eq_sum_budg`.

## NS1/Scale.lean

Shared the encoded budget size bound across exact and approximate rounds. Used Plain.mono from the common representation.

Proofs: `CutHyp.at`, `cst_def`, `size_LP`, `size_stepF`, `pow_le_pow`, `KT.expand_budget_bounds`, `size_zq_of_budget`, `round`.

## NS1/Step.lean

Kept the exact weighted-sum proof for the composed step evaluator; approximate rebilling adds a second set of constants.

Proofs: `wt_seq`, `wt_tick`, `wt_delay`, `wt_det`, `val_eq_sumF`, `sumF_delay`, `sum_rel`, `Ev.app`, `sumF_app`, `mem_app`, `LP_ev`, `ZE_ev`, `stepF_ev`.

## NS1/Util.lean

Word encoding, nonzero detection and taking a prefix use different machine programs and cost recurrences.

Proofs: `length_wordT`, `wordB_gives`, `wordF_gives`, `nzB_gives`, `takeB_gives`.

## Nc/Acc/ApproxMain.lean

The Laurent-polynomial error estimate uses the common polynomial line restriction over a commutative semiring.

Proofs: `PolyOrdGE.mul`, `polyOrdGE_C`, `ordGE_one`, `ordGE_line_coeff`, `ordGE_codeB`, `ordGE_sum_coeff_sub`.

## Nc/Acc/CompK.lean

Merged conditional cost/value proofs. A single induction groups a weighted list by output; KV.app uses it for both runs and weighted pairs.

Proofs: `wt_mul`, `mono`, `congr`, `hl`, `evl`, `of_does`, `of_gives`, `fail`, `mul`, `cons`, `ite_of_gives`, `ite_true`, `ite_false`, `either`, `sum_by_output`, `app`, `lett`, `app_gives`, `run`.

## Nc/Acc/Line.lean

Removed the duplicated line restriction and evaluation at one. The zero coefficient and interior terms of a product remain local to the accelerator argument.

Proofs: `line_coeff_zero`, `coeff_mul_succ`.

## Nc/Acc/Loop.lean

Removed the local bit-concatenation proof. Loop evaluation still distinguishes gate and stack transitions.

Proofs: `gwd_does`, `walkF_does`, `nameL_gives`, `nameK_gives`, `loopF_kv`.

## Nc/Acc/LowDeg.lean

The positive-degree recurrence and the truncated coefficient sum already use the shared line restriction. Preserved their commutative-ring hypotheses.

Proofs: `ser_zero`, `exists_series`, `W_nil`, `W_cons`, `sum_coeff_line`, `sum_coeff_eq_eval`.

## Nc/Acc/Main.lean

Constructor size bounds concern the syntax tree of the actual program. Retained the explicit arithmetic used to bound its full size.

Proofs: `size_quote`, `size_id`, `size_hd`, `size_tl`, `size_cons`, `size_ite`, `size_run`, `size_guess`, `size_mul`, `size_app`, `size_lett`, `size_gwd`, `size_walkF`, `size_pairsF`, `size_accF`.

## Nc/Acc/Prog.lean

The circuit-to-program construction uses the shared line restriction. Lookup lemmas recover the appropriate constant for each gate or letter.

Proofs: `pairB_gives`, `length_pairL_le`, `pairsF_gives`, `treeF_gives`, `length_tbits`, `wordT_eq`, `look_pairTree`, `decL_lc`, `length_lc`, `ltr_cases`, `lamK_ge`, `accK_k`, `accK_l`, `accK_c`, `nds_accK`, `ht_accK`, `accF_kv`.

## Nc/Acc/Trie.lean

Lookup value and admissible path membership have different specifications. Word enumeration and reversal justify the sum across all slots.

Proofs: `lk_full`, `inB_full`, `nds_full`, `ht_full`, `length_of_mem_wd`, `val_lt_of_length`, `exists_word`, `sum_wd`, `sum_wd_reverse`, `look_append`, `length_pairL`, `getD_pairL`, `look_pairs`.

## Paper/Next.lean

Reused the expanded-trie cost bound. The exact iteration keeps one trie, so its invariant and final name bound remain smaller than the approximate ones.

Proofs: `prop_next_round`, `prop_next`.

## Paper/ApproxRound.lean

Used the same trie-cost and encoded-instance bounds as the exact round. Proved the extraction program evaluation once for halting and coefficient correctness.

Proofs: `prop_approx_acc_round`, `prop_approx_acc_round_num`, `prop_approx_acc_next`, `prop_approx_acc_exact`.

## Paper/ApproxScales.lean

Kept the bootstrap and scale step distinct. The first fixes span and thinning constants, while the step must preserve them. The final circuit proof depends on substitution by Laurent polynomials.

Proofs: `def_approx_acc`, `cube_le`, `prop_approx_acc_step`, `prop_approx_acc_all_scales`, `prop_approx_acc_hasAcc`, `prop_approx_acc_first`, `prop_approx_acc`, `prop_approx_acc_setting`, `lem_circuit_approx`, `contracting_approx_complete`.

## Paper/Scales.lean

The conversion from bounds for integer exponents to a real quasipolynomial threshold is independent of the chosen complete family.

Proofs: `def_acc`, `quasi_of_exponents`, `exists_scale`, `scales_setting`, `contracting_complete`, `thm_contracting`.

## Paper/NoAcc.lean

The self-application witness uses finite residue fields, a uniform period and the exact cut evaluator. Retained their separate proofs and shared Plain.mono.

Proofs: `thm_noacc_finite_field`, `thm_noacc_periodic`, `thm_noacc_diagonal`, `thm_noacc_all_scales`, `thm_noacc`.

## Paper/Postpone.lean

The published statement wraps the budget-sum identity and evaluates the associated plain instances. The detailed evaluator belongs in NS1.

Proofs: `lem_postpone`.

## Paper/Circuit.lean

Retained the universal projection, syntactic program construction and gate/name bounds. Approximate circuits share the program but use Laurent-polynomial evaluation for correctness.

Proofs: `wordG_self`, `wordG_bits`, `universal_symbols_ne`, `lem_circuit_universal`, `lem_circuit_program`, `lem_circuit_names`, `lem_circuit_bound`, `lem_circuit`, `lem_circuit_perm`.

## Paper/CircuitPhi.lean

The assignment polynomial is evaluated under the clause/input encoding. Explicit bounds on literals and clauses are separate inputs to its total-degree estimate.

Proofs: `lem_circuit_assignment`, `lem_circuit_value`, `clauseSum_inputs`, `card_clauses`, `literal_bound`, `lem_circuit_phi`.

## Paper/Universal.lean

The proof maps words through the generator map before invoking the universal presentation. The finite-dimensional realization is supplied by the separate step lemmas.

Proofs: `map_word`, `prop_universal`.

## Paper/UniversalSteps.lean

Automaton extraction, machine realization and passage to power series have different intermediate types and paper correspondences.

Proofs: `prop_universal_automaton`, `prop_universal_machine`, `prop_universal_series`.

## Related modules

Generalized Nc/LowDegree.lean to commutative semirings. The group callers in Nc/Grp/{Base,GroupProg,Role,RoleProg,Seg}.lean use NS1.appBits_gives. The accelerator and cutting blueprint chapters describe the shared estimates and terminal cut.

Full-source checkpoint 35/47. Additional full reads: NS1/{ApproxBack,ApproxRound,ApproxExtract,Machine,EvalThm,Guess,Compose,Comp} and Nc/Acc/CompK. The approximate evaluator and rebilling branches share the weighted application law; the decoder branches repeat inversion of the same eleven-way disjunction. Guess and Compose retain their distinct run-order and cost laws. Twelve modules still need a complete body read: NS1/{DSteps,Lists,OneCut,Postpone}, Nc/Acc/{Loop,Prog}, Paper/{Next,ApproxRound,ApproxScales,NoAcc,Circuit,CircuitPhi}.
36/47. Read all Nc/Acc/Loop bodies. In walkF_does both path_ofBits equations were proved twice. Moved each to the parent successor branch. Retained separate input/product branches in loopF_kv: recursive stacks, bounds, guessed words, and the applied summation lemmas differ.
37/47: Paper/CircuitPhi. Assignment existence/uniqueness, value bijection, clause input product, arithmetic literal bound and the six conclusions of lem_circuit_phi read in full. Simplified the definitional product bridge in the value proof and retained the degree and antichain evaluation arguments. Focused Nc/RunMn and Paper/CircuitPhi passed together.
40/47. Read both Paper/Next proofs, all Nc/Acc/Prog and Paper/Circuit proof bodies. Consolidated node budget growth for both length and time, the identical three-field bit-name splits for product and input trie branches, and the factor-of-two lg bound used twice for circuit sizes. Retained the circuit log factor proof and the construction of a parse-tree sum; their hypotheses and outputs are distinct.
42/47. Full proof reads of OneCut and Postpone. In OneCut the terminal and recursive time-loss estimates use the same quotient cancellation against v^208. In Postpone the fixed-value indicator sum follows at once from the general enumeration theorem; removed the prior 46-line parity induction, including its two parallel modular branches.
47/47 full proof-body reads: final five NS1/{DSteps,Lists} and Paper/{NoAcc,ApproxRound,ApproxScales}. Read declaration/proof bodies, including long application/interpretation, exact/approximate numerical inductions, rescaling, and the diagonal. DSteps now extends the execution, cost and template expansion functions along their injective encodings. Lists can reuse Does.of_gives directly for fold and pick. NoAcc chooses power representatives on the finite range and invokes the same budget growth estimate as both rounds. Exact and approximate plain submissions have identical time and size estimates. The approximate extraction additionally requires Laurent support bounds and modular non-aliasing; kept this logic distinct from the exact path.

## Second cohort: 19/19 complete proof-body reads (66 baseline paths in total)

- Nc/End/Run: use ring-homomorphism mapping of a matrix and of a list product.
- Nc/End/Thm: Mathlib eval_assoc supplies the polynomial evaluation composition.
- Nc/End/PermThm: retain the letter substitution and coefficient transport.
- Nc/End/ApproxThm: read before removal; the universe-polymorphic affine substitution in Nc/Rate/Circuit proves the same result.
- Nc/Final/CClasses: share strict-monotone gate reindexing and gate mapping for renames and coefficient transport.
- Nc/Hc/Grid: retain incidence tests and interpreter-specific constructor checks.
- Nc/Hc/Segments: use Bool complement uniqueness for the two alternatives.
- Nc/Hc/Vnp: retain ordered cycle recovery and its cost; share the quartic witness packaging with Ryser.
- Nc/Rate/Defs: expose the common nonpositive-coefficient characterization.
- Nc/Rate/Circuit: retain coefficientwise affine substitution; both paper callers use it.
- Nc/Rate/Transfer: retain the nonzero tensor witness and Nullstellensatz projection.
- Nc/Rate/Truncate: reuse gate reindexing for preserved old gates.
- Paper/HcGrid: retain uniqueness of the nonzero weighted route and grid completion.
- Paper/LowDeg: retain the separate zero-degree obstruction for a nonempty parse witness.
- Paper/LowDegChains: retain constant, linear and remaining terms in the parse-tree multiplication step.
- Paper/Fields: use the shared quartic VNP witness and retain the final field-dependent growth and no-polynomial bound.
- Paper/Transfer: use the shared nonpositive-coefficient characterization.
- Paper/Approximate: use the same characterization; retain flat and contracting transfer hypotheses separately.
- Nc/LowDegree: read all bodies, including gate evaluation and affine constants/variables under the generalized semiring assumption.

Related witness edits in Paper/Ryser and the affine-substitution caller in Paper/ApproxScales were checked with the other reviewer. Additional cross-branch caller edits described above are outside the 66.

Final verification: the changed second-cohort Lean modules Nc/{End/{Run,Thm},Final/CClasses,Hc/{Segments,Vnp},Rate/{Defs,Truncate}} and Paper/{Ryser,Transfer,Fields,ApproxScales,Approximate} compiled with the pinned toolchain, using refreshed overlay dependencies. Commit 7d2a63b removes the duplicate affine module and updates the completeness blueprint. The independently reviewed network split 9db8646 and assembly refactor 4a71290 passed compilation from exact Git source at 4a71290 in a separate disposable overlay, then a fresh downstream importer verified Paper.ThinTrees, Paper.tree_node_le, Paper.tree_total_le, and the axioms of Paper.thm_tree (propext, Classical.choice, Quot.sound). A simultaneous mixed-artifact check of later shared Tree work hit a stale Nc.Tow import; integrated verification belongs to the root worker.
