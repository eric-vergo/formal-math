# Changes for Lean 4.36.0 and Mathlib v4.36.0

This branch builds the development with `leanprover/lean4:v4.36.0` and Mathlib at the tag `v4.36.0`
(`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`); upstream `vp-vnp` uses Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. This file lists every change to a Lean file that the move
needed.

## Statements whose spelling changed

Mathlib now defines `MvPolynomial σ R` (and `Polynomial R`) through the structure `AddMonoidAlgebra`,
whose field `coeff` holds the coefficients, and it has no `MvPolynomial.coeff` any more. Where the
upstream text writes `coeff d p` (`MvPolynomial.coeff`, the coefficient of the monomial `d` in `p`), this
branch writes `p.coeff d`. Four statements of the compared files contain such a coefficient:

| File | Declaration | Upstream | This branch |
|---|---|---|---|
| Statement.lean | `Statement.Approximates` (the definition) | `(coeff d q).coeff i = if i = 0 then coeff d f else 0` | `(q.coeff d).coeff i = if i = 0 then f.coeff d else 0` |
| Paper/Approximate.lean | `Paper.def_approx` (Definition N.1) | `(coeff d p).coeff i = 0`, `(coeff d p).coeff 0 = coeff d f` | `(p.coeff d).coeff i = 0`, `(p.coeff d).coeff 0 = f.coeff d` |
| Paper/Approximate.lean | `Paper.approx_rate_closed` | `(coeff d P).coeff i = 0`, `(coeff d P).coeff 0 = coeff d (G m)` | `(P.coeff d).coeff i = 0`, `(P.coeff d).coeff 0 = (G m).coeff d` |
| Paper/Transfer.lean | `Paper.lem_transfer_approx` (Lemma N.2) | `(coeff d P).coeff i = 0`, `(coeff d P).coeff 0 = coeff d (MvPolynomial.map (Int.castRingHom KK) q)` | `(P.coeff d).coeff i = 0`, `(P.coeff d).coeff 0 = (MvPolynomial.map (Int.castRingHom KK) q).coeff d` |

The rest of each statement is unchanged. The outer `.coeff i` is the coefficient of a Laurent series,
which is spelled as before. `MainTheoremApprox` and `SeparationClosure`, and through them
`Solution.mainTheoremApprox` and `Solution.separationClosure`, use `Approximates`; their own text is
unchanged.

Why the meaning is unchanged: both spellings name the function that is additive in the polynomial and
takes the value `a` at `d` on the monomial `monomial d a` and `0` at every other exponent. Upstream's
Mathlib proves these two laws for `MvPolynomial.coeff` (`MvPolynomial.coeff_add`,
`MvPolynomial.coeff_monomial`). [scripts/StatementSpelling.lean](scripts/StatementSpelling.lean) proves
them for `p.coeff d` at this branch's revision, proves that every function with them equals
`fun d p ↦ p.coeff d` (by induction over polynomials), and restates `Statement.Approximates` for any such
pair of functions. Check it with `lake env lean scripts/StatementSpelling.lean`, which prints nothing when
every proof checks.

Section 3 of the paper prints upstream's Statement.lean (Appendix Q says so). This branch's file differs
from upstream's in the line of `Approximates` shown above and nowhere else
(`git diff upstream/vp-vnp -- Statement.lean`).

[scripts/statement-diff.py](scripts/statement-diff.py) checks this mechanically. It compares every
declaration of Statement.lean, the Comparator challenge and solution, Paper.lean and Paper/ with upstream
`vp-vnp` (theorems up to `:=`, definitions and structures in full, with comments removed, and the other
top-level commands of each file in order), and it marks a change as one of the coefficient's spelling only
when rewriting upstream's `coeff A B` to `B.coeff A` gives this branch's text exactly:

    python3 -I scripts/statement-diff.py upstream/vp-vnp HEAD

## Proof repairs

No statement other than those above changed. No `sorry` was added, no axiom, no `native_decide`, and no
`maxHeartbeats` was raised (the `set_option maxHeartbeats` lines in the development are upstream's).

| File | Declaration | Change | Reason |
|---|---|---|---|
| Nc/PermCoeff.lean | `coeff_ones_prod`, `permanent_eq_coeff`, `coeff_ones_of_mem`, `coeff_ones_congr` | `coeff m p` → `p.coeff m` (statements and proofs) | `MvPolynomial.coeff` is gone (see above) |
| Nc/PermGrid.lean | `gridMatrix_permanent_aux` | `coeff m p` → `p.coeff m` in the statement | the same |
| Nc/Acc/ApproxMain.lean | `ordGE_line_coeff`, `ordGE_sum_coeff_sub` | `MvPolynomial.coeff m p` → `p.coeff m` | the same |
| Nc/Rate/Defs.lean | `Approximates` (the proof's own form) | `coeff m p` → `p.coeff m` | the same |
| Nc/Rate/Truncate.lean | `OrdGe`, `Approximates.exists_laurentPolynomial`, `Approximates.of_laurentPolynomial` | `coeff m p` → `p.coeff m` | the same |
| Nc/Rate/Circuit.lean | `Approximates.aeval` | `coeff m p` → `p.coeff m` | the same |
| Nc/End/Thm.lean | `totalDegree_aeval_le` | `coeff m p` → `p.coeff m` | the same |
| Paper/Approximate.lean | `flat_rate_approximating`, `thm_approx` | `coeff m p` → `p.coeff m` inside the proofs | the same |
| Paper/Transfer.lean | `lem_transfer` | `coeff m p` → `p.coeff m` inside the proof | the same |
| Nc/CaseI/Multi.lean | `cf_add` | the term `coeff_add _ _ _` → `by rw [cf, cf, cf, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]` | `MvPolynomial.coeff_add` is deprecated and protected; additivity of the coefficient is `AddMonoidAlgebra.coeff_add` |
| Nc/Rate/Truncate.lean | `OrdGe.add`, `Approximates.of_laurentPolynomial` | `coeff_add` → `AddMonoidAlgebra.coeff_add, Finsupp.add_apply` in a `rw` | the same |
| Nc/End/ApproxThm.lean | `Approximates.substitute_affine` | `coeff_add` → `AddMonoidAlgebra.coeff_add, Finsupp.add_apply` in a `rw` | the same |
| Nc/Rate/Circuit.lean | `Approximates.aeval` | `coeff_zero` → `AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply` in a `rw` | the coefficient of `0` is `AddMonoidAlgebra.coeff_zero`, an equation of functions |
| Nc/Price/BorderFew.lean | `le_type_bound`, `pow_le_few` | `Polynomial.coeff P n` → `AddMonoidAlgebra.coeff P n` (four places) | `Polynomial.coeff` is gone as well; the coefficient function has the same argument order |
| Paper/LowDegChains.lean | `lem_lowdeg_chains` | `rw [map_add]` → `rw [map_add (line u)]` | the coefficient is a `Finsupp` applied to an index, and an unannotated `map_add` first matches that application |
| Paper/Approximate.lean | `coeff_toLaurent_natCast` | `Finsupp.mapDomain_apply` → `Finsupp.mapDomain_apply_of_injective` | Mathlib renamed the lemma for an injective map and gave `mapDomain_apply` a general statement |
| Nc/Cross/Split.lean | `det_expand` | `MultilinearMap R …` → `MultilinearMap (RingHom.id R) …`; `rw [smul_eq_mul]` → `simp only [smul_eq_mul, RingHom.id_apply]` | multilinear maps are semilinear: the first argument is a ring hom, and `map_piecewise_smul` applies it to the scalars |
| Nc/Price/BorderFew.lean, Ov/Core/Wire.lean, Paper/Crossing.lean, Paper/Extension.lean, Paper/States.lean | `pow_le_few`, `push_le_move`, `prop_crossing_cut`, `prop_extend_product`, `prop_extend_lower`, `lem_count_sets` | `Finset.prod_le_prod` → `Finset.prod_le_prod₀` (six places) | the lemma with non-negativity hypotheses is now `prod_le_prod₀`; `prod_le_prod` is the one for ordered monoids |
| Nc/Tower/Chain.lean | `exists_chain` | `Sylow.exists_subgroup_card_pow_prime_le` → `Sylow.exists_subgroup_card_pow_prime_ge` | Mathlib renamed the lemma (a subgroup of order p^n lies in one of order p^m) and gave the old name to another lemma |
| Nc/Tower/Words.lean, Paper/Groups.lean | `WL.el_one`, `kappa_small` | `Nat.pow_pred_clog_lt_self` called without the hypothesis `1 < b` | the lemma takes the base explicitly and no longer needs it |
| Nc/Flag/Uni.lean | `wi_t_mul` | `Function.swap` added to a `simp` set | the transpose of a matrix now unfolds to `Function.swap` |
| Nc/Grp/StepRole.lean | `kNew_eq` | the three steps after `congr 1` removed | `congr 1` now closes the goal (the two filter conditions agree by definition) |
| Paper/CircuitPhi.lean | `lem_circuit_value` | `exact h1` → `convert h1 <;> rfl` | after `Fintype.prod_sum_type` the goal has `rLits` and `rWt` at `Sum.inl`, which `exact` no longer unfolds; the two goals left hold by `rfl` |
| Paper/CircuitPhi.lean | `clauseSum_inputs` | `split_ifs <;> rfl` removed | the `rw` before it now closes the goal |
| Paper/CircuitPhi.lean | `lem_circuit_phi` | `simp [code, …]` → `simp [Nc.code, …]` | Lean 4.36 has a global `code` (a documentation role), which the bare name now resolves to |
| Nc/FinDom.lean | `fdSum_eq`, `fdSum_elim` | `omit [Fintype ι] [DecidableEq ι] [DecidableEq θ] in` → `omit [DecidableEq θ] in` | the proofs now use the section's `[Fintype ι] [DecidableEq ι]`, which Lean then refuses to omit; the two theorems take these instances as arguments, and every use has them |
| Nc/Cat/Length.lean | `len_q` | the four `repeat' first \| exact hb _ _ \| apply Bd.smul \| apply Bd.add \| apply Bd.mul` run under `with_reducible` | the failing alternatives unfolded `df` and the operations on real numbers during unification and the proof ran out of heartbeats; at reducible transparency only the structural matches are tried |
| Nc/Tow/Slp4.lean | `mem_cur` | the one-line `simp [seen0, newUnits, SeenU]` for the initial units replaced by its two directions, closed by `simpa [seen0]` and `simp [newUnits]` (as in `mem_seen_init` of Nc/Tow/EndA.lean) | the combined `simp` ran out of heartbeats in instance search |

The table has 28 rows; the Lean files changed besides Statement.lean are the 27 named in it.

## Warnings

`lake build` prints, besides the five `declaration uses 'sorry'` warnings of the challenge (the theorems
it states without proof), warnings that the new toolchain and Mathlib introduce: deprecations (mostly
`if_pos`, `if_neg`, `dif_pos`, `dif_neg`, `if_true` and `if_false`, whose replacements Lean names in each
message), the notice that Mathlib is designed for the module system, and linter remarks (unused `simp`
arguments, unused variables, unused tactics). None of them is an error and none concerns a statement;
they are left as they are so that the proofs stay as close to upstream as the port allows.
