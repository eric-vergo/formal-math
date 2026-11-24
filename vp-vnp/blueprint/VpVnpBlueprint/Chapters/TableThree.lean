/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import Comparator.VpVnp.Solution
import Paper

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "The paper's statements and their Lean names" =>

%%%
tag := "chapter-table3"
file := "lean-names"
htmlSplit := .never
number := false
%%%

Table 3 of the paper (Appendix Q, page 67, in {repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) names the
Lean theorem of every numbered statement. This chapter is that table with three columns added:
whether the Lean statement says what the printed statement says, whether the Lean theorem lies on
the route by which the five theorems of `Solution.lean` are proved, and the chapter of this
blueprint that presents the statement. It is the index of the site: a reader who holds the paper
finds the Lean declaration here, and a reader who holds a Lean name finds the printed statement.

# How to read the table

The Lean names are those of Table 3, with the prefix `Paper.` written out, and for the statements
of Section 1 also the theorems of `Solution.lean`. Every name in this chapter resolves in the
build that the site is generated from; hovering over it shows its Lean statement.

The column _Lean statement_ has one of three entries.

- _matches_: the Lean statement says what the printed statement says, up to the encoding (types
  for sets, coercions, a finite sum with possibly zero summands for “at most”).
- _differs as the paper says_: Section Q.3 of the paper (pages 66–70), a formalization note, or
  the text beside the statement names a difference; the note in the last column says which, and
  quotation marks enclose the paper's words. Most of these differences make the Lean statement
  more general or more explicit, or move hypotheses and clauses into structures. The chapter that
  presents the statement gives the difference in full.
- _no Lean counterpart_: Remark N.6 only.

These entries are a reading of the printed statements against the Lean statements, made for this
blueprint by AI models: once for every row, from the paper and the Lean sources, and a second
time for a sample of 32 rows. No tool checks such a comparison, and no human has made it. For
Theorem H.2, Proposition J.2, Definition G.1, Lemma I.2 and Proposition E.1, whose content lies
in the fields of structures or in long statements, it was made against the paper's own list of
differences and not clause by clause. No difference was found that the paper does not name. A difference in a row
below cannot affect what the five theorems of `Solution.lean` state, which is fixed by
`Statement.lean` alone ({ref "chapter-statement"}[The statement to trust]); it affects how far
the printed text can serve as a guide to the Lean proof.

The column _route_ follows Section Q.3 (page 66): “The theorems with prefix `Paper.` state the
numbered statements, and each of them is proved once. The theorems of `Solution` are proved
through them, with these exceptions, which are not on that route: Theorem L.2, Corollary L.3, the
qualitative bound in the flat case (Proposition E.5 and Theorem E.6) and the definitions.”

The statements of Sections 1 and 2 restate statements of the appendix: Theorem 1.1 is Theorem
M.3, Corollary 1.2 is Corollary M.4, Definition 1.3 is Definition N.1, Theorem 1.4 is Theorem
N.5, and Definition 2.1 and Theorem 2.2 are Definition D.1 and Theorem D.2 with the hypotheses
stated for spectral points. So the 70 rows for numbered statements are 64 different statements;
two further rows are the displays (B.2) and (F.1), which Table 3 also names. Of the 70 rows, 31
match, 38 differ as the paper says, and one has no Lean counterpart.

# Sections 1 and 2

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Theorem 1.1
  * 2
  * {InlineLean.name}`Paper.thm_allfields`, {InlineLean.name}`Solution.mainTheorem`
  * matches
  * yes
  * {ref "chapter-claim"}[What is claimed]. The same statement as Theorem M.3. The Lean proof takes $`c = 1/1600^2`.
*
  * Corollary 1.2
  * 2
  * {InlineLean.name}`Paper.cor_allclasses`, {InlineLean.name}`Solution.separation`
  * matches
  * yes
  * {ref "chapter-claim"}[What is claimed]. The same statement as Corollary M.4.
*
  * Definition 1.3
  * 2
  * {InlineLean.name}`Paper.def_approx`, {InlineLean.name}`Paper.VPBar`, {InlineLean.name}`Statement.Approximates`, {InlineLean.name}`Statement.VPBar`
  * differs as the paper says
  * definition
  * {ref "chapter-claim"}[What is claimed]. The same statement as Definition N.1; see there.
*
  * Theorem 1.4
  * 2
  * {InlineLean.name}`Paper.thm_approx`, {InlineLean.name}`Solution.mainTheoremApprox`, {InlineLean.name}`Solution.separationClosure`
  * matches
  * yes
  * {ref "chapter-claim"}[What is claimed]. The same statement as Theorem N.5.
*
  * Definition 2.1
  * 4–5
  * {InlineLean.name}`Paper.def_cases`, {InlineLean.name}`Paper.Flat`, {InlineLean.name}`Paper.Contracting`
  * differs as the paper says
  * definition
  * {ref "chapter-overview"}[The shape of the proof]. Page 5: “The Lean definition states both hypotheses for prices”; the form of Definition D.1.
*
  * Theorem 2.2
  * 6
  * {InlineLean.name}`Paper.thm_alt`
  * matches
  * yes
  * {ref "chapter-overview"}[The shape of the proof]. In the form for prices; the same statement as Theorem D.2.
:::

# Appendix A

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Definition A.1
  * 19
  * {InlineLean.name}`Paper.def_spectral`, {InlineLean.name}`Paper.def_spectral_congr`
  * differs as the paper says
  * definition
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]. Page 66: “Lean does not identify equivalent tensors (`def_spectral_congr` shows that spectral points respect the identifications)”.
*
  * Lemma A.2
  * 19
  * {InlineLean.name}`Paper.lem_exponents`
  * matches
  * yes
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]
*
  * Lemma A.3
  * 19
  * {InlineLean.name}`Paper.lem_hubs`, {InlineLean.name}`Paper.lem_hubs_further`
  * differs as the paper says
  * yes
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]. More general: the tensor is pushed forward along an arbitrary map of parties; `lem_hubs_further` is the form with two further parties (page 68).
*
  * Definition A.4
  * 20
  * {InlineLean.name}`Paper.def_price`
  * matches
  * definition
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]
*
  * Proposition A.5
  * 20
  * {InlineLean.name}`Paper.prop_gauge`
  * matches
  * yes
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]
*
  * Theorem A.6
  * 20
  * {InlineLean.name}`Paper.thm_duality`
  * differs as the paper says
  * yes
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]. The family of tensors is indexed by any finite set (page 68).
*
  * Proposition A.7
  * 21
  * {InlineLean.name}`Paper.prop_extend`
  * differs as the paper says
  * yes
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]. The family of maps is indexed by any finite set (page 68).
*
  * Proposition A.8
  * 21
  * {InlineLean.name}`Paper.prop_random`
  * matches
  * yes
  * {ref "chapter-spectral"}[Tensors, spectral points and prices]. The random map is a family of measurable maps with finite ranges on a probability space.
:::

# Appendix B

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Lemma B.1
  * 22
  * {InlineLean.name}`Paper.lem_count`
  * matches
  * yes
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]
*
  * Proposition B.2
  * 22–23
  * {InlineLean.name}`Paper.prop_identity`
  * differs as the paper says
  * yes
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]. Proved without the assumption that $`\Sigma_1` and $`\Sigma_2` are nonempty (page 68).
*
  * Proposition B.3
  * 24
  * {InlineLean.name}`Paper.prop_crossing`
  * matches
  * yes
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]
*
  * Display (B.2)
  * 24
  * {InlineLean.name}`Paper.eq_Q`
  * matches
  * yes
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]. The display alone (page 66).
:::

# Appendix C

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Theorem C.1
  * 25
  * {InlineLean.name}`Paper.thm_cn`
  * matches
  * yes
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]
*
  * Lemma C.2
  * 26
  * {InlineLean.name}`Paper.lem_means`
  * differs as the paper says
  * yes
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]. One fixed free ultrafilter, prices counted from $`n = 0`; the Lean form also asserts that the limit defining $`N` exists and equals the infimum (page 69).
*
  * Proposition C.3
  * 28
  * {InlineLean.name}`Paper.prop_space`
  * matches
  * yes
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]
*
  * Lemma C.4
  * 29
  * {InlineLean.name}`Paper.lem_toolkit`, {InlineLean.name}`Paper.lem_toolkit_a`, {InlineLean.name}`Paper.lem_toolkit_b`, {InlineLean.name}`Paper.lem_toolkit_c`, {InlineLean.name}`Paper.lem_toolkit_d`, {InlineLean.name}`Paper.lem_toolkit_e`, {InlineLean.name}`Paper.lem_toolkit_f`, {InlineLean.name}`Paper.lem_toolkit_c_minimizer`
  * matches
  * yes
  * {ref "chapter-curvature"}[Two crossing wires and nonpositive curvature]. The parts are also separate theorems. Proofs in Appendix O.
:::

# Appendix D

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Definition D.1
  * 30
  * {InlineLean.name}`Paper.def_cases`
  * matches
  * definition
  * {ref "chapter-dichotomy"}[The two cases]
*
  * Theorem D.2
  * 30
  * {InlineLean.name}`Paper.thm_alt`
  * matches
  * yes
  * {ref "chapter-dichotomy"}[The two cases]. The remarks after its proof are not formalized (page 70).
:::

# Appendix E

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Proposition E.1
  * 31–32
  * {InlineLean.name}`Paper.prop_grid`
  * matches
  * yes
  * {ref "chapter-completeness"}[Completeness gadgets]
*
  * Corollary E.2
  * 32
  * {InlineLean.name}`Paper.cor_clauses`
  * matches
  * yes
  * {ref "chapter-completeness"}[Completeness gadgets]
*
  * Lemma E.3
  * 33
  * {InlineLean.name}`Paper.lem_fkl_perm`, {InlineLean.name}`Paper.lem_fkl_perm_printed`
  * differs as the paper says
  * yes
  * {ref "chapter-completeness"}[Completeness gadgets]. In Lean a variable of block $`a` of $`f_{k,\ell}` is indexed by $`k` strings; the theorem with suffix `_printed` is for the printed polynomial (page 68).
*
  * Lemma E.4
  * 33
  * {InlineLean.name}`Paper.lem_balanced`
  * differs as the paper says
  * yes
  * {ref "chapter-flat"}[The flat case]. More general: over every commutative semiring (page 68).
*
  * Proposition E.5
  * 33
  * {InlineLean.name}`Paper.prop_flat_lower`, {InlineLean.name}`Paper.prop_flat_lower_printed`
  * differs as the paper says
  * no
  * {ref "chapter-flat"}[The flat case]. As for Lemma E.3.
*
  * Theorem E.6
  * 35
  * {InlineLean.name}`Paper.thm_flat_simple`
  * differs as the paper says
  * no
  * {ref "chapter-flat"}[The flat case]. The standing hypothesis $`2 \neq 0` is written out and $`C` is a natural number (pages 66, 68).
*
  * Lemma E.7
  * 35
  * {InlineLean.name}`Paper.lem_few`
  * differs as the paper says
  * yes
  * {ref "chapter-flat"}[The flat case]. More general: whenever $`t` is covered by $`T_1, \ldots, T_J` (page 68).
*
  * Lemma E.8
  * 35
  * {InlineLean.name}`Paper.lem_convex`
  * matches
  * yes
  * {ref "chapter-flat"}[The flat case]
*
  * Proposition E.9
  * 36
  * {InlineLean.name}`Paper.prop_cube`
  * matches
  * yes
  * {ref "chapter-flat"}[The flat case]
*
  * Proposition E.10
  * 36
  * {InlineLean.name}`Paper.prop_flat_rate`, {InlineLean.name}`Paper.prop_flat_rate_printed`
  * differs as the paper says
  * yes
  * {ref "chapter-flat"}[The flat case]. As for Lemma E.3. Its Lean proof uses the step `prop_flat_lower_sum` of the proof of Proposition E.5, not the proposition (page 70).
*
  * Theorem E.11
  * 37
  * {InlineLean.name}`Paper.thm_flat_rate`
  * matches
  * yes
  * {ref "chapter-flat"}[The flat case]. The hypothesis $`2 \neq 0` is written out.
:::

# Appendix F

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Lemma F.1
  * 38
  * {InlineLean.name}`Paper.lem_growth`
  * differs as the paper says
  * yes
  * {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups]. More general: without the assumption $`s^2 < \mu`, and also for $`r = 0` (page 68).
*
  * Lemma F.2
  * 38
  * {InlineLean.name}`Paper.lem_words`
  * differs as the paper says
  * yes
  * {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups]. More general: without the conditions $`1 \le k < n` and $`\xi, \omega \neq 0` (page 68).
*
  * Lemma F.3
  * 38
  * {InlineLean.name}`Paper.lem_first`
  * differs as the paper says
  * yes
  * {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups]. Stated for explicit numbers $`\vartheta_n` (`kappa`), “which are not those of the printed proof” (page 68).
*
  * Display (F.1)
  * 39
  * {InlineLean.name}`Paper.eq_window`, {InlineLean.name}`Paper.projection_nearest`
  * differs as the paper says
  * yes
  * {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups]. $`C(n)` is formed with Lean's $`\vartheta_n`; the projection is defined as the barycenter of the orbit, and `projection_nearest` shows that it is the nearest point (page 68).
*
  * Lemma F.4
  * 39
  * {InlineLean.name}`Paper.lem_tele`
  * differs as the paper says
  * yes
  * {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups]. $`C(n)` is formed with Lean's $`\vartheta_n` (page 68).
*
  * Lemma F.5
  * 40
  * {InlineLean.name}`Paper.lem_angle`
  * differs as the paper says
  * yes
  * {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups]. $`C(n)` is formed with Lean's $`\vartheta_n` (page 68).
*
  * Theorem F.6
  * 40
  * {InlineLean.name}`Paper.thm_poincare`
  * matches
  * yes
  * {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups]
:::

# Appendix G

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Definition G.1
  * 42
  * {InlineLean.name}`Paper.def_law`
  * differs as the paper says
  * definition
  * {ref "chapter-laws"}[Rerouting laws and tree networks]. The notion is the structure `Nc.G.Law`; `def_law` “lists only three of the fields of the structure, in one direction, so that it rests on reading the structure that it is the printed notion” (page 68).
*
  * Theorem G.2
  * 43
  * {InlineLean.name}`Paper.thm_laws`
  * differs as the paper says
  * yes
  * {ref "chapter-laws"}[Rerouting laws and tree networks]. The Lean form also states the choices of Section G and asserts (a) and (b) for every multiple $`h \ge 2u` of $`u` that satisfies (G.1) (page 68).
:::

# Appendix H

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Proposition H.1
  * 44
  * {InlineLean.name}`Paper.prop_tower`, {InlineLean.name}`Paper.prop_tower_representatives`
  * differs as the paper says
  * yes
  * {ref "chapter-laws"}[Rerouting laws and tree networks]. Bijectivity on cosets is stated as equivariance and freeness, and the cosets over a coset are given by representatives; stated for every $`h \ge 3` and $`n \ge 0` (page 68).
*
  * Theorem H.2
  * 45–46
  * {InlineLean.name}`Paper.thm_tree`, {InlineLean.name}`Paper.thm_tree_good`
  * differs as the paper says
  * yes
  * {ref "chapter-laws"}[Rerouting laws and tree networks]. The clauses are fields of a structure (`ThinTrees`); “no theorem restates this as the value of a network as defined in Section H” (page 69); the laws are standing hypotheses. Parts (d), (e): the printed proof defers to Lean (page 17).
:::

# Appendix I

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Proposition I.1
  * 49
  * {InlineLean.name}`Paper.prop_universal`
  * differs as the paper says
  * yes
  * {ref "chapter-programs"}[Programs, automata and cutting]. That the two symbols differ is a separate theorem (`universal_symbols_ne`); pairs are read by list length (page 69). The printed proof defers to Lean (page 17).
*
  * Lemma I.2
  * 50–51
  * {InlineLean.name}`Paper.lem_runnet`
  * differs as the paper says
  * yes
  * {ref "chapter-programs"}[Programs, automata and cutting]. Proved in a stronger or more general form (page 68).
:::

# Appendix J

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Definition J.1
  * 52
  * {InlineLean.name}`Paper.def_cut`
  * matches
  * definition
  * {ref "chapter-programs"}[Programs, automata and cutting]
*
  * Proposition J.2
  * 52
  * {InlineLean.name}`Paper.prop_pieces`, {InlineLean.name}`Paper.prop_pieces_identity`
  * differs as the paper says
  * yes
  * {ref "chapter-programs"}[Programs, automata and cutting]. The clauses are fields of a structure (`PieceCut`); outcomes range below a bound that is part of the data, and the identity sums over those (page 69).
*
  * Theorem J.3
  * 53
  * {InlineLean.name}`Paper.thm_onecut`
  * differs as the paper says
  * yes
  * {ref "chapter-programs"}[Programs, automata and cutting]. The laws and the generators of $`A` are standing hypotheses; quotients are rounded down; the programs are written out as `thm_onecut_evaluator` and `thm_onecut_program` (page 69). The printed proof defers to Lean (page 17).
*
  * Theorem J.4
  * 54–55
  * {InlineLean.name}`Paper.thm_cut`, {InlineLean.name}`Paper.exists_setting`
  * differs as the paper says
  * yes
  * {ref "chapter-programs"}[Programs, automata and cutting]. Standing hypotheses as for Theorem J.3; `exists_setting` states the conclusion without them in the contracting case (page 69).
:::

# Appendix K

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Definition K.1
  * 55
  * {InlineLean.name}`Paper.def_acc`
  * matches
  * definition
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]
*
  * Lemma K.2
  * 56
  * {InlineLean.name}`Paper.lem_lowdeg`
  * differs as the paper says
  * yes
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]. Stated for the alphabet of two symbols and the end mark, with explicit constants; the bound on the steps is for accepting runs (pages 69–70).
*
  * Lemma K.3
  * 56
  * {InlineLean.name}`Paper.lem_circuit`, {InlineLean.name}`Paper.lem_circuit_perm`
  * differs as the paper says
  * yes
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]. More general: for every family that is complete for grid sums and every $`H \ge 32` (page 68). `lem_circuit_phi` “states what is used of $`\Phi`, not that it equals the printed sum over words” (page 70).
*
  * Lemma K.4
  * 57
  * {InlineLean.name}`Paper.lem_postpone`
  * matches
  * yes
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]. Explicit constants in place of $`O(\cdot)`.
*
  * Proposition K.5
  * 57–58
  * {InlineLean.name}`Paper.prop_next`, {InlineLean.name}`Paper.scales_setting`
  * differs as the paper says
  * yes
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]. Does not assume the contracting case: the conclusion of Theorem J.4 is a hypothesis (`CutHyp`), with $`H = 16h`, $`h \ge 17`; `scales_setting` is the instance in the contracting case (page 69).
*
  * Theorem K.6
  * 58
  * {InlineLean.name}`Paper.thm_noacc`, {InlineLean.name}`Paper.scales_setting`
  * differs as the paper says
  * yes
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]. As for Proposition K.5; here $`A` has to be finitely generated (page 69).
*
  * Theorem K.7
  * 59
  * {InlineLean.name}`Paper.thm_contracting`
  * matches
  * yes
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]. The hypothesis $`2 \neq 0` is written out. Theorem M.3 uses it for the permanent and the general form `contracting_complete` for $`\mathrm{HC}_m`.
:::

# Appendix L

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Theorem L.1
  * 59
  * {InlineLean.name}`Paper.thm_main`, {InlineLean.name}`Paper.thm_main_form`, {InlineLean.name}`Solution.permanent_over_real`
  * matches
  * yes
  * {ref "chapter-assembly"}[All fields and approximate computation]. `thm_main_form` is the equality of the two forms of the bound.
*
  * Theorem L.2
  * 59
  * {InlineLean.name}`Paper.thm_simple`
  * matches
  * no
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * Corollary L.3
  * 59
  * {InlineLean.name}`Paper.cor_classes`
  * matches
  * no
  * {ref "chapter-assembly"}[All fields and approximate computation]
:::

# Appendix M

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Lemma M.1
  * 60
  * {InlineLean.name}`Paper.lem_transfer`
  * differs as the paper says
  * yes
  * {ref "chapter-assembly"}[All fields and approximate computation]. More general: any algebraically closed field of characteristic $`p` in the place of $`\mathbb{K}` (page 68).
*
  * Proposition M.2
  * 61
  * {InlineLean.name}`Paper.prop_hc_grid`, {InlineLean.name}`Paper.cor_clauses_hc`
  * differs as the paper says
  * yes
  * {ref "chapter-completeness"}[Completeness gadgets]. “Lean has $`\mathrm{HC}_0 = 1`, which matters only for empty $`I`” (page 69).
*
  * Theorem M.3
  * 61
  * {InlineLean.name}`Paper.thm_allfields`
  * matches
  * yes
  * {ref "chapter-assembly"}[All fields and approximate computation]. The Lean proof takes $`c = 1/1600^2`.
*
  * Corollary M.4
  * 62
  * {InlineLean.name}`Paper.cor_allclasses`
  * matches
  * yes
  * {ref "chapter-assembly"}[All fields and approximate computation]
:::

# Appendix N

:::table +header
*
  * Statement
  * Page
  * Lean
  * Lean statement
  * Route
  * Chapter and note
*
  * Definition N.1
  * 62
  * {InlineLean.name}`Paper.def_approx`, {InlineLean.name}`Paper.VPBar`
  * differs as the paper says
  * definition
  * {ref "chapter-assembly"}[All fields and approximate computation]. `def_approx` states the second sentence of the definition; “the last sentence of the definition is the definition of `Paper.VPBar`, and the match rests on reading it” (page 69).
*
  * Lemma N.2
  * 62
  * {InlineLean.name}`Paper.lem_transfer_approx`
  * differs as the paper says
  * yes
  * {ref "chapter-assembly"}[All fields and approximate computation]. As for Lemma M.1.
*
  * Lemma N.3
  * 62
  * {InlineLean.name}`Paper.lem_few_approx`
  * differs as the paper says
  * yes
  * {ref "chapter-flat"}[The flat case]. As for Lemma E.7.
*
  * Proposition N.4
  * 63
  * {InlineLean.name}`Paper.prop_approx_acc`, {InlineLean.name}`Paper.prop_approx_acc_setting`
  * differs as the paper says
  * yes
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]. As for Proposition K.5; `prop_approx_acc_setting` is the instance in the contracting case (page 69). The printed proof defers to Lean (page 17).
*
  * Theorem N.5
  * 64
  * {InlineLean.name}`Paper.thm_approx`
  * matches
  * yes
  * {ref "chapter-assembly"}[All fields and approximate computation]. The Lean proof does not cite Lemma K.3, Theorem K.7 and Theorem M.3; it uses `thm_allfields_exceeds` and the approximate analogues `lem_circuit_approx` and `contracting_approx_complete` (page 70).
*
  * Remark N.6
  * 64
  * not formalized
  * no Lean counterpart
  * —
  * {ref "chapter-assembly"}[All fields and approximate computation]. Page 64: “This remark is the one numbered statement of the paper that has not been formalized in Lean.”
:::

# Lean theorems without a number in the paper

Section Q.3 (page 66): “Many unnumbered steps of the printed proofs have named theorems too.”
The ones below carry content that the chapters use by name. The second column is this
blueprint's summary of the Lean statement, not the paper's text.

:::table +header
*
  * Lean
  * What it states
  * Chapter
*
  * {InlineLean.name}`Paper.hc_mem_VNP`
  * $`(\mathrm{HC}_n) \in \mathrm{VNP}` over every field, with $`r(n) = n^2` summation bits and the exponent $`a = 700` for the family $`(g_n)`: the membership half of Corollary M.4.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Paper.perm_mem_VNP`
  * $`(\mathrm{PERM}_n) \in \mathrm{VNP}` by Ryser's formula; used for Corollary L.3 only.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Paper.vp_subset_vnp`
  * $`\mathrm{VP} \subseteq \mathrm{VNP}` over every commutative semiring, with $`r = 0`.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Paper.exists_beyond_poly`
  * For $`c > 0` and all $`m_0`, $`C` there is $`m \ge m_0` with $`m^{c(\log m)^{1/3}} \ge m^C + C`: the step from the bound to the separations.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Paper.thm_allfields_exceeds`
  * A bound $`2^{c(\log m)^2/\log\log m}` for all large $`m`, for any $`c > 0`, implies the bound $`2^{(\log m)^{4/3}/1600^2}` for all large $`m`: why the absolute constant is that of the flat case.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Paper.thm_main_calculation`
  * For every real $`C`, $`C(\log m)^{4/3} \le (\log m)^2/\log\log m` for all large $`m`.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Paper.exists_closed`
  * For $`p` zero or prime, an algebraically closed field of characteristic $`p` in the lowest universe.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Paper.flat_rate_complete`
  * The flat bound for every family that is complete for grid sums.
  * {ref "chapter-flat"}[The flat case]
*
  * {InlineLean.name}`Paper.flat_rate_approx_complete`
  * The same for approximating circuits.
  * {ref "chapter-flat"}[The flat case]
*
  * {InlineLean.name}`Paper.contracting_complete`
  * The contracting bound for every family that is complete for grid sums.
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]
*
  * {InlineLean.name}`Paper.contracting_approx_complete`
  * The same for approximating circuits.
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]
*
  * {InlineLean.name}`Paper.approx_rate_closed`
  * Both cases over an algebraically closed field, for circuits with constants in the Laurent polynomials.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Paper.gridComplete_perm`
  * $`(\mathrm{PERM}_m)` is complete for grid sums when $`2 \neq 0` (factor 3).
  * {ref "chapter-completeness"}[Completeness gadgets]
*
  * {InlineLean.name}`Paper.gridComplete_hc`
  * $`(\mathrm{HC}_m)` is complete for grid sums over every field (factor 40).
  * {ref "chapter-completeness"}[Completeness gadgets]
*
  * {InlineLean.name}`Paper.lem_circuit_phi`
  * What the proof uses of $`\Phi`.
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]
*
  * {InlineLean.name}`Paper.lem_circuit_approx`
  * The analogue of Lemma K.3 for approximating circuits.
  * {ref "chapter-accelerators"}[Accelerators and the diagonal argument]
*
  * {InlineLean.name}`Paper.exists_laws`
  * Supplies the laws, a standing hypothesis of Theorems H.2 to J.4, in the contracting case.
  * {ref "chapter-laws"}[Rerouting laws and tree networks]
*
  * {InlineLean.name}`Paper.exists_generates`
  * Supplies the named generators of $`A`, a standing hypothesis of Theorems J.3 and J.4.
  * {ref "chapter-programs"}[Programs, automata and cutting]
*
  * {InlineLean.name}`Paper.thm_onecut_evaluator`
  * The evaluator of Theorem J.3, written out.
  * {ref "chapter-programs"}[Programs, automata and cutting]
*
  * {InlineLean.name}`Paper.thm_onecut_program`
  * The cutting program of Theorem J.3, written out.
  * {ref "chapter-programs"}[Programs, automata and cutting]
*
  * {InlineLean.name}`Paper.universal_symbols_ne`
  * The two symbols of the word of an instance are different.
  * {ref "chapter-programs"}[Programs, automata and cutting]
*
  * {InlineLean.name}`Nc.Approximates.exists_laurentPolynomial`
  * An approximating circuit with $`s` gates gives one with $`s` gates whose constants are Laurent polynomials in $`\varepsilon`, over every field.
  * {ref "chapter-assembly"}[All fields and approximate computation]
*
  * {InlineLean.name}`Nc.Approximates.of_laurentPolynomial`
  * The converse.
  * {ref "chapter-assembly"}[All fields and approximate computation]
:::

The declarations of the development that no chapter names are listed, module by module, in the
part {ref "part-generated"}[The Lean development, declaration by declaration].

# What Table 3 does not cover

Section Q.3 (page 70), quoted: “Some steps exist only under names of the underlying library and
not as theorems with prefix `Paper.` These are the sorting pass, the tape encoding and the time
count of Proposition I.1, the constructions of Propositions E.1 and M.2, the induction of Lemma
E.4, the word in Lemma F.2, the averaging in Lemma F.1, the properties of the mean
$`\mathbb{E}` in Section C, and the semantics of scripts inside the evaluator.” And: “Remark N.6,
the example of flattening ranks after Definition A.1, the remarks that follow the proof of
Theorem D.2, the fact that $`r` in the proof of Proposition A.5 is also a limit, and the factor
three between the two ways of counting gates in Section 1 are not formalized.”
{ref "chapter-caveats"}[What a reader should keep in mind] sets out what follows from these for a
reader.
