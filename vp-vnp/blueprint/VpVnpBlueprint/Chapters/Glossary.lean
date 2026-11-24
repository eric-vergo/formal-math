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

#doc (Manual) "Glossary" =>

%%%
tag := "chapter-glossary"
file := "glossary"
htmlSplit := .never
number := false
%%%

The paper coins a number of terms and uses others in a special sense; its Appendix P (pages
65–66 of {repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) lists them. This chapter gives each term,
and the notation of the paper that the chapters of this blueprint use, with the Lean declaration
that formalizes it, in the order of the paper. Where the column _meaning_ is in quotation marks it
quotes Appendix P or the page named; otherwise it is a short description, adapted from the page
named, and the definition is in the chapter linked at the head of each table. Every Lean name
resolves in the build of this site and can be hovered for its statement. Where no declaration
corresponds to a term, the last column says how the Lean development expresses it.

# The Lean development's other words

Section Q.3 of the paper (pages 66–68), quoted: “The Lean development uses some other words. It
says _gauge_ for an upper functional, _unit_ for a packet, _table_ for a node tensor, _bill_ for
a tally, _near pair_ for an edge of the Cayley graph of $`U_h`, _window_ for the boxes of Section
C as well as for the windows of Section F, and _state_ for the symbols of Section B.” This
blueprint uses the paper's words in its text and the Lean words only inside Lean names.

The names of the Lean theorems that state numbered statements are formed, in the paper's words
(page 17), “from the kind of the statement and a short name, such as `thm_alt` for Theorem D.2”;
{ref "chapter-table3"}[The paper's statements and their Lean names] lists them.

# Conventions

From “Notation and conventions” (pages 17–18).

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * $`\log`
  * the logarithm to the base two, “here and throughout” (page 2)
  * `Real.logb 2`
*
  * $`\ln`
  * the natural logarithm
  * `Real.log`
*
  * $`\lg n`
  * $`\lfloor \log n \rfloor + 1`, the number of binary digits of $`n \ge 1`
  * {InlineLean.name}`NS1.lg`
*
  * $`\mathbb{N}`, $`[k]`
  * $`\mathbb{N}` contains 0; $`[k] = \{1, \ldots, k\}`
  * `ℕ`; `Fin k`, which is $`\{0, \ldots, k-1\}`
*
  * $`[P]`
  * 1 if the condition $`P` holds and 0 otherwise
  * `if P then 1 else 0`
*
  * $`c`, $`C`
  * “a small and a large constant whose values may differ from one statement to the next”
  * existential quantifiers in each Lean statement; $`C`, $`a`, $`\alpha` are natural numbers (page 68)
*
  * $`\Bbbk`
  * the field of coefficients: $`\mathbb{R}` in Sections A to L, “of which we use only that it is a field in which $`2 \neq 0`”; any field in Appendices M and N
  * a variable `K : Type` with `[Field K]`, and the hypothesis `(2 : K) ≠ 0` where it is used; `F` in `Statement.lean`
*
  * $`\mathbb{K}`
  * the algebraic closure of the prime field of characteristic $`p`
  * any algebraically closed field of characteristic $`p`; {InlineLean.name}`Paper.exists_closed`
*
  * $`|xy|`, $`|x, y|`
  * the distance of $`x` and $`y` in the price under discussion
  * a function `w x y` or `dist x y`
*
  * $`\mathbb{E}`, $`\mathbb{E}_g`
  * an expectation; with a subscript, the uniform average over a finite set
  * sums divided by cardinalities
:::

# Section 1: the model and the classes

{ref "chapter-statement"}[The statement to trust] reads these definitions in full.

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * arithmetic circuit, gate, size
  * a finite list of polynomials, each a variable, a constant, or the sum or product of two earlier entries; the size is the length of the list (pages 3–4)
  * {InlineLean.name}`Statement.Computes`, {InlineLean.name}`Nc.Computes`, {InlineLean.name}`Nc.IsStep`
*
  * $`\mathrm{PERM}_m`
  * $`\sum_{\sigma \in S_m} \prod_i x_{i,\sigma(i)}` (page 1)
  * {InlineLean.name}`Statement.perm`, {InlineLean.name}`Nc.genPerm`, {InlineLean.name}`Paper.permInt`
*
  * $`\mathrm{HC}_m`
  * the same sum over the $`(m-1)!` cyclic permutations (page 1)
  * {InlineLean.name}`Statement.hc`, {InlineLean.name}`Nc.genHC`, {InlineLean.name}`Nc.Hc.hcSum`
*
  * family; VP; VNP
  * Valiant's classes (page 4)
  * {InlineLean.name}`Statement.Family`, {InlineLean.name}`Statement.VP`, {InlineLean.name}`Statement.VNP`, {InlineLean.name}`Nc.Family`, {InlineLean.name}`Nc.VP`, {InlineLean.name}`Nc.VNP`, {InlineLean.name}`Nc.bits`
*
  * approximates; $`\overline{\mathrm{VP}}`
  * Definition 1.3, repeated as Definition N.1
  * {InlineLean.name}`Statement.Approximates`, {InlineLean.name}`Statement.VPBar`, {InlineLean.name}`Nc.Approximates`, {InlineLean.name}`Paper.VPBar`
*
  * the bound $`m^{c(\log m)^{1/3}}`
  * Theorem 1.1
  * {InlineLean.name}`Statement.Beyond`, {InlineLean.name}`Paper.thm_main_form`
:::

# Appendix A: tensors, spectral points and prices

{ref "chapter-spectral"}[Tensors, spectral points and prices].

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * party
  * an element of the finite index set $`I` (page 18)
  * an element of a type `I` with `[Fintype I]`
*
  * tensor on $`I`
  * an array over $`\Bbbk` with one index for each party (page 18)
  * {InlineLean.name}`Ov.Ten`
*
  * restriction
  * $`s = (\bigotimes_p A_p)\, t` for linear maps $`A_p` (page 18)
  * {InlineLean.name}`Ov.Ten.Restr`; mutual restriction: {InlineLean.name}`Ov.Ten.Equi`
*
  * cover
  * $`s = s_1 + \cdots + s_r` with every $`s_j` a restriction of $`t_j` (page 18)
  * {InlineLean.name}`Ov.Ten.SumRestr`
*
  * product $`st`, the tensor 1, powers
  * each party holds its index of $`s` and its index of $`t` (page 18)
  * `*` and `1` on `Ov.Ten`; {InlineLean.name}`Ov.Ten.kpow`, {InlineLean.name}`Ov.Ten.prod`
*
  * push-forward $`\pi t`; flattening
  * the party $`\pi(p)` holds the index of $`p` (page 18)
  * {InlineLean.name}`Ov.Ten.push`
*
  * unit tensor $`\langle q \rangle_P`
  * $`\sum_{i=1}^q \bigotimes_{p \in P} e_i` (page 18)
  * {InlineLean.name}`Ov.Ten.unit`
*
  * wire $`\langle q \rangle_{uv}`
  * Appendix P: “the unit tensor on two parties $`u \neq v`; it has dimension $`q` and carries $`\log q` bits”
  * {InlineLean.name}`Ov.Ten.wire`
*
  * graph tensor
  * a product of wires (page 18)
  * a product, by `Ov.Ten.prod`, of wires
*
  * spectral point $`\phi`
  * Appendix P: “a nonnegative function on tensors with $`\phi(1) = 1` that is multiplicative, does not increase under restriction and is subadditive” (Definition A.1)
  * {InlineLean.name}`Ov.Spec`
*
  * $`g_\phi(P)`, $`d_\phi(u,v)`
  * Appendix P: “the exponents in $`\phi(\langle q \rangle_P) = q^{g_\phi(P)}`; $`d_\phi(u,v) = g_\phi(\{u,v\})`” (Lemma A.2)
  * {InlineLean.name}`Nc.Price.hexp`, {InlineLean.name}`Ov.Spec.e`
*
  * price; $`|xy|`
  * Appendix P: “a limit of multiples $`c\, d_\phi`; the distance of $`x` and $`y` in it” (Definition A.4)
  * {InlineLean.name}`Nc.Price.IsPrice`
*
  * hub
  * Appendix P: “one of two additional parties through which a tensor of small rank is routed” (Lemma A.3)
  * the parties `o₁`, `o₂` of {InlineLean.name}`Paper.lem_hubs`
*
  * upper functional
  * the functionals of Proposition A.5 (page 20); Lean says _gauge_
  * {InlineLean.name}`Ov.PreSpec`
:::

# Appendices B and C: crossing wires and curvature

{ref "chapter-curvature"}[Two crossing wires and nonpositive curvature].

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * symbol; its energy
  * the index of the tensors in the crossing identity (page 22); Lean says _state_
  * {InlineLean.name}`Nc.Cross.states`
*
  * $`P(E)`
  * the number of symbols of energy at most $`E` (Lemma B.1)
  * {InlineLean.name}`Paper.stateCount`, {InlineLean.name}`Nc.Cross.pairs`
*
  * midpoint; the inequality of Bruhat and Tits
  * page 8; Theorem C.1
  * {InlineLean.name}`Cat.mid`, {InlineLean.name}`Cat.cn`
*
  * CAT(0) space; price space
  * Appendix P: “a complete CAT(0) space whose metric is a price”
  * {InlineLean.name}`Cat.CN` together with {InlineLean.name}`Nc.Price.IsPrice` of the metric
*
  * $`\nu(g)`; the seminorm $`N`
  * the root mean square length over boxes from which $`N` is defined (Section C.2); Lean says _window_ for a box
  * {InlineLean.name}`Paper.meanLength`
:::

# Appendix D: the two cases

{ref "chapter-dichotomy"}[The two cases].

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * $`\mathrm{Mat}_\mu(\mathbb{F}_2)`
  * the $`\mu \times \mu` matrices over the field with two elements, as a set of parties with an addition
  * {InlineLean.name}`Nc.Flag.Mt`
*
  * $`D(r)`
  * $`D(r)^2` is the mean of $`|a, a+W|^2` over all $`a` and all $`W` of rank $`r` (page 5)
  * {InlineLean.name}`Paper.distAtRank`, {InlineLean.name}`Paper.meanSq`
*
  * flat hypothesis, flat case
  * Definition D.1
  * {InlineLean.name}`Paper.Flat`, {InlineLean.name}`Nc.Flag.CaseOne`
*
  * contracting hypothesis, contracting case; $`\mu`, $`s`
  * Definition D.1
  * {InlineLean.name}`Paper.Contracting`
:::

# Appendix E: completeness and the flat case

{ref "chapter-completeness"}[Completeness gadgets] and {ref "chapter-flat"}[The flat case].

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * clause sum
  * Appendix P: “a sum over bit vectors of a product of weights of satisfied clauses”
  * {InlineLean.name}`Paper.clauseSum`
*
  * affine in one variable
  * the form of the matrix entries in Corollary E.2
  * {InlineLean.name}`Nc.IsAffine`
*
  * complete network; $`f_{k,\ell}`
  * Appendix P: “the tensor network on the complete graph on $`k` nodes with $`\ell` bits on every edge; its polynomial”
  * {InlineLean.name}`Nc.CaseI.fkl`; the printed polynomial: {InlineLean.name}`Paper.fklExact`
*
  * the tensor of $`f_{k,\ell}`; end $`(a,b)`
  * the coefficient tensor, with the ends of the edges as parties (page 8)
  * {InlineLean.name}`Paper.fklTen`
*
  * balanced set
  * a set $`S` of nodes with $`k/3 \le |S| \le 2k/3` (page 7)
  * the condition `k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k` in {InlineLean.name}`Paper.lem_balanced`
*
  * the part linear in each block
  * page 7
  * {InlineLean.name}`Paper.linearPart`, {InlineLean.name}`Paper.linearIn`
*
  * complete for grid sums
  * Appendix M (page 61)
  * {InlineLean.name}`Nc.GridComplete`
:::

# Appendix F: the Poincaré inequality

{ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups].

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * $`U_h`; its generators
  * the upper unitriangular $`h \times h` matrices over $`\mathbb{F}_2` (page 9)
  * {InlineLean.name}`Nc.Tower.U`, {InlineLean.name}`Nc.Tower.x`
*
  * length function; contracts
  * page 38
  * {InlineLean.name}`Nc.Flag.Len`, {InlineLean.name}`Nc.Flag.Contr`
*
  * mean over a rank
  * Lemma F.1
  * {InlineLean.name}`Paper.rankMean`
*
  * $`\vartheta_n`, $`C(n)`
  * Lemma F.3 and (F.1); in Lean explicit numbers that “are not those of the printed proof” (page 68)
  * {InlineLean.name}`Paper.kappa`, {InlineLean.name}`Paper.windowConst`
*
  * window; projection
  * Section F; the projection is defined in Lean as the barycenter of the orbit (page 68)
  * {InlineLean.name}`Nc.Flag.IsoAct`, {InlineLean.name}`Paper.projection_nearest`
:::

# Appendices G and H: laws and tree networks

{ref "chapter-laws"}[Rerouting laws and tree networks].

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * edge
  * an edge of the Cayley graph of $`U_h`; Lean says _near pair_
  * {InlineLean.name}`Nc.Tower.NN`, {InlineLean.name}`Nc.Vp.cNear`, {InlineLean.name}`Nc.Vp.dNear`
*
  * $`b`
  * in Lean `2 ^ ee h` with {InlineLean.name}`Nc.Tower.ee`
  * {InlineLean.name}`Nc.Tower.ee`
*
  * load
  * Appendix P: “a vector of natural numbers on pairs of elements, or on edges”
  * written out in {InlineLean.name}`Paper.thm_laws`
*
  * law; slot; channel
  * Appendix P: “an identity that rewrites bits on arbitrary pairs (slots) as a sum of networks with bits on edges (channels)” (Definition G.1)
  * {InlineLean.name}`Nc.G.Law`; the chosen family: {InlineLean.name}`Nc.Tow.VLaws`
*
  * the ring $`A`
  * the finitely generated ring generated by the coefficients of the laws (Theorem G.2)
  * a subring `A` of the field with `Algebra.FiniteType ℤ A`
*
  * the tower of groups
  * Section H.1
  * {InlineLean.name}`Nc.Tower.G`, {InlineLean.name}`Nc.Tower.gen`, {InlineLean.name}`Nc.Tower.th`, {InlineLean.name}`Nc.Tower.pr`, {InlineLean.name}`Nc.Tower.XX`, {InlineLean.name}`Nc.Tower.VV`, {InlineLean.name}`Nc.Tower.JJ`
*
  * packet
  * Appendix P: “a string of $`\ell` bits carried between two nodes”; Lean says _unit_
  * in the fields of {InlineLean.name}`Paper.ThinTrees`
*
  * network; node tensor; value; outcome
  * Appendix P: “numbers of packets on pairs of nodes and a tensor at each node; the sum over all contents of the packets of the product of the node tensors; the numbers of packets that a law puts on its channels”; Lean says _table_ for a node tensor
  * in the fields of {InlineLean.name}`Paper.ThinTrees`
*
  * good outcome
  * Section H.2; tested in Lean with $`\lfloor 2 C_1 a_1^2 \rfloor` (page 69)
  * {InlineLean.name}`Paper.goodBound`, {InlineLean.name}`Paper.thm_tree_good`
:::

# Appendix I: programs and automata

{ref "chapter-programs"}[Programs, automata and cutting].

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * binary tree; size
  * the data of the program model (Section I.1)
  * {InlineLean.name}`NS1.Tree`, {InlineLean.name}`NS1.Tree.size`
*
  * program
  * a nondeterministic program on binary trees with weights in $`A` (Section I.1)
  * {InlineLean.name}`NS1.Fm`, {InlineLean.name}`NS1.Fm.ofTree`
*
  * run; weight; tally
  * Appendix P: “a computation of a nondeterministic program; the element of $`A` that it accumulates; the list of names of constants that it has used”; Lean says _bill_ for a tally
  * {InlineLean.name}`NS1.Run`, {InlineLean.name}`NS1.evl`
*
  * all runs halt
  * Section I.1
  * {InlineLean.name}`NS1.Hl`
*
  * named generators of $`A`
  * Section I.1
  * {InlineLean.name}`Paper.Generates`
*
  * instance $`z`; $`\mathrm{sum}(z)`
  * Appendix P: “a program with an argument; the sum of the weights of its accepting runs”
  * {InlineLean.name}`NS1.pv`
*
  * $`\tau`-plain
  * Appendix P: “all runs halt, and the accepting ones have empty tallies and take at most $`\tau` steps”
  * {InlineLean.name}`NS1.Plain`
*
  * tape automaton
  * Appendix P: “a finite automaton with a matrix over $`A` for each letter, whose letters write on the two sides of tapes”
  * {InlineLean.name}`Nc.Letter`, {InlineLean.name}`Nc.runVal`
*
  * the word of an instance
  * the input of the universal automaton (Proposition I.1)
  * {InlineLean.name}`Nc.Dl.wordG`, {InlineLean.name}`NS1.tbits`
*
  * the data of a run as a network
  * Lemma I.2
  * {InlineLean.name}`Nc.Cut.RowData`, {InlineLean.name}`Nc.Cut.ValidRows`
:::

# Appendices J and K: cutting and accelerators

{ref "chapter-programs"}[Programs, automata and cutting] and {ref "chapter-accelerators"}[Accelerators and the diagonal argument].

:::table +header
*
  * Term or notation
  * Meaning
  * Lean
*
  * scale $`v`
  * a large integer (page 9)
  * a natural number `v`
*
  * a program cuts
  * Definition J.1
  * {InlineLean.name}`NS1.CutD`, {InlineLean.name}`NS1.CutProg`
*
  * piece
  * the short instances that a run of the cutting program lists (page 9)
  * {InlineLean.name}`Paper.PieceCut`
*
  * the conclusion of the cutting theorem
  * Theorem J.4; a hypothesis of Proposition K.5, Theorem K.6 and Proposition N.4 in Lean
  * {InlineLean.name}`NS1.CutHyp`
*
  * constants, names
  * Definition K.1; in Lean a trie with the constants at its leaves
  * {InlineLean.name}`NS1.KT`
*
  * accelerator
  * Appendix P: “a program that evaluates sums over $`v^H` steps within $`v^{H-16}` steps” (Definition K.1)
  * {InlineLean.name}`NS1.HasAcc`, {InlineLean.name}`NS1.IsAccT`
*
  * short instance
  * of size at most $`v^{H-32}` (page 9)
  * `z.size ≤ v ^ (H - 32)`
*
  * the point that encodes a word
  * page 6
  * {InlineLean.name}`NS1.codeB`, {InlineLean.name}`Nc.code1`
*
  * $`\Phi`
  * the polynomial (2.2) of the overview
  * not defined; what is used of it: {InlineLean.name}`Paper.lem_circuit_phi`
*
  * approximate accelerator
  * Appendix N
  * {InlineLean.name}`NS1.HasAccA`, {InlineLean.name}`NS1.IsAccA`
:::

# The libraries

The Lean development consists of the statement file, the challenge and the solution, and four
libraries. `Paper` holds one theorem for each numbered statement, with the paper's short name,
and the assembly of the main theorems. `Ov` holds tensors, restrictions, spectral points and
duality. `NS1` holds the program model on binary trees and what is proved about accelerators.
`Nc` holds the rest, by far the largest part: prices and their geometry, the flat case, the
completeness constructions, laws, towers and trees, tape automata, the universal automaton, the
evaluator and the cutting program. The part
{ref "part-generated"}[The Lean development, declaration by declaration] lists them module by
module.
