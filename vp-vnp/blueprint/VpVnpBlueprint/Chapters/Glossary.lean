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
resolves in the build of this site and can be hovered for its statement; a term whose
definition is a node of this site links to that node. Where no declaration corresponds to a
term, the last column says how the Lean development expresses it.

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
  * an array over $`\Bbbk` with one index for each party (page 18; {bpref "Ten"}[the definitions of Section A.1])
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
  * Appendix P: “a nonnegative function on tensors with $`\phi(1) = 1` that is multiplicative, does not increase under restriction and is subadditive” ({bpref "def_spectral"}[Definition A.1])
  * {InlineLean.name}`Ov.Spec`
*
  * $`g_\phi(P)`, $`d_\phi(u,v)`
  * Appendix P: “the exponents in $`\phi(\langle q \rangle_P) = q^{g_\phi(P)}`; $`d_\phi(u,v) = g_\phi(\{u,v\})`” ({bpref "lem_exponents"}[Lemma A.2])
  * {InlineLean.name}`Nc.Price.hexp`, {InlineLean.name}`Ov.Spec.e`
*
  * price; $`|xy|`
  * Appendix P: “a limit of multiples $`c\, d_\phi`; the distance of $`x` and $`y` in it” ({bpref "def_price"}[Definition A.4])
  * {InlineLean.name}`Nc.Price.IsPrice`
*
  * hub
  * Appendix P: “one of two additional parties through which a tensor of small rank is routed” ({bpref "lem_hubs"}[Lemma A.3])
  * the parties `o₁`, `o₂` of {InlineLean.name}`Paper.lem_hubs`
*
  * upper functional
  * a nonnegative function $`p` on tensors with $`p(1) = 1` that is submultiplicative and subadditive on covers (page 20; {bpref "def_gauge"}[the definition], {bpref "prop_gauge"}[Proposition A.5]); Lean says _gauge_
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
  * a pair $`(I, J)` of finite subsets of $`\mathbb{N}` with $`|I| = |J|`; its energy is $`\sum_{i \in I}(2i+1) + \sum_{j \in J}(2j+1)` (page 22; {bpref "lem_count"}[Lemma B.1]); the symbols of given size and energy index the tensors of the crossing identity; Lean says _state_
  * {InlineLean.name}`Nc.Cross.states`
*
  * $`P(E)`
  * the number of symbols of energy at most $`E` ({bpref "lem_count"}[Lemma B.1])
  * {InlineLean.name}`Paper.stateCount`, {InlineLean.name}`Nc.Cross.pairs`
*
  * midpoint; the inequality of Bruhat and Tits
  * a point at half the distance from both; the inequality (C.1) of {bpref "thm_cn"}[Theorem C.1] (pages 25 and 28)
  * {InlineLean.name}`Cat.mid`, {InlineLean.name}`Cat.cn`
*
  * CAT(0) space; price space
  * a complete metric space in which any two points have a midpoint that satisfies the inequality of Bruhat and Tits (page 28; {bpref "CN"}[the definition]); Appendix P, of a price space: “a complete CAT(0) space whose metric is a price”
  * {InlineLean.name}`Cat.CN` together with {InlineLean.name}`Nc.Price.IsPrice` of the metric
*
  * $`\nu(g)`; the seminorm $`N`
  * the root mean square length over boxes, and the seminorm $`N(g) = \inf_S \nu(Sg)/S` defined from it (Section C.2; {bpref "lem_means"}[Lemma C.2]); Lean says _window_ for a box
  * {InlineLean.name}`Paper.meanLength`, {InlineLean.name}`Paper.meanNorm`
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
  * $`D(r)^2` is the mean of $`|a, a+W|^2` over all $`a` and all $`W` of rank $`r` (pages 5 and 29; {bpref "distAtRank"}[the definitions of Section D.1])
  * {InlineLean.name}`Paper.distAtRank`, {InlineLean.name}`Paper.meanSq`
*
  * flat hypothesis, flat case
  * all finite subsets of all Euclidean spaces, with their metrics, are prices ({bpref "def_cases"}[Definition D.1])
  * {InlineLean.name}`Paper.Flat`
*
  * contracting hypothesis, contracting case; $`\mu`, $`s`
  * $`D(\mu) \le s\, D(1)` for all prices on $`\mathrm{Mat}_\mu(\mathbb{F}_2)`, for some integer $`\mu \ge 2` and real $`s` with $`1 \le s`, $`s^2 < \mu` ({bpref "def_cases"}[Definition D.1])
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
  * Appendix P: “a sum over bit vectors of a product of weights of satisfied clauses” ({bpref "clauseSum"}[the definition], page 32)
  * {InlineLean.name}`Paper.clauseSum`
*
  * affine in one variable
  * a constant, or $`a x_i + b` for one variable $`x_i`: the form of the matrix entries in {bpref "cor_clauses"}[Corollary E.2]
  * {InlineLean.name}`Nc.IsAffine`
*
  * complete network; $`f_{k,\ell}`
  * Appendix P: “the tensor network on the complete graph on $`k` nodes with $`\ell` bits on every edge; its polynomial” ({bpref "fkl"}[the definition], page 32)
  * {InlineLean.name}`Nc.CaseI.fkl`; the printed polynomial: {InlineLean.name}`Paper.fklExact`
*
  * the tensor of $`f_{k,\ell}`; end $`(a,b)`
  * the coefficient tensor, with the ends of the edges as parties (pages 8 and 33; {bpref "fklTen"}[the definition])
  * {InlineLean.name}`Paper.fklTen`
*
  * balanced set
  * a set $`S` of nodes with $`k/3 \le |S| \le 2k/3` (pages 7 and 33; {bpref "lem_balanced"}[Lemma E.4])
  * the condition `k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k` in {InlineLean.name}`Paper.lem_balanced`
*
  * the part linear in each block
  * page 7
  * {InlineLean.name}`Paper.linearPart`, {InlineLean.name}`Paper.linearIn`
*
  * complete for grid sums
  * the property of $`(\mathrm{PERM}_M)` and $`(\mathrm{HC}_M)` that the proof uses (Appendix M, page 61; {bpref "GridComplete"}[the definition])
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
  * the upper unitriangular $`h \times h` matrices over $`\mathbb{F}_2`, with the generators $`x_i = 1 + E_{i,i+1}` (pages 9 and 37; {bpref "unitriangular_group"}[the definition])
  * {InlineLean.name}`Nc.Tower.U`, {InlineLean.name}`Nc.Tower.x`
*
  * length function; contracts
  * page 38 ({bpref "contracting_length"}[the definition])
  * {InlineLean.name}`Nc.Flag.Len`, {InlineLean.name}`Nc.Flag.Contr`
*
  * mean over a rank
  * Lemma F.1
  * {InlineLean.name}`Paper.rankMean`
*
  * $`\vartheta_n`, $`C(n)`
  * {bpref "lem_first"}[Lemma F.3] and {bpref "eq_window"}[the display (F.1)]; in Lean explicit numbers that “are not those of the printed proof” (page 68)
  * {InlineLean.name}`Paper.kappa`, {InlineLean.name}`Paper.windowConst`
*
  * window; projection
  * Section F.2 ({bpref "windows"}[the definition]); the projection is defined in Lean as the barycenter of the orbit (page 68)
  * {InlineLean.name}`Nc.Flag.IsoAct`; the window {InlineLean.name}`Nc.Flag.IsoAct.W`, its projection {InlineLean.name}`Nc.Flag.IsoAct.P`; {InlineLean.name}`Paper.projection_nearest`
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
  * $`b = |U_h| = 2^{h(h-1)/2}` (page 41)
  * `2 ^ ee h` with {InlineLean.name}`Nc.Tower.ee`
*
  * load
  * Appendix P: “a vector of natural numbers on pairs of elements, or on edges”
  * written out in {InlineLean.name}`Paper.thm_laws`
*
  * law; slot; channel
  * Appendix P: “an identity that rewrites bits on arbitrary pairs (slots) as a sum of networks with bits on edges (channels)” ({bpref "def_law"}[Definition G.1])
  * {InlineLean.name}`Nc.G.Law`; the chosen family: {InlineLean.name}`Nc.Tow.VLaws`
*
  * the ring $`A`
  * the finitely generated ring generated by the coefficients of the laws ({bpref "thm_laws"}[Theorem G.2])
  * a subring `A` of the field with `Algebra.FiniteType ℤ A`
*
  * the tower of groups
  * Section H.1 ({bpref "prop_tower"}[Proposition H.1])
  * {InlineLean.name}`Nc.Tower.G`, {InlineLean.name}`Nc.Tower.gen`, {InlineLean.name}`Nc.Tower.th`, {InlineLean.name}`Nc.Tower.pr`, {InlineLean.name}`Nc.Tower.XX`, {InlineLean.name}`Nc.Tower.VV`, {InlineLean.name}`Nc.Tower.JJ`
*
  * packet
  * Appendix P: “a string of $`\ell` bits carried between two nodes”; Lean says _unit_
  * the packets of a given network: {InlineLean.name}`Paper.NetUnit`; the names of the packets in the construction of Theorem H.2: {InlineLean.name}`Nc.G.Uid`; a content, absent or a string of $`\ell` bits: {InlineLean.name}`Nc.UW`
*
  * network; node tensor; value; outcome
  * Appendix P: “numbers of packets on pairs of nodes and a tensor at each node; the sum over all contents of the packets of the product of the node tensors; the numbers of packets that a law puts on its channels”; Lean says _table_ for a node tensor ({bpref "network_value"}[the definition], page 45)
  * {InlineLean.name}`Paper.NodeTable`, {InlineLean.name}`Paper.netValue`; an outcome is the argument `o` of the conditions of {InlineLean.name}`Nc.G.Plan` ({bpref "law_move"}[the definition]); the trees of Theorem H.2 are the structure {InlineLean.name}`Paper.ThinTrees`
*
  * relay
  * a move that replaces a packet between two nodes by two packets through a third (page 45); in Lean “a law with one slot, two channels, one index and $`\lambda = 0`, applied to a batch of packets” (page 68; {bpref "relay"}[the definition])
  * {InlineLean.name}`Nc.Tow.relay`
*
  * good outcome
  * Section H.2; tested in Lean with $`\lfloor 2 C_1 a_1^2 \rfloor` (page 69; {bpref "thm_tree_good"}[the node])
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
  * a nondeterministic program on binary trees with weights in $`A` (Section I.1; {bpref "def_program"}[the definition])
  * {InlineLean.name}`NS1.Fm`, {InlineLean.name}`NS1.Fm.ofTree`
*
  * run; weight; tally
  * Appendix P: “a computation of a nondeterministic program; the element of $`A` that it accumulates; the list of names of constants that it has used”; Lean says _bill_ for a tally ({bpref "def_runs"}[the definition])
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
  * Appendix P: “all runs halt, and the accepting ones have empty tallies and take at most $`\tau` steps” ({bpref "def_plain"}[the definition])
  * {InlineLean.name}`NS1.Plain`
*
  * tape automaton
  * Appendix P: “a finite automaton with a matrix over $`A` for each letter, whose letters write on the two sides of tapes” ({bpref "def_tape_automaton"}[the definition])
  * {InlineLean.name}`Nc.Letter`, {InlineLean.name}`Nc.runVal`
*
  * the word of an instance
  * the input of the universal automaton ({bpref "prop_universal"}[Proposition I.1])
  * {InlineLean.name}`Nc.Dl.wordG`, {InlineLean.name}`NS1.tbits`
*
  * the data of a run as a network
  * {bpref "lem_runnet"}[Lemma I.2]
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
  * {bpref "def_cut"}[Definition J.1]
  * {InlineLean.name}`NS1.CutD`, {InlineLean.name}`NS1.CutProg`
*
  * piece
  * the short instances that a run of the cutting program lists (page 9; {bpref "prop_pieces"}[Proposition J.2]); Lean says _group_
  * the value of a piece: {InlineLean.name}`Nc.G.grpVal`; the clauses of Proposition J.2: {InlineLean.name}`Paper.PieceCut`
*
  * evaluator
  * the program of Theorem J.3 that evaluates a piece ({bpref "thm_onecut_evaluator"}[the node])
  * its specification: {InlineLean.name}`Nc.Grp.GroupOK`
*
  * the conclusion of the cutting theorem
  * {bpref "thm_cut"}[Theorem J.4]; a hypothesis of Proposition K.5, Theorem K.6 and Proposition N.4 in Lean
  * {InlineLean.name}`NS1.CutHyp`
*
  * constants, names
  * {bpref "def_acc"}[Definition K.1]; in Lean a trie with the constants at its leaves
  * {InlineLean.name}`NS1.KT`
*
  * accelerator
  * Appendix P: “a program that evaluates sums over $`v^H` steps within $`v^{H-16}` steps” ({bpref "def_acc"}[Definition K.1], {InlineLean.name}`NS1.HasAcc`)
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
  * the polynomial (2.2) of the overview (page 6)
  * not defined; what is used of it: {InlineLean.name}`Paper.lem_circuit_phi` ({bpref "lem_circuit_phi"}[the node])
*
  * approximate accelerator
  * Section N.3 (page 63; {bpref "def_approx_acc"}[the definition])
  * {InlineLean.name}`NS1.HasAccA`, {InlineLean.name}`NS1.IsAccA`
*
  * exponent vector $`e`; the instances $`z_e`
  * Lemma K.4 ({bpref "lem_postpone"}[the node]); Lean says _budget_ for an exponent vector
  * {InlineLean.name}`NS1.Bt`, {InlineLean.name}`Paper.postponed`
*
  * interpreter
  * the fixed program of Lemma K.4 that runs a program and counts the names it uses ({bpref "lem_postpone"}[the node])
  * {InlineLean.name}`NS1.IF`, inside the fixed program {InlineLean.name}`NS1.WF`
*
  * the diagonal program $`\mathsf{P}`
  * proof of Theorem K.6 (page 59; {bpref "thm_noacc_diagonal"}[the node])
  * {InlineLean.name}`NS1.diagF`
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
