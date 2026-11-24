/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic), GPT (OpenAI)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.Completeness
import VpVnpBlueprint.Chapters.Dichotomy
import Paper.Flat
import Paper.Convex
import Paper.Rate
import Paper.Approximate

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "The flat case" =>

%%%
tag := "chapter-flat"
file := "flat-case"
htmlSplit := .never
number := false
%%%

This chapter proves the lower bound under the flat hypothesis of {bpref "def_cases"}[]: if all
finite Euclidean configurations are prices over $`\Bbbk`, then every circuit over $`\Bbbk` for the
network polynomial $`f_{k,\ell}` with $`\ell \geq 100\sqrt{k}` has at least
$`2^{\ell k^{3/2}/16}` gates (Proposition E.10), and therefore, if $`2 \neq 0` in $`\Bbbk`, every
circuit for $`\mathrm{PERM}_m` has more than $`2^{(\log m)^{4/3}/1600^2}` gates for large $`m`
(Theorem E.11); the same bound holds for $`\mathrm{HC}_m` without the condition on $`2`, and for
approximating circuits. It is the complete argument for one of the two cases, and the source of
the exponent in the main theorem. The chapter follows Sections E.2 to E.6 of the paper (pages 33–37) and Section
N.2 (page 62) of {repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]; the reduction from the permanent
(Proposition E.1, Corollary E.2, Lemma E.3) is in
{ref "chapter-completeness"}[Completeness gadgets].

Status of the printed proof. The paper (page 17): “Section E treats the flat case completely, and
nothing after it is needed for that case except Section L.” The proofs of Sections A to G “are
meant to be complete, if terse” (page 17), and none of the statements of this chapter carries a
formalization note.

# The argument in outline

The following outline is this blueprint's summary of pages 33–37; the numbered statements follow.

1. *The tensor.* The coefficients of $`f_{k,\ell}`, read on the $`k(k-1)` _ends_ of the edges of
   the complete graph, form the graph tensor $`T_{k,\ell}` with one wire of dimension $`2^\ell` on
   each of the $`N = \binom{k}{2}` edges. For a spectral point $`\phi`,
   $`\log \phi(T_{k,\ell}) = \ell \sum_{e} d_\phi(e)`, the sum over the edges of the distance of
   the two ends ({bpref "fklTen"}[]).
2. *What a circuit gives.* A circuit with $`L` gates for $`f_{k,\ell}` writes $`T_{k,\ell}` as a
   sum, over the at most $`2^k` balanced sets $`S` of nodes, of tensors $`t_S` of rank at most
   $`L` across the cut between the ends at nodes of $`S` and the other ends
   ({bpref "lem_balanced"}[]). By Lemma A.3 each $`t_S` is a restriction of a network $`T_S` in
   which every end is wired to one of two hubs $`\pm o_S` and the hubs are joined by a wire of
   dimension $`L` ({bpref "prop_flat_lower_sum"}[]).
3. *The inequality.* Subadditivity gives $`\phi(T_{k,\ell}) \leq 2^k \max_S \phi(T_S)`, and in the
   refined form of {bpref "lem_few"}[], $`\phi(T_{k,\ell}) \leq (2^k)^{g_\phi(\mathcal{E})} \max_S \phi(T_S)`
   with $`\mathcal{E}` the set of all ends. Taking logarithms:
   $$`\ell \sum_e d_\phi(e) \;\leq\; k\, g_\phi(\mathcal{E}) \;+\; \ell \sum_{\text{ends } \epsilon} d_\phi(\epsilon, \text{hub of } \epsilon) \;+\; d_\phi(o_S, -o_S) \log L \qquad \text{for some balanced } S.`
4. *The flat hypothesis.* Choose points of $`\mathbb{R}^k` for the ends and the hubs so that the
   two ends of every edge are at distance $`1`, while for every balanced $`S` the distances from
   the ends to their hubs add up to at most $`N - \tfrac{4}{81}k`, and the two hubs are at
   distance $`2\eta = \tfrac{4}{9\sqrt{k}}`. (A balanced set separates
   $`|S|(k - |S|) \geq 2k^2/9` of the edges, and the hubs are displaced towards the two sides.)
   The flat hypothesis supplies $`\phi` and a scale $`c \geq 0` with $`c\, d_\phi` as close to
   these Euclidean distances as desired. Multiplying the inequality of step 3 by $`c`:
   $`\ell N \lesssim k \cdot c\, g_\phi(\mathcal{E}) + \ell \bigl(N - \tfrac{4}{81}k\bigr) + \tfrac{4}{9\sqrt{k}} \log L`.
5. *The overhead.* The term $`k \cdot c\, g_\phi(\mathcal{E})` is the cost of naming a balanced set.
   With the ends at facet centres of a cube, $`c\, g_\phi(\mathcal{E}) \leq \sqrt{k} + \varepsilon`
   ({bpref "prop_cube"}[], through {bpref "lem_convex"}[]), so the overhead is about
   $`k^{3/2}` and is absorbed by $`\ell k` as soon as $`\ell \geq 100\sqrt{k}`. This leaves
   $`\log L \gtrsim \ell k^{3/2}`.

*Where the exponent comes from.* The reduction of Lemma E.3 needs
$`m \geq 3k^3 \ell\, 2^{k\ell}`, so $`\log m` is about $`k\ell`. The paper (page 37): “For the
permanent we take $`\ell = 100\sqrt{k}`, the smallest value that Proposition E.10 admits, which
makes $`\log m` of order $`k^{3/2}` and the bound of order $`k^2`.” Hence
$`\log L \gtrsim (\log m)^{4/3}`, that is, $`L \geq m^{c(\log m)^{1/3}}`. On the limits of the
method (page 60): “The exponent $`1/3` comes from the flat case alone, since the contracting case
gives the stronger bound of Theorem K.7. Two quantities limit the argument in the flat case: the
$`k` bits that name a balanced set, and the scaled exponent $`c\, g_\phi(P)` of the set $`P` of
all ends, which Proposition E.9 bounds by about $`\sqrt{k}`. We do not know whether the bound in
the flat case can be improved.”

*The route of the Lean proof.* Two of the numbered statements of this chapter, Proposition
E.5 and Theorem E.6, are formalized but are not used by the theorems of `Solution`. Appendix Q.3
(page 66): “The theorems of `Solution` are proved through them, with these exceptions, which are
not on that route: Theorem L.2, Corollary L.3, the qualitative bound in the flat case
(Proposition E.5 and Theorem E.6) and the definitions.” And (page 70): “Proposition E.10 uses the
step `prop_flat_lower_sum` of the proof of Proposition E.5, not the proposition.” The route is
therefore Lemma E.4, the step {bpref "prop_flat_lower_sum"}[], Lemmas E.7 and E.8, Propositions
E.9 and E.10, and then {bpref "flat_rate_complete"}[] for the exact bound of both
families, including the permanent. {bpref "thm_flat_rate"}[Theorem E.11] specializes the
general bound to the permanent and supplies the qualitative Theorem E.6. The approximate
exports use {bpref "flat_rate_approx_complete"}[], with Lemma N.3 in place of Lemma E.7.
{ref "chapter-table3"}[The paper's statements and their Lean names] records each export's
dependence on the named theorems.

# E.2. The network polynomial (continued): balanced products

:::lemma_ "lem_balanced" (lean := "Paper.lem_balanced, Paper.linearPart, Paper.linearIn, Paper.lem_balanced_cf") (parent := "part-flat")
*Lemma E.4 of the paper* (balanced products; page 33), quoted: “Let a polynomial over a
commutative ring in $`k \geq 2` blocks of variables of equal size have a circuit with $`L` gates,
and let $`f` be its part that is linear in each block. Then
$$`f = \sum_{S \text{ balanced}} \; \sum_{j=1}^{L} g_{S,j}\, h_{S,j},`
where $`g_{S,j}` is linear in each block of $`S`, $`h_{S,j}` is linear in each block outside
$`S`, and neither contains other variables.” Before the lemma (page 33): “We call a set
$`S \subseteq [k]`, or the set of blocks with numbers in $`S`, _balanced_ if
$`k \leq 3|S| \leq 2k`.” After it: “Some of the products may be zero, so that there are at most
$`L` products for every balanced set.”

The Lean statement differs as the paper says. Appendix Q.3 (page 68): “Lemma E.4 is proved over
every commutative semiring”. The variables are indexed by `Fin k × T` for a finite type `T` (the
common size of the blocks); `Paper.linearPart P` is the part of `P` that is linear in each block,
$`\sum_x \mathrm{coeff}(P; \prod_a x_{a, x(a)}) \prod_a x_{a, x(a)}`; `Paper.linearIn S c` is the
polynomial with coefficients `c` that is linear in each block of `S` and free of the others; and
for every balanced `S` there are exactly `L` products, indexed by `Fin L`.
`Paper.lem_balanced_cf` is the same statement for coefficients: the coefficient of
$`\prod_a x_{a, y(a)}` in `P` is $`\sum_S \sum_\delta g_{S,\delta}(y|_S)\, q_{S,\delta}(y|_{S^c})`.
The circuit is for `P` itself; nothing is assumed about the parts of `P` that are not linear in
each block.
:::

:::proof "lem_balanced"
*The paper's proof* (page 33), quoted: “We argue by induction along the circuit. For a gate
$`\gamma` and a set $`S` of blocks let $`\gamma_S` be the part of $`\gamma` of degree one in each
block of $`S` and zero in the others. We show that if $`3|S| > 2k`, then
$`\gamma_S = \sum_{\delta, A} \delta_A\, h_{\delta, A}` over the gates $`\delta` and the balanced
subsets $`A` of $`S`, where $`h_{\delta, A}`, which depends on $`\gamma` and $`S`, is linear in
each block of $`S \setminus A` and free of the other blocks. Variables and constants have
$`\gamma_S = 0`, because $`S` has at least two elements, and for a sum of two gates we add their
representations. For a product $`\gamma = \gamma_1 \gamma_2` we have
$`\gamma_S = \sum (\gamma_1)_A (\gamma_2)_B` over all $`A \sqcup B = S`. In each term the larger
of the two sets, say $`A`, has more than $`k/3` elements, so either $`A` is balanced and the term
has the required form, or the induction hypothesis applies to $`(\gamma_1)_A` and we multiply by
$`(\gamma_2)_B`. Finally we take $`\gamma` to be the output and $`S = [k]`, so that
$`\gamma_S = f`, and collect the terms by $`(\delta, A)`, of which there are at most $`L` for
every balanced $`A`.”

The paper introduces the lemma with: it “concerns arbitrary circuits, and its proof is the
argument behind depth reduction \[Hya79, VSBR83\]”. This is one of the two steps of the whole
proof that look inside the circuit (Figure 1, page 5: “The two arrows marked C are the only steps
that look inside the circuit, both times at the polynomial at every gate”). Appendix Q.3 (page
70) lists “the induction of Lemma E.4” among the steps that exist only under names of the
underlying library; in the Lean proof it is the theorem `Nc.CaseI.dec_gate` of
{repoFile "vp-vnp/Nc/CaseI/Multi.lean"}[`Nc/CaseI/Multi.lean`].
:::

:::definition "fklTen" (lean := "Paper.fklTen, Paper.fklTen_val, Paper.fklTen_price") (parent := "part-flat")
*Definition of the paper* (the tensor $`T_{k,\ell}`; page 33, unnumbered), quoted: “The
coefficients of $`f_{k,\ell}` form a tensor on the $`k` nodes, in which the node $`a` has the
index $`\rho_a \in \{0,1\}^{(k-1)\ell}`. We give each of the $`k-1` strings of $`\rho_a` to a
party of its own, the _end_ $`(a, b)` of the edge $`ab` at $`a` (a half-edge in the language of
graph theory). On the $`k(k-1)` ends this tensor is
$$`T_{k,\ell} = \prod_{a<b} \langle 2^\ell \rangle_{(a,b)(b,a)},`
which has one wire of dimension $`2^\ell` for every edge.”

In Lean the ends are the type `Nc.CaseI.End k` (an edge $`a < b` and one of its two sides), and
`Paper.fklTen K k ℓ` is the product over the edges of the unit tensors of size $`2^\ell` on the
two ends. `Paper.fklTen_val` says that its entries are the coefficients of `fkl`, and
`Paper.fklTen_price` that for a spectral point $`\phi` on any set of parties and any placement
`π` of the ends,
$`\phi(\pi\, T_{k,\ell}) = 2^{\ell \sum_e d_\phi(\pi(e,0),\, \pi(e,1))}`.
:::

The paper states the consequence of Lemma E.4 for the tensor (page 33): “For a circuit for
$`f_{k,\ell}` the lemma says that $`T_{k,\ell} = \sum_S t_S` over the balanced sets $`S`, where
$`t_S` is a sum of at most $`L` products of a tensor on the ends $`(a, b)` with $`a \in S` and a
tensor on the other ends, which is the form to which Lemma A.3 applies.”

:::lemma_ "prop_flat_lower_sum" (lean := "Paper.prop_flat_lower_sum, Paper.hubTen, Paper.hubTen_price, Paper.card_bal_le") (parent := "part-flat")
*An unnumbered step of the proofs of Propositions E.5 and E.10* (“The comparison”; page 34),
quoted: “By Lemmas E.4 and A.3, with $`\pm o_S` as the two further parties,
$`T_{k,\ell} = \sum_S t_S`, where $`t_S` is a restriction of the tensor
$$`T_S = \prod_{a \in S,\ b \neq a} \langle 2^\ell \rangle_{(a,b),\, o_S} \cdot \langle L \rangle_{o_S, -o_S} \cdot \prod_{a \notin S,\ b \neq a} \langle 2^\ell \rangle_{(a,b),\, -o_S}`
of Figure 7. Thus $`T_{k,\ell}` is covered by at most $`2^k` tensors $`T_S`”.

`Paper.hubTen K ℓ L π hub S` is $`T_S` for a placement `π` of the ends and a choice `hub S b` of
two parties for every set `S`; `Paper.hubTen_price` gives its value under a spectral point, with
exponent `Paper.hubCost`: $`\ell` times the sum of the distances from the ends to their hubs,
plus $`d_\phi(\text{hub}, \text{hub}') \log L`. `Paper.prop_flat_lower_sum` is the cover: if a
polynomial `P` in the variables of `fkl` has a circuit with `L` gates, then the tensor of the
coefficients of its part that is linear in each block, pushed forward along `π`, is covered by
the tensors $`T_S`, $`S` balanced. `Paper.card_bal_le` bounds the number of balanced sets by
$`2^k`. This is the step of the proof of Proposition E.5 that the main route uses (Appendix Q.3,
page 70, quoted above).
:::

# E.3. A first lower bound (not on the route to the main theorems)

:::proposition "prop_flat_lower" (lean := "Paper.prop_flat_lower, Paper.prop_flat_lower_printed, Paper.prop_flat_lower_lengths") (parent := "part-flat")
*Proposition E.5 of the paper* (a first lower bound for the network polynomial; page 33), quoted:
“In the flat case, for every $`k \geq 2` there is $`\ell_0` such that for $`\ell \geq \ell_0`
every circuit over $`\Bbbk` for $`f_{k,\ell}` has at least $`2^{\ell k^{3/2}/6}` gates.”

`Paper.prop_flat_lower` is this statement for the Lean polynomial `fkl`, and
`Paper.prop_flat_lower_printed` for the printed polynomial `fklExact` (see {bpref "fkl"}[] for
the two polynomials and the quotation of Appendix Q.3, page 68). Both hold for every field `K` in
`Type` with `Flat K`; the flat case is the hypothesis `hK`. Neither is used by the theorems of
`Solution` (Appendix Q.3, page 66, quoted above). The paper keeps the proposition because it
“shows the method” (page 31: “Section E.3 proves a first bound with an unspecified threshold on
$`\ell`, which shows the method, and Sections E.4 to E.6 make the threshold explicit”).
:::

:::proof "prop_flat_lower"
*The paper's proof* (page 34), summarised.

_The ends._ Let $`u_{ab} = (e_a - e_b)/\sqrt{2}` and put the end $`(a, b)` at
$`\tfrac12 u_{ab}`, so that the two ends of each of the $`N = \binom{k}{2}` edges have distance
$`1`.

_The hubs._ For a balanced $`S` let $`w_S = \sum_{a \in S,\, b \notin S} u_{ab}`, so that
$`\|w_S\|^2 = \tfrac12 k|S|(k - |S|) \geq k^3/9`. The hubs are
$`\pm o_S = \pm \eta\, w_S/\|w_S\|` with $`\eta = \tfrac{1}{6\sqrt{k}}`, “regarded as different
parties for different $`S`”. Since $`\|\tfrac12 u - o\| \leq \tfrac12 - u \cdot o + \|o\|^2` for
a unit vector $`u`, the distances from the ends to their hubs add up to at most
$`N - 2\eta\|w_S\| + k^2\eta^2 \leq N - \tfrac{k}{12}`. (Lean: `Paper.prop_flat_lower_lengths`.)

Lean writes $`Q = k|S|(k-|S|)` and sums the signed projections before estimating their gain.
The gain is nonnegative and its square is $`2\eta^2 Q`. Substituting $`Q \geq 2k^3/9` and
$`\eta^2 = 1/(36k)` gives a gain of at least $`k/9`. The quadratic cost is $`k^2\eta^2 = k/36`,
leaving a saving of $`k/12`.

A related argument in OpenAI's [VP and VNP are different, §2](https://github.com/openai/math/blob/e07100d36b22bcf8bb759f2f1abc7976ba472e47/preprints/VP-and-VNP-are-different-November-23-2026/build/Paper.tex#L261-L275)
moves one hub in the direction of an expander cut's resultant. That comparison prompted the
calculation by squares above. The complete graph and the two symmetric hubs here are the
construction in the original formalization.

_The spectral point._ Let $`\delta = \tfrac{1}{150k}`. “Because we are in the flat case, there
are a spectral point $`\phi` on the set of the ends and of all hubs and a factor $`c \geq 0`,
both depending on $`k` only, such that $`c\, d_\phi` differs from the Euclidean distances of the
positions by less than $`\delta`. We put $`\ell_0 = \lceil 100c \rceil + 1`.”

_The comparison._ From the cover by the $`T_S` and Definition A.1,
$`\phi(T_{k,\ell}) \leq 2^k \max_S \phi(T_S)`. Taking logarithms, using Lemma A.2 for every wire,
multiplying by $`c` and replacing each $`c\, d_\phi` by the Euclidean distance gives, for some
$`S`,
$$`\ell N(1 - \delta) \leq ck + \ell\Bigl(N - \frac{k}{12} + 2N\delta\Bigr) + (2\eta + \delta)\log L. \tag{E.1}`

_The conclusion._ $`ck \leq \ell k/100` by the choice of $`\ell_0`, and
$`3N\delta \leq k/100`; hence
$`\ell k(\tfrac{1}{12} - \tfrac{1}{50}) \leq (2\eta + \delta)\log L \leq 0.34\, k^{-1/2}\log L`,
which gives $`\log L \geq \ell k^{3/2}/6`.

The threshold $`\ell_0` depends on the scale $`c`, about which the flat hypothesis says nothing:
the term $`ck` in (E.1) is the $`k` bits that name a balanced set, multiplied by $`c`. Removing
this dependence is the purpose of Sections E.4 and E.5.
:::

:::theorem "thm_flat_simple" (lean := "Paper.thm_flat_simple") (parent := "part-flat")
*Theorem E.6 of the paper* (no circuits of polynomial size in the flat case; page 35), quoted:
“In the flat case, for every $`C` there is $`m_0` such that for $`m \geq m_0` no circuit over
$`\Bbbk` with at most $`m^C` gates computes $`\mathrm{PERM}_m`.”

In the Lean statement the standing hypothesis $`2 \neq 0` of Sections A to L is written out
(`h2`), and $`C` is a natural number (Appendix Q.3, page 68: “The numbers $`C`, $`a` and
$`\alpha` are natural numbers”). Like Proposition E.5, the theorem is not used by the theorems of
`Solution`; the paper uses it in its direct proof of Theorem L.2 (page 60: “The following direct proof uses
of Section E only the part that precedes Section E.4”).
:::

:::proof "thm_flat_simple" (uses := "thm_flat_rate")
*The paper's proof* (page 35), quoted: “We apply Proposition E.5 with a fixed $`k` for which
$`\sqrt{k} \geq 30(C+1)`. For large $`m` let $`\ell` be the largest integer with
$`3k^3\ell\, 2^{k\ell} \leq m`, so that $`m < 3k^3(\ell+1)2^{k(\ell+1)}`, and hence
$`\log m \leq 2k\ell` and $`\ell \geq \ell_0`. By Lemma E.3 a circuit with at most $`m^C` gates
for $`\mathrm{PERM}_m` then gives $`\ell k^{3/2}/6 \leq 3 + 2Ck\ell`, which is false by the
choice of $`k`.”

Lean deduces this conclusion from {bpref "thm_flat_rate"}[Theorem E.11].
The exponent of the resulting bound on circuit size eventually exceeds every fixed degree.
:::

# E.4. Sums with few terms

The paper (page 35): “In (E.1) the $`k` bits that name a balanced set are multiplied by the
unknown factor $`c`, which is the reason for the unspecified threshold $`\ell_0`. The following
lemma replaces the factor $`J` in the inequality for covers of Definition A.1 by
$`J^{g_\phi(P)}` when the $`J` terms arise by applying functionals outside a set $`P` of
parties. With $`P` the set of all ends, the term $`ck` becomes $`k` times the scaled exponent
$`c\, g_\phi(P)`, which Section E.5 bounds by about $`\sqrt{k}`.”

:::lemma_ "lem_few" (lean := "Paper.lem_few") (parent := "part-flat")
*Lemma E.7 of the paper* (sums with few terms; page 35), quoted: “Let $`P \subseteq V` be
nonempty, let $`t` be a tensor on $`P`, and let $`T_1, \ldots, T_J` be tensors on $`V` that have
the same index sets as $`t` at the parties of $`P`. Suppose that $`t = \sum_j f_j(T_j)`, where
each $`f_j` consists of one linear functional at every party outside $`P`, the trivial one where
there is no index, and $`f_j(T_j)` is the tensor on $`P` that results when these functionals are
applied to the indices of $`T_j` outside $`P`. Then
$`\phi(t) \leq J^{g_\phi(P)} \max_j \phi(T_j)` for every spectral point $`\phi` on $`V`.”

The Lean statement is more general, as the paper says. Appendix Q.3 (page 68): Lemmas E.7 and
N.3 are proved “whenever $`t` is covered by $`T_1, \ldots, T_J`, so that linear maps may also be
applied at the parties of $`P`.” In `Paper.lem_few`, `t` is a tensor on `V` whose index sets
outside the finite set `P` have at most one element (`ht`), the hypothesis is the cover
`Ten.SumRestr t T`, the exponent $`g_\phi(P)` is `hexp φ (Subtype.val : P → V)`, the maximum is
`Finset.sup'` over `Fin J`, and `[NeZero J]` says $`J \geq 1`. The printed hypothesis is the
special case in which the restriction of $`T_j` is the identity at the parties of $`P`. The Lean
form does not ask that $`P` be nonempty.

Compared with the defining inequality $`\phi(t) \leq J \max_j \phi(T_j)` of a spectral point,
the gain is the exponent $`g_\phi(P)`, which can be much smaller than $`1` after scaling: what is
paid for a sum of $`J` terms is a unit tensor of size $`J` on $`P`, not $`J` itself.
:::

:::proof "lem_few"
*The paper's proof* (page 35), quoted: “We expand a high power $`t^n` by words with $`n` letters
in $`[J]`, and group the words by their _type_ $`\tau = (\tau_1, \ldots, \tau_J)`, in which
$`\tau_j` is the number of places with the letter $`j`. We number the $`M_\tau \leq J^n` words of
type $`\tau`. The sum over these words is a restriction of
$`\langle M_\tau \rangle_P \cdot \prod_j T_j^{\tau_j}`, because every party of $`P` can order its
$`n` indices as the word whose number it holds prescribes, while the parties outside $`P` apply
$`\prod_j f_j^{\tau_j}`. There are at most $`(n+1)^J` types, so
$$`\phi(t)^n \leq (n+1)^J\, J^{n\, g_\phi(P)} \max_j \phi(T_j)^n.`
Taking $`n`th roots and letting $`n` tend to infinity proves the lemma.”
:::

# E.5. The exponent of the set of all ends

The paper (page 35): “The scaled exponent $`c\, g_\phi(P)` of two points is their distance, and
the next lemma allows us to pass to larger sets $`P` by taking midpoints. For a map $`\pi` of a
finite set $`I` into $`V` we write $`g_\phi(\pi) = g_\phi(\pi(I))` for the exponent of its
image.”

:::lemma_ "lem_convex" (lean := "Paper.lem_convex, Paper.hexp_convex, Paper.exists_mix_hexp, Paper.sq_dist_midpoint_le") (parent := "part-flat")
*Lemma E.8 of the paper* (the exponent is almost convex along midpoints; page 35), quoted: “Let
$`V \subseteq \mathbb{R}^n` and $`I \neq \emptyset` be finite. For every $`\varepsilon > 0`
there is $`\delta > 0` with the following property. Let $`\phi` be a spectral point on $`V` and
$`c \geq 0` with $`\bigl|c\, d_\phi(x, y) - \|x - y\|\bigr| < \delta` for all $`x, y \in V`, and
let $`a, b, m : I \to V` be maps such that every $`m(i)` is the midpoint of $`a(i)` and $`b(i)`.
Then
$$`c\, g_\phi(m) \leq \tfrac12\, c\, g_\phi(a) + \tfrac12\, c\, g_\phi(b) + \varepsilon.`”

In `Paper.lem_convex`, `V` is a finite set of points of `EuclideanSpace ℝ (Fin n)`, `I` is a
finite type, and $`g_\phi(\pi)` is `hexp φ π`. The Lean statement does not require $`I` to be
nonempty; otherwise it is the printed one. Note the order of the quantifiers: $`\delta` depends
on $`V`, $`I` and $`\varepsilon`, and not on $`\phi`, $`c` or the maps. The lemma does not use
the flat hypothesis.
:::

:::proof "lem_convex" (uses := "prop_extend")
*The paper's proof* (pages 35–36), summarised. Add a new party $`i'` for every $`i \in I` and let
$`Q` be the set of these. Let $`\pi_a, \pi_b : V \cup Q \to V` be the identity on $`V` and send
$`i'` to $`a(i)`, respectively to $`b(i)`. Proposition A.7, with the weights
$`\tfrac12, \tfrac12` and with $`C` the product of the wires of dimension $`2` on $`V` and of
$`\langle 2 \rangle_{m(I)}`, gives a spectral point $`\phi'` on $`V \cup Q` with
$`\phi'(t) \leq \phi(\pi_a t)^{1/2}\phi(\pi_b t)^{1/2}` and with the same values as $`\phi` on
the factors of $`C`, “because each can only decrease and the product is kept”. Thus
$`d_{\phi'} = d_\phi` on $`V`, $`g_{\phi'}(m(I)) = g_\phi(m)`, and
$$`g_{\phi'}(Q) \leq \tfrac12 g_\phi(a) + \tfrac12 g_\phi(b), \qquad d_{\phi'}(i', x) \leq \tfrac12 d_\phi(a(i), x) + \tfrac12 d_\phi(b(i), x) \quad (x \in V).`
Contracting $`\langle q \rangle_Q` with the wires $`\langle q \rangle_{i'\, m(i)}` gives
$`\langle q \rangle_{m(I)}`, hence
$`g_\phi(m) \leq g_{\phi'}(Q) + \sum_i d_{\phi'}(i', m(i))`. It remains to see that $`i'` is
close to $`m(i)` in the price $`c\, d_{\phi'}`. With $`\lambda` the distance of $`a(i)` and
$`b(i)`, the point $`i'` is an exact midpoint of them, and $`m(i)` has distance less than
$`\tfrac{\lambda}{2} + \tfrac32\delta` from both; Theorem C.1, with $`i'` as the midpoint,
$`D = \lambda/2` and $`z = m(i)`, bounds the squared distance of $`i'` and $`m(i)` by
$`\tfrac32\delta\lambda + (\tfrac32\delta)^2`.

The use of {bpref "thm_cn"}[] here is the point of contact between the flat case and the
curvature of prices: in a price, a point that is metrically a midpoint of two points is close to
every other near-midpoint. In Lean: `Paper.exists_mix_hexp` (the spectral point $`\phi'` with its
four properties), `Paper.sq_dist_midpoint_le` (the consequence of Theorem C.1), and
`Paper.hexp_convex` (the lemma for an arbitrary function `w` on a finite type in the role of the
Euclidean distances, under the two inequalities that say that $`m(i)` is a midpoint in `w`).
:::

:::proposition "prop_cube" (lean := "Paper.prop_cube, Paper.cubeAlpha_midpoint") (parent := "part-flat")
*Proposition E.9 of the paper* (facet centres of a cube; page 36), quoted: “In the flat case let
$`V \subseteq \mathbb{R}^k` be finite, let
$`P \subseteq V \cap \{\pm\tfrac12 e_1, \ldots, \pm\tfrac12 e_k\}` be nonempty, and let
$`\varepsilon > 0`. There are a spectral point $`\phi` on $`V` and $`c \geq 0` with
$`\bigl|c\, d_\phi(x, y) - \|x - y\|\bigr| < \varepsilon` for all $`x, y \in V` and
$`c\, g_\phi(P) \leq \sqrt{k} + \varepsilon`.”

The Lean statement is the printed one: `hK : Flat K`, finite sets `P ⊆ V` of points of
`EuclideanSpace ℝ (Fin k)`, and the hypothesis `hc` that every point of `P` is
$`\pm\tfrac12 e_j` for some $`j`.

For comparison (a remark of this blueprint): the tree bound of {bpref "lem_exponents"}[] gives
for the $`2k` facet centres only $`c\, g_\phi(P) \lesssim (2k-1)/\sqrt{2}`, the length of a
spanning tree with edges of length $`1/\sqrt{2}`. The proposition replaces a bound linear in
$`k` by $`\sqrt{k}`, the length of one main diagonal of the cube.
:::

:::proof "prop_cube"
*The paper's proof* (page 36), summarised. One passes from the two ends of a main diagonal of the
cube $`[-\tfrac12, \tfrac12]^k` to the set $`P` by taking midpoints $`k` times. Add to $`V` the
points $`\tfrac12 u` with $`u \in \{-1, 0, 1\}^k`. For a level $`0 \leq j \leq k` and signs
$`\chi = (\chi_{j+1}, \ldots, \chi_k)` let $`\alpha_\chi : P \to V` map a centre
$`\pm\tfrac12 e_i` to itself if $`i \leq j`, and to
$`\pm\tfrac12 \chi_i\, (0, \ldots, 0, \chi_{j+1}, \ldots, \chi_k)` if $`i > j`. At level $`k`
the map is the identity; at level $`0` its image is contained in the two ends
$`\pm\tfrac12\chi` of a main diagonal, “so that $`g_\phi(\alpha_\chi)` is at most the exponent of
one wire of length $`\sqrt{k}`”. For $`j \geq 1` the map $`\alpha_\chi` of level $`j` is the
pointwise midpoint of the two maps $`\alpha_{(1,\chi)}` and $`\alpha_{(-1,\chi)}` of level
$`j - 1` (Lean: `Paper.cubeAlpha_midpoint`). The flat hypothesis gives $`\phi` and $`c` with
$`c\, d_\phi` within $`\varepsilon/(k+1)` of the Euclidean metric, and so close that Lemma E.8
applies to each of these finitely many triples of maps with $`\varepsilon/(k+1)`; induction on
$`j` gives $`c\, g_\phi(\alpha_\chi) \leq \sqrt{k} + (j+1)\varepsilon/(k+1)`.

The flat hypothesis is used once, for the enlarged configuration; this is why the proposition
needs all finite Euclidean configurations and not only the one of the ends and hubs.
:::

# E.6. The lower bound for ℓ ≥ 100√k

:::proposition "prop_flat_rate" (lean := "Paper.prop_flat_rate, Paper.prop_flat_rate_printed") (parent := "part-flat")
*Proposition E.10 of the paper* (lower bound for the network polynomial; page 36), quoted: “In
the flat case, for $`k \geq 2` and $`\ell \geq 100\sqrt{k}` every circuit over $`\Bbbk` for
$`f_{k,\ell}` has at least $`2^{\ell k^{3/2}/16}` gates.”

`Paper.prop_flat_rate` is this statement for the Lean polynomial `fkl`, and
`Paper.prop_flat_rate_printed` for the printed polynomial `fklExact` (Appendix Q.3, page 68,
quoted under {bpref "fkl"}[]). The field is any field `K` in `Type` with `Flat K`; no condition
on the characteristic is needed. The bound is `(2 : ℝ) ^ (ℓ * k ^ (3/2) / 16) ≤ s` for every `s`
with `Computes (fkl K k ℓ) s`.
:::

:::proof "prop_flat_rate" (uses := "prop_flat_rate_steps")
*The paper's proof* (pages 36–37), summarised; “The steps and the notation are those of the proof
of Proposition E.5.”

_The ends._ For $`a < b` put the end $`(a, b)` at $`\tfrac12 e_a` and the end $`(b, a)` at
$`-\tfrac12 e_a`. “The ends thus occupy facet centres of the cube $`[-\tfrac12, \tfrac12]^k`, the
two ends of an edge have distance $`1`, and all positions add up to $`0`.”

_The hubs._ For a balanced $`S` let $`w_S` be twice the sum of the positions of the ends
$`(a, b)` with $`a \in S`. If $`c_a` is the number of $`b > a` such that exactly one of $`a, b`
lies in $`S`, then $`w_S = \sum_a \pm c_a e_a` and
$`\sum_a c_a = |S|(k - |S|) \geq 2k^2/9`, so $`\|w_S\| \geq \tfrac29 k^{3/2}` by the
Cauchy–Schwarz inequality. The hubs are $`\pm o_S = \pm\eta\, w_S/\|w_S\|` with
$`\eta = \tfrac{2}{9\sqrt{k}}`, and the distances from the ends to their hubs add up to at most
$$`N - 2\eta\|w_S\| + k^2\eta^2 \leq N - \tfrac{4}{81}k.`

_The spectral point._ Let $`\delta = 10^{-3}/k`, and let $`\phi` and $`c` be as in Proposition
E.9 for the set $`V` of the positions of all ends and hubs and the set $`P` of the positions of
the ends, with $`\delta` as $`\varepsilon`, “pulled back to the ends and hubs regarded as
different parties”. Then $`c\, d_\phi` differs from the Euclidean distance of the positions by
less than $`\delta`, and $`c\, g_\phi(\mathcal{E}) \leq \sqrt{k} + \delta` for the set
$`\mathcal{E}` of all ends.

_The comparison._ $`T_{k,\ell} = \sum_S t_S` over the at most $`2^k` balanced sets, and $`t_S`
is a restriction of $`T_S`. “By the proof of Lemma A.3 this restriction applies a functional at
$`o_S` and one at $`-o_S` and nothing at the ends, and $`T_S` has no index at the hubs of the
other sets. Lemma E.7, with $`\mathcal{E}` as the set $`P` of the lemma and $`J \leq 2^k`,
therefore gives $`\phi(T_{k,\ell}) \leq 2^{k\, g_\phi(\mathcal{E})} \max_S \phi(T_S)`, and as
before we find for some $`S`
$$`\ell N(1 - \delta) \leq k(\sqrt{k} + \delta) + \ell\Bigl(N - \frac{4}{81}k + \delta k^2\Bigr) + (2\eta + \delta)\log L. \tag{E.2}`”

_The conclusion._ “Here $`k(\sqrt{k} + \delta) \leq 1.5\, k^{3/2} \leq 0.015\, \ell k`, because
$`\ell \geq 100\sqrt{k}`, and the two terms with $`\delta` add up to at most
$`\tfrac32\delta k^2\ell = 0.0015\, \ell k`. Hence $`(2\eta + \delta)\log L \geq \ell k/31`, and
since $`2\eta + \delta \leq 0.446\, k^{-1/2}`, it follows that
$`\log L \geq \ell k^{3/2}/14`, which implies the claim.”

The Lean proof follows these steps; they are the next node. Because the Lean form of Lemma E.7
takes a cover as its hypothesis, the sentence “By the proof of Lemma A.3 this restriction applies
a functional at $`o_S` … and nothing at the ends” is not needed there: the cover of
{bpref "prop_flat_lower_sum"}[] is passed to `Paper.lem_few` as it is.
:::

:::lemma_ "prop_flat_rate_steps" (lean := "Paper.prop_flat_rate_lengths, Paper.SomeSetPays, Paper.someSetPays_of_few, Paper.rate_of_someSetPays, Paper.rate_numbers14, Paper.rate_pow") (parent := "part-flat")
*Unnumbered steps of the proof of Proposition E.10* (pages 36–37).

- `Paper.prop_flat_rate_lengths` is “The hubs”: for a balanced set there is a point $`x` with
  $`\|x\| = \tfrac{2}{9\sqrt{k}}` such that the distances from the ends to $`\pm x` add up to at
  most $`\tfrac{k(k-1)}{2} - \tfrac{4}{81}k`.
- `Paper.SomeSetPays φ ℓ s` is the inequality of step 3 of the outline above, for a spectral
  point on the ends and hubs: for some balanced `A`,
  $`\ell \sum_e d_\phi(e) \leq k\, g_\phi(\mathcal{E}) + \mathrm{hubCost}(A)`.
  `Paper.someSetPays_of_few` derives it from the conclusion of Lemma E.7.
- `Paper.rate_of_someSetPays` is “The ends”, “The hubs”, “The spectral point” and “The
  conclusion” together: in the flat case, if `SomeSetPays φ ℓ s` holds for every spectral point
  $`\phi` on the ends and hubs and $`\ell \geq 100\sqrt{k}`, then
  $`\ell k\sqrt{k}/14 \leq \log s`. It calls `Paper.prop_cube` with
  $`\varepsilon = \tfrac{1}{1000k}`.
- `Paper.rate_numbers14` is the arithmetic of “The conclusion”, with the constant $`14`, and
  `Paper.rate_pow` passes from $`\ell k\sqrt{k}/14 \leq \log s` to
  $`2^{\ell k^{3/2}/16} \leq s`.

The hypothesis of `Paper.rate_of_someSetPays` does not mention a circuit. This is what allows the
same theorem to serve exact and approximating circuits (Section N.2 below).
:::

:::lemma_ "rate_of_projection" (lean := "Paper.rate_of_projection") (parent := "part-flat")
*The calculation of the proof of Theorem E.11* (page 37; the proof is quoted under
{bpref "thm_flat_rate"}[]), as a Lean theorem of its own. `Paper.rate_of_projection κ` is stated
for an arbitrary relation $`P(m, s)` in place of “a circuit with $`s` gates for the $`m`th
polynomial” and an arbitrary factor $`\kappa` in place of $`3`: if $`P(m, s)` implies
$`2^{\ell k^{3/2}/16} \leq 5s` whenever $`k \geq 2`, $`\ell \geq 100\sqrt{k}` and
$`\kappa k^3 \ell\, 2^{k\ell} \leq m`, then for all large $`m`, $`P(m, s)` implies
$`2^{(\log m)^{4/3}/1600^2} < s`. The threshold $`m_0` depends on $`\kappa` only. The theorem
mentions neither a circuit nor a field; Theorem E.11, its general form and the form for
approximating circuits are its instances.
:::

:::theorem "thm_flat_rate" (lean := "Paper.thm_flat_rate") (parent := "part-flat")
*Theorem E.11 of the paper* (lower bound for the permanent in the flat case; page 37), quoted:
“In the flat case there is $`m_0` such that for $`m \geq m_0` every circuit over $`\Bbbk` for
$`\mathrm{PERM}_m` has more than $`2^{(\log m)^{4/3}/1600^2}` gates.”

In `Paper.thm_flat_rate` the hypotheses are `Flat K` and `(2 : K) ≠ 0` (the standing hypothesis,
written out), and the bound is `(2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s`, in which
the exponent is $`(\log_2 m)^{4/3}/1600^2`. The paper records no difference in the statement.
:::

:::proof "thm_flat_rate"
*The paper's proof* (page 37), quoted: “We apply Proposition E.10 to a square $`k = r^2`. Let
$`r` be the largest integer with $`200r^3 \leq \lfloor \log m \rfloor`, and let $`k = r^2` and
$`\ell = 100r`. For large $`m` we have $`r \geq 2`,
$`3k^3\ell\, 2^{k\ell} \leq 2^{200r^3} \leq m` and $`\log m \leq 1600r^3`. By Lemma E.3 and
Proposition E.10, a circuit with $`L` gates for $`\mathrm{PERM}_m` gives
$$`\log(5L) \geq \frac{\ell k^{3/2}}{16} = \frac{25}{4} r^4.`
Hence $`\log L > r^4 \geq (\log m/1600)^{4/3} \geq (\log m)^{4/3}/1600^2`.”

The constant $`1/1600^2` of the main theorem is this one. In Lean the calculation is
{bpref "rate_of_projection"}[]. The general family theorem {bpref "flat_rate_complete"}[] uses
this calculation and {bpref "prop_flat_rate"}[Proposition E.10]. Taking the permanent with
completeness factor three gives `Paper.thm_flat_rate`.
:::

:::theorem "flat_rate_complete" (lean := "Paper.flat_rate_complete") (parent := "part-flat")
*A sentence of the paper after Proposition M.2* (page 61), quoted: “Corollary E.2, Lemma E.3 and
with it Theorem E.11 hold for every such family, with $`\theta` in place of $`3`.”

This Lean theorem has no number in the paper. For every factor $`\kappa` there is $`m_0` such
that for every field `K` in `Type` with `Flat K` and every family $`(G_M)` that is complete for
grid sums with factor $`\kappa` ({bpref "GridComplete"}[]), every circuit for $`G_m` with
$`m \geq m_0` has more than $`2^{(\log m)^{4/3}/1600^2}` gates. Three features differ from
Theorem E.11: the family is arbitrary; no hypothesis $`2 \neq 0` appears (it is needed only to
show that $`\mathrm{PERM}` is complete for grid sums); and $`m_0` is chosen before the field, so
it depends on $`\kappa` alone. Appendix Q.3 (page 70) says of the route: “Lemma K.3, Theorem M.3
and Theorem N.5 use the general forms for families that are complete for grid sums, of which
Corollary E.2 and the statements about the permanent are instances.” The shared quantitative proof applies the approximate form
{bpref "flat_rate_approx_complete"}[] to both families, with factors 40 for HC and 3 for the
permanent when two is nonzero. Exact circuits enter that result as constant-series circuits
({ref "chapter-assembly"}[All fields and approximate computation]). The proof of the present
theorem is that of Theorem E.11 with {bpref "fkl_complete"}[] in the place of Lemma E.3; both are
instances of {bpref "rate_of_projection"}[].
:::

# N.2. Approximating circuits in the flat case

The flat case extends to circuits over $`\Bbbk((\varepsilon))` that approximate the polynomial
in the sense of Definition N.1 of the paper (Definition 1.3; see `Statement.Approximates` in
{ref "chapter-statement"}[The statement to trust]). The paper (page 62): “The flat case needs
Lemma E.7 for functionals that are Laurent polynomials.”

:::lemma_ "lem_few_approx" (lean := "Paper.lem_few_approx") (parent := "part-flat")
*Lemma N.3 of the paper* (sums with few terms, approximate version; page 62), quoted: “Lemma E.7
remains true if the functionals of which the $`f_j` consist have coefficients in
$`\Bbbk[\varepsilon, \varepsilon^{-1}]`, no negative power of $`\varepsilon` occurs in
$`\sum_j f_j(T_j)`, and $`t` is the coefficient of $`\varepsilon^0` in this sum.”

The Lean statement is more general in the same way as that of Lemma E.7 (Appendix Q.3, page 68,
quoted under {bpref "lem_few"}[]): the local maps `f j p`, with entries in
`LaurentPolynomial K`, act at every party, also at those of `P`. The hypothesis `h` says that for
every index `x` of `t` and every integer $`i \leq 0`, the coefficient of $`\varepsilon^i` in
$`\sum_j \sum_y \bigl(\prod_p f_{j,p}(x_p, y_p)\bigr)\, T_j(y)` is $`t(x)` for $`i = 0` and
$`0` for $`i < 0`. The tensors $`t` and $`T_j` have entries in `K`, and the conclusion is that of
`Paper.lem_few`.
:::

:::proof "lem_few_approx"
*The paper's proof* (page 62), quoted: “We follow the proof of Lemma E.7, and let all exponents
of $`\varepsilon` in the functionals lie in $`[-\Delta, \Delta]`. As no negative powers occur,
$`t^n` is the coefficient of $`\varepsilon^0` in the $`n`th power of the sum, which is again a
sum over the types. For each type the functional at a party outside $`P` is a sum of at most
$`2n\Delta + 1` functionals over $`\Bbbk`, one for each power of $`\varepsilon`, so that this
coefficient is covered by $`(2n\Delta + 1)^{|V|}` copies of the same tensor as before, a
subexponential number.”
:::

:::theorem "flat_rate_approx_complete" (lean := "Paper.flat_rate_approximating, Paper.flat_rate_approx_complete, Paper.exists_cut_off, Paper.hubs_series") (parent := "part-flat")
*A paragraph of the paper after Lemma N.3* (page 62), quoted: “It follows that Proposition E.10,
and with it Theorem E.11, holds for approximating circuits. Indeed, we apply Lemma E.4, which
holds over every commutative ring, over $`\Bbbk((\varepsilon))`, cut the functionals off at a
power of $`\varepsilon` that is high against their negative exponents times the number of
parties, and use Lemma N.3 in place of Lemma E.7.”

These Lean theorems have no number in the paper.

- `Paper.flat_rate_approximating` is Proposition E.10 for approximating circuits, with a
  different explicit number. Appendix Q.3 (page 68): “The flat bound for approximating circuits
  has 14 where Proposition E.10 has 16.” Its conclusion is
  $`\ell k\sqrt{k}/14 \leq \log s` for every `s` with `Approximates (fkl K k ℓ) s`, under
  `Flat K`, $`k \geq 2` and $`\ell \geq 100\sqrt{k}`. This is the intermediate inequality of the
  printed proof of Proposition E.10 and implies the bound $`2^{\ell k^{3/2}/16} \leq s` of that
  proposition by `Paper.rate_pow`; no theorem of the development states Proposition E.10 for
  approximating circuits in the form with $`16`.
- `Paper.flat_rate_approx_complete` is Theorem E.11 for approximating circuits and for every
  family that is complete for grid sums, with the same bound $`2^{(\log m)^{4/3}/1600^2} < s`
  and the same uniformity as {bpref "flat_rate_complete"}[]. It is the flat half of the proof of
  Theorem N.5 ({ref "chapter-assembly"}[All fields and approximate computation]).
- `Paper.hubs_series` is the hub decomposition for a circuit over the Laurent series (Lemma E.4
  over the ring `LaurentSeries K`, and Lemma A.3), and `Paper.exists_cut_off` is the cut: for
  finitely many Laurent series there are Laurent polynomials such that every product of $`|V|`
  of them, one per party, has the same coefficients of $`\varepsilon^i` for all $`i \leq 0`.

In the proof of `Paper.flat_rate_approx_complete` the approximating circuit for $`G_m` is turned
into one for $`f_{k,\ell}` with five times as many gates by substituting affine polynomials over
`K`, which preserves the property of approximating (the substitution acts on the variables and
not on $`\varepsilon`).
:::

# What the rest of the proof takes from this chapter

- {ref "chapter-assembly"}[All fields and approximate computation] takes, as the flat halves of
  its theorems, {bpref "flat_rate_complete"}[] for both families in Theorem M.3 and
  {bpref "flat_rate_approx_complete"}[] for Theorem N.5. Theorems L.1 and L.2 inherit their flat
  bound from Theorem M.3. The explicit constant $`1/1600^2` of this chapter
  becomes the absolute constant of the main theorem, because the bound of the contracting case
  exceeds it for large $`m`.
- The contracting case does not use this chapter, with one exception named by the paper's map of
  the proof (Table 1, page 17): Section K uses Section E, namely the reduction of
  {ref "chapter-completeness"}[Completeness gadgets].
