/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.Curvature
import Paper.Alternative

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "The two cases" =>

%%%
tag := "chapter-dichotomy"
file := "two-cases"
htmlSplit := .never
number := false
%%%

The proof of the main theorem is a proof by cases, and this chapter states the cases and proves
that they are exhaustive. Two hypotheses on the field $`\Bbbk` are formulated, a _flat_ one and a
_contracting_ one; each is a statement about the set of all prices over $`\Bbbk`, and neither
mentions circuits or polynomials. Theorem D.2 says that at least one of them holds. The lower
bound is then proved twice, by two unrelated arguments: under the flat hypothesis in
{ref "chapter-flat"}[The flat case], and under the contracting hypothesis in the four chapters of
the contracting case. The chapter follows Appendix D of the paper (pages 29–31) of
{repoFile "vp-vnp/paper.pdf"}[`paper.pdf`].

What is and is not known about the two cases, in the paper's words:

- Section 2.1 (page 6): “We do not know which of the two hypotheses holds, even over
  $`\mathbb{R}`, nor do we show that the two are mutually exclusive.”
- Section D.3 (page 31): “We do not show that the two cases exclude each other. Outside the
  contracting case not every price is Euclidean, because for $`\mu \geq 3` the price
  $`\sqrt{\mathrm{rk}(a - a')}` of the proof above is not. Theorem D.2 is not effective: we do not
  know which case occurs, and the contracting case comes without a value for $`\mu`.”
- Remarks after Corollary L.3 (page 60): “The constant $`m_0` in our theorems is not effective
  … To make $`m_0` effective along the lines of this proof we would have to decide which case
  holds, and in the contracting case we would also need values for the numbers $`\mu` and $`s` of
  Definition D.1, which the proof of Theorem D.2 does not provide.”

So the main theorem is established without determining, for any field, which of the two arguments
is the one that applies. The remarks of Section D.3 are not formalized: Appendix Q.3 (page 70)
lists “the remarks that follow the proof of Theorem D.2” under “Not in Lean”.

The logical form of the theorem, as the Lean proof makes plain: `Paper.thm_alt` is proved by a
case distinction on the proposition `Contracting K` (the law of excluded middle), and its
mathematical content is the implication _if the contracting hypothesis fails, then the flat
hypothesis holds_ (`Paper.thm_alt_euclidean` below). The proof of that implication passes to a
limit of prices by compactness and gives no bound.

# D.1. The two hypotheses

The paper (page 29): “Let $`\mathrm{Mat}_\mu(\mathbb{F}_2)` be the additive group of the
$`\mu \times \mu` matrices over the field with two elements. For a price on it and
$`r \leq \mu` let $`D(r) \geq 0` be the root mean square distance of two matrices whose
difference has rank $`r`, that is, let $`D(r)^2` be the mean of $`|a, a+W|^2` over all matrices
$`a` and all matrices $`W` of rank $`r`. We call matrices $`W_1, W_2, \ldots` _transversal_ if
their column spaces are linearly independent and their row spaces are as well. The rank of their
sum is then the sum of their ranks.”

The matrices are only the points on which prices are considered. Section 2.1 (page 5): “The field
enters only through the tensors, which have entries in $`\Bbbk`, and the restrictions, which use
$`\Bbbk`-linear maps. The set $`\mathrm{Mat}_\mu(\mathbb{F}_2)` only supplies the parties and
their addition; its $`\mathbb{F}_2` is not the field $`\Bbbk`.”

:::definition "distAtRank" (lean := "Paper.meanSq, Paper.distAtRank, Paper.def_transversal") (parent := "part-common")
*Definitions of Section D.1 of the paper* ($`D(r)` and transversal matrices; page 29,
unnumbered), quoted above.

In Lean, $`\mathrm{Mat}_\mu(\mathbb{F}_2)` is `Nc.Flag.Mt μ`, the type of matrices indexed by
`Fin μ` over `ZMod 2`. For a function `w` on pairs of matrices, `Paper.meanSq w r` is $`D(r)^2`:
the sum of $`w(a, a+W)^2` over all $`a` and all $`W` of rank $`r`, divided by the number of such
pairs; `Paper.distAtRank w r` is its square root. `Paper.def_transversal` unfolds the definition
`Nc.Flag.Transversal` of a transversal family: the spans of the columns are independent
subspaces, and so are the spans of the rows.
:::

:::definition "def_cases" (lean := "Paper.Flat, Paper.Contracting, Paper.def_cases") (parent := "part-common")
*Definition D.1 of the paper* (page 30), quoted: “We consider two hypotheses on the field
$`\Bbbk`, on which the notion of a price depends.

*Flat hypothesis:* All finite subsets of all Euclidean spaces, with their metrics, are prices.

*Contracting hypothesis:* There are an integer $`\mu \geq 2` and a real number $`s` with
$`1 \leq s` and $`s^2 < \mu` such that $`D(\mu) \leq s\, D(1)` for all prices on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)`.

We say that we are in the _flat case_ if the flat hypothesis holds, and in the _contracting case_
if the contracting hypothesis holds.”

`Paper.Contracting K` is the printed contracting hypothesis word for word, with `distAtRank`.
The definition of `Paper.Flat K` quantifies over every $`k`, every finite type `V` and every
map `E` from `V` to $`\mathbb{R}^k` with the Euclidean metric (`EuclideanSpace ℝ (Fin k)`). It requires that the
function $`(a, b) \mapsto \|E(a) - E(b)\|` is a price on `V`. `Paper.def_cases` proves that this
is equivalent to the printed form, with finite subsets `S` of $`\mathbb{R}^n` for all $`n`, and
restates the contracting hypothesis with the means written out. “Euclidean spaces” are thus the
spaces $`\mathbb{R}^n`, $`n` finite. The paper records no difference for Definition D.1.

*The form in the overview.* Definition 2.1 of the paper (pages 4–5) states the hypotheses for
spectral points instead of prices. Its contracting hypothesis asks, for every spectral point
$`\phi` on $`V = \mathrm{Mat}_\mu(\mathbb{F}_2)`, that
$$`\mathbb{E}_{a,\,W :\, \mathrm{rk}\,W = \mu}\; d_\phi(a, a+W)^2 \;\leq\; s^2\; \mathbb{E}_{a,\,W :\, \mathrm{rk}\,W = 1}\; d_\phi(a, a+W)^2,`
and its flat hypothesis reads: “For every finite subset $`V` of a Euclidean space and every
$`\varepsilon > 0` there are a spectral point $`\phi` on $`V` and a real number $`c \geq 0` such
that $`|c\, d_\phi(u, v) - \|u - v\|| \leq \varepsilon` for all $`u, v \in V`.” The paper relates
the two forms (page 5): “The Lean definition states both hypotheses for prices: the contracting
one as $`D(\mu) \leq s\, D(1)` for all prices on $`\mathrm{Mat}_\mu(\mathbb{F}_2)`, which is the
same because the inequality survives scaling and limits, and the flat one as the statement that
all finite subsets of Euclidean spaces, with their metrics, are prices.” For the flat
hypothesis the two forms are related by the first clause of `Paper.def_price`
({bpref "def_price"}[]), applied to the Euclidean metric of a finite set of points. The equivalence of the contracting forms is not stated by a Lean theorem that
this blueprint could find; the development uses the form for prices throughout.
:::

What the contracting hypothesis says geometrically. Every price on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` satisfies $`D(r) \leq \sqrt{r}\, D(1)` (Step 1 below). The paper
(page 30): “Thus the contracting hypothesis says that for some $`\mu` the bound
$`D(\mu) \leq \sqrt{\mu}\, D(1)` can be improved by a constant factor.” And (page 5): “So the
contracting hypothesis says that, for some $`\mu`, every price on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` falls short of a Euclidean rectangle by a fixed factor, and the
flat hypothesis says that prices can be Euclidean.” The flat hypothesis is a statement of
richness: over $`\Bbbk` there are spectral points whose pseudometrics approximate, up to scale,
any prescribed finite Euclidean configuration. The contracting hypothesis is a uniform
inequality, valid for all spectral points on one fixed finite set of parties.

The paper states the theorem at this point, at the end of Section D.1.

:::theorem "thm_alt" (lean := "Paper.thm_alt") (parent := "part-common")
*Theorem D.2 of the paper* (the two cases; page 30), quoted: “At least one of the two hypotheses
of Definition D.1 holds, that is, one of the two cases occurs.”

The same statement is Theorem 2.2 of the paper (page 6): “Over every field $`\Bbbk` at least one
of the two hypotheses of Definition 2.1 holds, that is, one of the two cases occurs.” The Lean
statement is `Flat K ∨ Contracting K` for every field `K` in `Type`, in the forms of Definition
D.1. It does not say which disjunct holds, it does not say that only one holds, and its proof
provides no way to decide.
:::

# D.2. Proof of Theorem D.2

:::proof "thm_alt" (uses := "thm_alt_euclidean")
*The paper's outline of the proof* (page 30), quoted: “We assume that the contracting hypothesis
fails and derive the flat one. Steps 1 to 3 produce a price on $`\mathrm{Mat}_\mu(\mathbb{F}_2)`
with equality in Lemma C.4(b) for all quadrilaterals as in Figure 6, Steps 4 to 7 deduce that its
squared distances are the ranks of the differences, and Step 8 fills a Euclidean cube by Lemma
C.4(f).”

The proof begins (page 30): “Suppose that the contracting hypothesis fails, and fix
$`\mu \geq 3`. By Proposition C.3 every price is pulled back from the metric of a CAT(0) space,
so that Lemma C.4 applies to the points of a price.” The eight steps are the following nodes. In
Lean the final assembly applies the implication with $`\mu = k + 3` to obtain the flat hypothesis
in dimension $`k`.
:::

:::lemma_ "thm_alt_subadditive" (lean := "Paper.thm_alt_subadditive, Paper.thm_alt_quadrangle") (parent := "part-common")
*Step 1 of the proof of Theorem D.2* (subadditivity; page 30), quoted: “Let $`(W, W')` be a
uniformly random transversal pair of matrices of ranks $`i` and $`j`, where $`i + j \leq \mu`,
and let $`a` be uniformly random and independent of it. Then $`W`, $`W'` and $`W + W'` are
uniformly distributed among the matrices of ranks $`i`, $`j` and $`i + j`. Both diagonals of the
quadrilateral $`a,\ a + W,\ a + W + W',\ a + W'` have the difference $`W + W'`, so the mean of
the second inequality of Lemma C.4(b) over these quadrilaterals is
$`D(i+j)^2 \leq D(i)^2 + D(j)^2`.”

That both diagonals have the same difference uses $`2 = 0` in $`\mathbb{F}_2`:
$`(a + W) - (a + W') = W + W'`. `Paper.thm_alt_quadrangle` is Lemma C.4(b), second statement
with its equality case, for four points of an arbitrary price (through {bpref "prop_space"}[]).
`Paper.thm_alt_subadditive` is the displayed inequality, for every price `w` and
$`i + j \leq \mu`. In particular $`D(r)^2 \leq r\, D(1)^2`.
:::

:::lemma_ "thm_alt_extremal" (lean := "Paper.thm_alt_extremal, Paper.Extremal, Paper.thm_alt_bounded, Paper.thm_alt_ranks") (parent := "part-common")
*Step 2 of the proof of Theorem D.2* (a price with equality; page 30), quoted: “As the
contracting hypothesis fails, for every $`s` with $`1 \leq s < \sqrt{\mu}` there is a price on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` with $`D(\mu) > s\, D(1)`. Every distance in a price on
$`\mathrm{Mat}_\mu(\mathbb{F}_2)` is at most a constant, which depends on $`\mu` only, times
$`D(1)`, so we may scale these prices to $`D(1) = 1` and, by compactness, pass to a limit for
$`s \to \sqrt{\mu}`, which is a price with $`D(1) = 1` and $`D(\mu)^2 \geq \mu`. By Step 1 it has
$`D(r)^2 \leq r` and $`\mu \leq D(\mu)^2 \leq D(r)^2 + D(\mu - r)^2 \leq \mu`, and therefore
$`D(r)^2 = r` for all $`r \leq \mu`.”

`Paper.Extremal K w` is the structure “`w` is a price with $`D(1)^2 = 1` and $`D(\mu)^2 = \mu`”.
`Paper.thm_alt_bounded` is the bound of all distances by a constant times $`D(1)`;
`Paper.thm_alt_extremal` produces an extremal price from `¬ Contracting K`, for $`\mu \geq 2`;
`Paper.thm_alt_ranks` is $`D(r)^2 = r`. This step is the only place where the failure of the
contracting hypothesis is used. The extremal price is a limit point supplied by the compactness
of bounded sets of prices ({bpref "def_price_facts"}[]); no construction of it is given.
:::

:::proof "thm_alt_extremal" (uses := "def_price_facts")
For a pair with difference of rank $`r`, its squared distance is one nonnegative summand in the sum
that defines $`D(r)^2`. The number of terms is at most the square of the number of matrices, and
Step 1 gives $`D(r)^2 \leq rD(1)^2`. This supplies the uniform bound. For every $`n` the failure of the contracting
hypothesis with $`s^2 = \mu - 1/(n+1)` gives a price, scaled to $`D(1)^2 = 1` and bounded by the
constant of `Paper.thm_alt_bounded`, with $`D(\mu)^2 \geq \mu - 1/(n+1)`; a limit point of these
prices exists by compactness and is extremal by Step 1.
:::

:::lemma_ "thm_alt_equality" (lean := "Paper.thm_alt_equality, Paper.thm_alt_opposite, Paper.thm_alt_diagonal") (parent := "part-common")
*Step 3 of the proof of Theorem D.2* (equality for all quadrilaterals; page 30), quoted: “In this
price the inequality of Step 1, a mean of finitely many inequalities, is an equality, so for
every $`a` and every transversal pair $`(W, W')` the quadrilateral of Step 1 has equality in the
second statement of Lemma C.4(b). Put $`n_a(W) = |a, a+W|^2`. For transversal $`W, W'` opposite
sides are equal by the lemma, and the equality then expresses one diagonal by the other and the
sides, that is,
$$`n_{a+W'}(W) = n_a(W), \tag{D.1}`
$$`|a + W,\ a + W'|^2 = 2n_a(W) + 2n_a(W') - n_a(W + W'). \tag{D.2}`”

The three Lean theorems are the equality, (D.1) and (D.2), for an extremal price; $`n_a(W)` is
`Nc.Flag.nn w a W`.
:::

:::lemma_ "thm_alt_additive" (lean := "Paper.thm_alt_additive") (parent := "part-common")
*Step 4 of the proof of Theorem D.2* (additivity; page 30), quoted: “Let
$`B_a(W, W') = \tfrac12\bigl(n_a(W + W') - n_a(W) - n_a(W')\bigr)`, which is symmetric in $`W`
and $`W'`. We claim that for transversal $`W_1, W_2, W_3`
$$`B_a(W_1, W_2 + W_3) = B_a(W_1, W_2) + B_a(W_1, W_3). \tag{D.3}`”

The paper's argument: apply (D.2) at the matrix $`a + W_2` to the pair $`(W_1, W_2 + W_3)` and
express all terms by $`n_a`, using (D.1) and (D.2) at $`a`; this gives
$`n_a(W_1 + W_2 + W_3) - \sum_{i<j} n_a(W_i + W_j) + \sum_i n_a(W_i) = 0`. In Lean $`B_a` is
`Nc.Flag.BB w a`.
:::

:::lemma_ "thm_alt_lambda" (lean := "Paper.thm_alt_lambda, Paper.thm_alt_exchange, Paper.thm_alt_connect, Paper.thm_alt_third") (parent := "part-common")
*Step 5 of the proof of Theorem D.2* ($`B_a` is constant on pairs of rank one; page 31),
summarised. For column vectors over $`\mathbb{F}_2`,
$`u_1 x_1^{\mathsf T} + u_2 x_2^{\mathsf T} = u_1 (x_1 + x_2)^{\mathsf T} + (u_1 + u_2) x_2^{\mathsf T}`.
If $`W, u_1 x_1^{\mathsf T}, u_2 x_2^{\mathsf T}` are transversal, so are $`W` and the two
matrices on the right, and (D.3) gives, for $`\chi(u, x) = B_a(W, u x^{\mathsf T})`,
$$`\chi(u_1, x_1) - \chi(u_1, x_1 + x_2) = \chi(u_1 + u_2, x_2) - \chi(u_2, x_2).`
The right-hand side does not depend on $`x_1`, and the left-hand side changes sign when $`x_1`
becomes $`x_1 + x_2`; so both sides vanish. Thus $`x` may be changed by any vector outside its
span with the row space of $`W`, and likewise $`u`. The paper concludes: “As $`\mu \geq 3`, for
$`W` of rank one such moves connect all vectors outside its row space, respectively column space,
and any two matrices of rank one are both transversal to a third. As $`B_a` is symmetric, it
takes one value $`\lambda(a)` on all transversal pairs of matrices of rank one.”

In Lean: `Paper.thm_alt_exchange` (both sides vanish, for any function additive in the sense of
(D.3)), `Paper.thm_alt_connect` (the function has one value on the matrices of rank one
transversal to $`W`, if $`\mathrm{rk}\, W + 2 \leq \mu`), `Paper.thm_alt_third` (the third
matrix; this is where $`\mu \geq 3` enters), and `Paper.thm_alt_lambda` (the conclusion).
:::

:::lemma_ "thm_alt_orthogonal" (lean := "Paper.thm_alt_orthogonal, Paper.thm_alt_reflect") (parent := "part-common")
*Step 6 of the proof of Theorem D.2* ($`\lambda = 0`; page 31), quoted: “For transversal
$`V, W'` we have $`n_{a+V}(V) = n_a(V)`, we have $`n_{a+V}(W') = n_a(W')` by (D.1), and
$`n_{a+V}(V + W') = |a + V,\ a + W'|^2` is given by (D.2), so that
$`B_{a+V}(V, W') = -B_a(V, W')`. If $`V` and $`W'` have rank one, this says that
$`\lambda(a + V) = -\lambda(a)`. If $`V` has rank two and $`W'` has rank one, the two sides are
$`2\lambda(a + V)` and $`-2\lambda(a)` by (D.3), and again $`\lambda(a + V) = -\lambda(a)`. But a
matrix $`V` of rank two is reached by two steps of rank one, which give
$`\lambda(a + V) = \lambda(a)`. Hence $`\lambda = 0`.”

`Paper.thm_alt_reflect` is the identity $`B_{a+V}(V, W') = -B_a(V, W')`, and
`Paper.thm_alt_orthogonal` the conclusion: $`B_a(W, W') = 0` for transversal $`W, W'` of rank
one.
:::

:::lemma_ "thm_alt_rank" (lean := "Paper.thm_alt_rank, Paper.thm_alt_rank_price, Paper.thm_alt_sum, Paper.thm_alt_rank_one") (parent := "part-common")
*Step 7 of the proof of Theorem D.2* (the squared distance is the rank; page 31), quoted: “By
Step 6 and (D.3), $`B_a` vanishes on all transversal pairs, that is, $`n_a` is additive on
transversal sums. The exchange of Step 5, with $`W = 0` and $`n_a` in place of $`B_a`, shows that
$`n_a` has one value on all matrices of rank one. By (D.1) this value does not depend on $`a`, so
it equals $`D(1)^2 = 1`. Hence $`|a, a'|^2 = \mathrm{rk}(a - a')` for all
$`a, a' \in \mathrm{Mat}_\mu(\mathbb{F}_2)`.”

`Paper.thm_alt_rank_price` packages Steps 2 to 7: if `Contracting K` fails and $`\mu \geq 3`,
there is a price `w` on `Mt μ` with $`w(a, a')^2 = \mathrm{rk}(a - a')` for all $`a, a'`. This
price is the one that Section D.3 calls not Euclidean.
:::

:::proof "thm_alt_rank" (uses := "thm_alt_equality, thm_alt_additive, thm_alt_lambda, thm_alt_orthogonal")
The Lean proof uses the identities (D.1) and (D.2) of Step 3, the additivity (D.3) of Step 4 and
the vanishing of $`B_a` on transversal pairs of rank one from Steps 5 and 6, as in the quoted
argument.
The earlier compactness argument controls every matrix distance by the mean on its rank
class. The final price gives the exact squared distance as the rank of the difference.
:::

:::lemma_ "thm_alt_euclidean" (lean := "Paper.thm_alt_euclidean, Paper.thm_alt_cube, Paper.thm_alt_fill, Paper.thm_alt_vertices") (parent := "part-common")
*Step 8 of the proof of Theorem D.2* (a solid cube; page 31), quoted: “By Step 7 the diagonal
matrices with entries $`0` and $`1` form the vertices of a Euclidean cube $`[0, 1]^\mu` in a
price space. We fill it one coordinate at a time, sending each segment in the new direction,
whose ends are already mapped, to the geodesic segment between their images. Lemma C.4(f),
applied with $`h = 1` to two such segments, shows that the map stays isometric, and thus the
metric of $`[0, 1]^\mu` is a price. Every finite subset of a Euclidean space of dimension at most
$`\mu` is, up to translation and scale, a subset of this cube, and hence its metric is a price.
As $`\mu \geq 3` was arbitrary, the flat hypothesis holds.”

In Lean: `Paper.thm_alt_vertices` (the diagonal $`0/1` matrices are at squared distance
$`|S \,\triangle\, T|`), `Paper.thm_alt_fill` (one coordinate: an isometric map on the points
whose coordinates from the $`k`th on are $`0` or $`1` extends to those whose coordinates from the
$`(k+1)`st on are $`0` or $`1`), `Paper.thm_alt_cube` (in a CAT(0) space, a map of the vertices
of the cube with the Euclidean distances extends to an isometric map of $`[0, 1]^\mu`), and
`Paper.thm_alt_euclidean`: if `Contracting K` fails, $`\mu \geq 3` and $`k \leq \mu`, then every
finite family of points of $`\mathbb{R}^k` with its distances is a price. The solid cube lies in
the price space of {bpref "prop_space"}[], whose metric is a price; this is why Proposition C.3
asserts that the metric of the CAT(0) space is again a price.
:::

# D.3. Remarks on the two cases

The remarks of Section D.3 are quoted at the head of this chapter. Three points for the reader
who wants to locate the non-constructive content of the whole proof.

1. *Which case, and for which field.* The hypotheses are properties of the field. In the proof of
   the main theorem they are applied to one algebraically closed field in each characteristic
   ({ref "chapter-assembly"}[All fields and approximate computation]); the paper says there that
   Theorem D.2 “gives the flat or the contracting case, depending on $`p`” (page 61). Nothing in
   the paper or in the Lean development says which case holds for any characteristic, or whether
   the answer depends on the characteristic.
2. *Both may hold.* If both hypotheses hold over a field, both lower bounds hold; the flat one is
   the weaker (the paper, page 60: “The exponent $`1/3` comes from the flat case alone, since the
   contracting case gives the stronger bound of Theorem K.7”). The final constant is therefore
   that of the flat case.
3. *Parameters of the contracting case.* When the contracting hypothesis holds, it holds with
   some $`\mu` and $`s`, and the contracting case starts from them (page 37: “we fix $`\mu` and
   $`s` as in Definition D.1”). The proof of Theorem D.2 gives no values for them.

# What the rest of the proof takes from this chapter

- {ref "chapter-flat"}[The flat case] takes the flat hypothesis in the form of
  {bpref "def_cases"}[]: for every finite configuration of points of $`\mathbb{R}^k` and every
  $`\varepsilon > 0` there are a spectral point $`\phi` and $`c \geq 0` with
  $`|c\, d_\phi - \text{Euclidean distance}| < \varepsilon` on the configuration.
- {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups] takes the contracting
  hypothesis, with its $`\mu` and $`s`.
- {ref "chapter-assembly"}[All fields and approximate computation] takes {bpref "thm_alt"}[] for
  an algebraically closed field of each characteristic.
