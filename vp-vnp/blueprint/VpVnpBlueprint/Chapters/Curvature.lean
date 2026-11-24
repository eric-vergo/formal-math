/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part
import VpVnpBlueprint.Chapters.SpectralPoints
import Paper.States
import Paper.Identity
import Paper.Crossing
import Paper.Means
import Paper.Fan
import Paper.Curvature
import Paper.Toolkit

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "Two crossing wires and nonpositive curvature" =>

%%%
tag := "chapter-curvature"
file := "curvature"
htmlSplit := .never
number := false
%%%

This chapter contains the one new piece of tensor algebra on which both cases rest, and the
geometry drawn from it. An identity between integer tensors on four parties (the _crossing
identity_) writes the product of two wires that cross as a sum of few tensors, each of small rank
across two different cuts. Spectral points turn it into an inequality between eight distances of
an arbitrary price (the _crossing inequality_). From that inequality alone, together with the
freedom to add random points, it follows that every price satisfies the inequality of Bruhat and
Tits: prices are metrics of nonpositive curvature. Consequently every price embeds in a complete
CAT(0) space whose metric is again a price, and the standard toolkit of such spaces applies to
prices. The chapter follows Appendices B, C and O of the paper (pages 22–29 and 64–65) of
{repoFile "vp-vnp/paper.pdf"}[`paper.pdf`].

How to read it. The paper (page 22): “Only (B.2) is used later, and only in the proof of Lemma
C.2, so that the proof of the identity in Section B.3 may be skipped at first reading.” And (page
25): “The only properties of prices that we use are Proposition A.8, the inequality (B.2), and
the fact that pull-backs, nonnegative multiples and limits of prices are prices.” So the logical
interface of this chapter is narrow: in comes the display (B.2) ({bpref "prop_crossing"}[]) and
{bpref "prop_random"}[]; out go {bpref "thm_cn"}[], {bpref "prop_space"}[] and the facts of
{bpref "lem_toolkit"}[]. The crossing identity is an identity over $`\mathbb{Z}`, so it holds over
every field; nothing in this chapter depends on the characteristic.

_Background (not from the paper's proofs)._ The inequality (C.1) below, for the midpoint of two
points of a metric space, is the CN inequality of F. Bruhat and J. Tits (_Groupes réductifs sur
un corps local I_, Publ. Math. IHÉS 41 (1972); the paper's reference BT72). A complete metric
space in which any two points have a midpoint satisfying it is a CAT(0) space (a Hadamard space);
see M. R. Bridson and A. Haefliger, _Metric spaces of non-positive curvature_, Springer 1999 (the
paper's BH99), Exercise II.1.9, and K.-T. Sturm, _Probability measures on metric spaces of
nonpositive curvature_, Contemp. Math. 338 (2003) (the paper's Stu03), which takes this as the
definition.

# B.1. Frobenius symbols

The index sets of the tensors in the crossing identity are sets of combinatorial objects whose
number is governed by a square-root law.

:::lemma_ "lem_count" (lean := "Paper.lem_count, Paper.stateCount") (parent := "part-common")
*Lemma B.1 of the paper* (number of symbols; page 22), quoted: “There is $`\kappa > 0` with
$`\ln P(E) \leq \kappa\sqrt{E}` for all integers $`E \geq 0` and
$`\ln P(E) \geq (\kappa - o(1))\sqrt{E}` for $`E \to \infty`.”

The definitions (page 22): “A _symbol_ is a pair $`(I, J)` of finite subsets of $`\mathbb{N}` with
$`|I| = |J|`. The number $`|I|` is the _size_ of the symbol, and
$`\sum_{i \in I} (2i+1) + \sum_{j \in J} (2j+1)` is its _energy_. … For an integer $`E \geq 0`
let $`P(E)` be the number of symbols of energy at most $`E`.” The paper remarks that the symbols
of energy $`2n` are the Frobenius symbols of the partitions of $`n`, “but we use no property of
partitions”.

In Lean a symbol is called a _state_ (Appendix Q.3, page 68), $`P(E)` is `Paper.stateCount E`, the
cardinality of the finite set `Nc.Cross.pairs E`, and $`\ln` is `Real.log`. The second clause is
stated as: for every $`\varepsilon > 0`, eventually
$`(\kappa - \varepsilon)\sqrt{E} \leq \ln P(E)`. The paper records no difference.
:::

:::proof "lem_count"
*The paper's proof* (page 22), summarised. Interleaving $`k` symbols of energy at most $`E` into
one (put $`ki + r` into $`I` for $`i \in I_r` and $`kj + k - 1 - r` into $`J` for $`j \in J_r`)
is injective and multiplies the total energy by $`k`, because $`|I_r| = |J_r|`; hence
$`P(k^2 E) \geq P(E)^k`. For $`0 < t < 1` the number of finite sets $`S` with
$`\sum_{i \in S} (2i+1) \leq E` is at most $`t^{-E} e^{1/(1-t)}`, and
$`1 - t = 1/(2\sqrt{E})` gives $`\ln P(E) \leq 10\sqrt{E}`. Then
$`\kappa = \sup_{E \geq 1} \ln P(E)/\sqrt{E}`, and the lower bound follows from the
supermultiplicativity. The paper notes: “the proof uses no asymptotic formula for the number of
partitions”.

The Lean steps are `Paper.lem_count_interleave`, `Paper.lem_count_sets` and
`Paper.lem_count_upper`.
:::

Both halves of the lemma are used in the proof of the crossing inequality below: the upper bound,
valid for every $`E`, bounds the number of summands in the crossing identity, and the lower bound
gives index sets of the required size. Both are measured in the same unit $`\kappa\sqrt{n_0}`,
which is possible because the two bounds have the same constant $`\kappa`.

# B.2. The crossing identity

The setting (page 22): “We fix sizes $`n_1, n_2 \geq 0` and energies $`e_1, e_2 \geq 0`, and let
$`\Sigma_1` and $`\Sigma_2` be the sets of all symbols with size and energy $`(n_1, e_1)`,
respectively $`(n_2, e_2)`. We assume that both sets are nonempty. We consider tensors on four
parties $`a, b, c, d` whose index set is $`\Sigma_1` at $`a` and at $`c`, and $`\Sigma_2` at $`b`
and at $`d`, and we write $`s_a, s_b, s_c, s_d` for their indices. Such a tensor is called
_integral_ if all its entries are integers.”

:::proposition "prop_identity" (lean := "Paper.prop_identity") (parent := "part-common")
*Proposition B.2 of the paper* (crossing identity; pages 22–23), quoted: “Let
$`\Theta = 2(e_1 + e_2)`. There are integral tensors $`\Psi_0, \ldots, \Psi_\Theta` such that, all
functions below being integer valued,

(a) $`\sum_N \Psi_N` is $`\langle |\Sigma_1| \rangle_{ac} \langle |\Sigma_2| \rangle_{bd}`;

(b) $`\Psi_N` is a sum of at most $`(N+1)P(N)` products of a function of $`(s_a, s_d)` and one
of $`(s_b, s_c)`;

(c) $`\Psi_N` is a sum of at most $`(N'+1)P(N')` products of a function of $`(s_a, s_b)` and one
of $`(s_c, s_d)`, where $`N' = \Theta - N`.”

In words: the two wires $`a - c` and $`b - d` cross. Their product has full rank
$`|\Sigma_1||\Sigma_2|` across the cut $`\{a,b\} \mid \{c,d\}` and across $`\{a,d\} \mid \{b,c\}`.
The identity splits it into $`\Theta + 1` pieces; the piece $`\Psi_N` has rank at most
$`(N+1)P(N)` across the second cut and at most $`(N'+1)P(N')` across the first, and
$`N + N' = \Theta`. By Lemma B.1 the logarithms of these ranks are at most $`\kappa\sqrt{N} + \ln(N+1)` and
$`\kappa\sqrt{N'} + \ln(N'+1)`, and $`(\sqrt{N})^2 + (\sqrt{N'})^2 = \Theta`: what is saved
across one cut is paid across the other, on a quadratic scale.

The Lean statement differs as the paper says. Appendix Q.3 (page 68): “Proposition B.2 is proved
without the assumption that $`\Sigma_1` and $`\Sigma_2` are nonempty.” In `Paper.prop_identity`
the sizes are `μ ν`, the classes are the finite sets `Nc.Cross.states μ e₁` and `states ν e₂`, the
tensors are functions $`\Psi_N(a, b, c, d) \in \mathbb{Z}` for $`N` in `Fin (2 * (e₁ + e₂) + 1)`,
clause (a) reads $`\sum_N \Psi_N(a,b,c,d) = [a = c]\,[b = d]`, and “a sum of at most $`K`
products” is a sum of exactly $`K` products of integer-valued functions, some of which may be
zero.
:::

:::proof "prop_identity"
*The paper's proof* (Section B.3, pages 23–24), summarised. Put $`y = X^2`. Let
$`\mathsf{B}(r, n)` and $`\mathsf{C}(r, n)` be the coefficients of $`t^n` in
$`(1+t)^r/(1+yt)^{r+1}` and $`(1+yt)^r/(1+t)^{r+1}` (Meixner polynomials, in $`\mathbb{Z}[y]`).
For four symbols a square matrix $`\mathbf{M}` over $`\mathbb{Z}[X]` is written down, with rows
indexed by the elements of $`I_a, I_d, I_c, I_b` and columns by those of $`J_a, J_d, J_c, J_b`,
whose blocks are built from $`\mathsf{B}`, $`\mathsf{C}`, powers of $`X` and the factor $`y - 1`
(the table on page 23). Let $`\Psi = \det \mathbf{M}`, a polynomial in $`X` for every choice of
the four symbols; up to a sign, $`\Psi_N` is the coefficient of $`X^N`.

1. _The value at $`X = 1`._ All entries with a factor $`y - 1` vanish, the matrix becomes block
   triangular, and $`\Psi|_{X=1}` is a sign depending only on $`n_1, n_2` times
   $`[J_c = I_a,\ I_c = J_a,\ J_b = I_d,\ I_b = J_d]`. Exchanging $`I` and $`J` in the symbols at
   $`c` and $`d` gives (a), once $`\deg \Psi \leq \Theta` is known.
2. _The coefficients._ The truncated orthogonality relation
   $$`(1 - y) \sum_{r < R} y^r\, \mathsf{B}(r, i)\, \mathsf{B}(r, j) \equiv [i = j]\, y^i \pmod{y^R}`
   (the paper's (B.1)) shows that, modulo $`X^{2R}` with $`R = N + 1`, the two off-diagonal
   blocks of $`\mathbf{M}` between the pairs $`\{a, d\}` and $`\{c, b\}` factor as $`F D G` and
   $`-G' D F'`, where $`D` is diagonal with entries $`X^{2r+1}`, $`F, F'` depend on
   $`(s_a, s_d)` only and $`G, G'` on $`(s_b, s_c)` only. A Schur complement and an expansion by
   multilinearity write the coefficients of degree at most $`N` as a sum, over pairs
   $`T = (T_1, T_2)` of subsets of $`\{0, \ldots, R-1\}` with $`|T_1| = |T_2|`, of $`X^{E(T)}`
   times a product of a polynomial depending on $`(s_a, s_d)` and one depending on
   $`(s_b, s_c)`. The pairs $`T` with $`E(T) \leq N` are at most $`P(N)` symbols, and the
   remaining degree splits in at most $`N + 1` ways. This is (b).
3. _Reflection._ Substituting $`1/X` for $`X` and rescaling rows and columns gives
   $`X^\Theta\, \Psi(1/X; s_a, s_b, s_c, s_d) = \Psi(X; s_a, s_d, s_c, s_b)`. Hence
   $`\deg \Psi \leq \Theta`, and (c) is (b) with $`b` and $`d` exchanged.

The Lean file {repoFile "vp-vnp/Paper/Identity.lean"}[`Paper/Identity.lean`] follows these steps
with named theorems, shown in the next node.
:::

:::lemma_ "prop_identity_steps" (lean := "Paper.eq_orth, Paper.prop_identity_one, Paper.prop_identity_coefficients, Paper.prop_identity_reflection") (parent := "part-common")
*Unnumbered steps of the proof of Proposition B.2* (pages 23–24): the congruence (B.1), stated in
any commutative ring as divisibility by $`y^R`; the value of the determinant at $`X = 1`; the
decomposition of the coefficient of $`X^N` into $`(N+1)P(N)` products; and the reflection
$`x^{\Theta}\, \Psi(z; s_a, s_b, s_c, s_d) = \Psi(x; s_a, s_d, s_c, s_b)` for elements $`x, z`
of an integral domain with $`xz = 1` and $`x^2 \neq 1`.

In these theorems a symbol is given as a pair of sequences (`Nc.Cross.Wd μ`) and the determinant
is `Nc.Cross.psi`; the passage to the finite sets of symbols is made in the proof of
`Paper.prop_identity`.
:::

# B.4. The crossing inequality

The paper (page 24): “In the resulting inequality, the points $`x, v, y, u` play the roles of the
parties $`a, c, b, d`, the points $`o, o'` and $`w, w'` are the hubs in the two products of wires
…, and $`r, r'` measure the dimensions of the two dotted wires on a logarithmic scale.”

:::proposition "prop_crossing" (lean := "Paper.prop_crossing, Paper.eq_Q") (parent := "part-common")
*Proposition B.3 of the paper* (crossing inequality; page 24), quoted: “Let
$`x, v, y, u, o, o', w, w'` be points of a price and $`p, q \geq 0`. There are $`r, r' \geq 0`
with $`r^2 + r'^2 \leq 2(p^2 + q^2)` such that $`p|xv| + q|yu|` is at most each of
$$`p|xo| + q|yo| + p|vo'| + q|uo'| + r|oo'|,`
$$`p|xw| + q|uw| + q|yw'| + p|vw'| + r'|ww'|.`
In particular, for every $`t_0 > 0`,
$$`2\bigl(p|xv| + q|yu|\bigr) \leq p\bigl(|xo| + |vo'| + |xw| + |vw'|\bigr) + q\bigl(|yo| + |uo'| + |uw| + |yw'|\bigr) + t_0(p^2 + q^2) + \bigl(|oo'|^2 + |ww'|^2\bigr)/(2t_0). \tag{B.2}`”

`Paper.prop_crossing` is the whole proposition for a price `d` on any type; `Paper.eq_Q` is the
display (B.2) alone (Appendix Q.2, page 66: “`eq_Q` is the display (B.2)”). In Lean $`r'` is
called `l` and $`t_0` is `τ`. The paper records no difference.
:::

:::proof "prop_crossing"
*The paper's proof* (pages 24–25), summarised. Pull the price back to eight distinct points; both
bounds are homogeneous and the pairs $`(r, r')` lie in a compact set, so it suffices to treat
$`d_\phi` for a spectral point $`\phi` on eight parties. For a large integer $`n_0` let
$`E_1 = \lfloor p^2 n_0 \rfloor` and $`E_2 = \lfloor q^2 n_0 \rfloor`. By the pigeonhole principle
there is a class $`\Sigma_i` of some size and some energy $`e_i \leq E_i` that contains at least
the fraction $`(E_i + 1)^{-2}` of the symbols of energy at most $`E_i`; so by Lemma B.1, in
units of $`\kappa\sqrt{n_0}`, the logarithms of $`|\Sigma_1|` and $`|\Sigma_2|` are $`p + o(1)`
and $`q + o(1)`. Identify $`a, c, b, d` with $`x, v, y, u`. The product of the two wires is
covered by the $`\Theta + 1` tensors $`\Psi_N`, and $`\ln(\Theta + 1) = o(\sqrt{n_0})`, so by
subadditivity and Lemma A.2 some $`N` has
$`\ln \phi(\Psi_N) \geq (p|xv| + q|yu| - o(1))\,\kappa\sqrt{n_0}`. Put
$`r^2 = (\Theta - N)/n_0` and $`r'^2 = N/n_0`, so that
$`r^2 + r'^2 = \Theta/n_0 \leq 2(p^2 + q^2)`. In the same units the logarithm of the number of
products in (c) is at most $`r + o(1)` and that in (b) at most $`r' + o(1)`. Lemma A.3, with the
hubs $`o, o'` for (c) and $`w, w'` for (b), bounds $`\phi(\Psi_N)` in both ways. A limit along a
subsequence of the $`n_0` gives the first statement; adding the two bounds and using
$`r\lambda \leq \tfrac{t_0}{2} r^2 + \lambda^2/(2t_0)` gives (B.2).

The Lean file {repoFile "vp-vnp/Paper/Crossing.lean"}[`Paper/Crossing.lean`] has the steps as
theorems: `Paper.prop_crossing_cut` (Lemma A.3 combined with Lemma A.2, as an inequality for
$`\phi`), `Paper.prop_crossing_cover` (subadditivity on the $`\Psi_N`),
`Paper.prop_crossing_classes` (the pigeonhole step), `Paper.prop_crossing_class_size` and
`Paper.prop_crossing_products` (the two uses of Lemma B.1), `Paper.prop_crossing_spectral` (the
inequality for $`d_\phi`), and `Paper.prop_crossing_first` (the first statement for prices).
:::

The constraint $`r^2 + r'^2 \leq 2(p^2 + q^2)` is quadratic because the counts of Lemma B.1 grow
like $`e^{\kappa\sqrt{E}}`. In (B.2) it has become the two terms $`t_0(p^2 + q^2)` and
$`(|oo'|^2 + |ww'|^2)/(2t_0)`, and these are what the next section turns into a parallelogram
law.

# C.1. The curvature bound

:::theorem "thm_cn" (lean := "Paper.thm_cn") (parent := "part-common")
*Theorem C.1 of the paper* (curvature bound for prices; page 25), quoted: “Let $`x, v, m, z` be
points of a price with $`|xm|, |vm| \leq D` and $`|xv| = 2D`. Then
$$`|zm|^2 \leq \tfrac12 |zx|^2 + \tfrac12 |zv|^2 - D^2. \tag{C.1}`”

The paper comments: “The hypotheses say that $`m` is a midpoint of $`x` and $`v` … In the
Euclidean plane (C.1) is the formula for the length of a median, and in general it is the CN
inequality of Bruhat and Tits \[BT72\], \[BH99, Exercise II.1.9(1)(c)\].” The Lean statement is
the printed one, for a price `w` on any type.
:::

:::proof "thm_cn"
*The paper's plan of the proof* (page 25), quoted: “If a price on $`\mathbb{Z}^2` is given by a
seminorm $`N`, then (B.2) forces the parallelogram law for $`N`, so that three values of $`N`
determine all others. One would like to differentiate the price at $`m`, but the proof avoids
differentiation. Instead, for a large integer $`n`, we use Proposition A.8 to join $`x` and $`v`
to $`m` by paths of new points $`\gamma_i`, and every $`\gamma_i` to $`z` by a path of new points
$`G(i, j)` (Figure 5). This family of points is called a _fan_, and it has two _sheets_, one for
$`x` and one for $`v`, because only the two paths to $`m` together have a known length, namely
$`2D`. We multiply distances by $`n^2` and average their squares over boxes in the coordinates
$`(i, k)`, where $`j = i + k + n`. The boxes are short in $`k`, so that $`j/n^2` follows
$`i/n^2`. The inequality (B.2) survives this averaging, and the averages depend only on the
displacement and define a seminorm $`N` that satisfies the parallelogram law (Lemma C.2). We
bound $`N` in three directions, and in a fourth direction it contains $`\Gamma` by a telescoping
sum, so that the parallelogram law compares them.” Here
$`\Gamma = |mz|^2 - \tfrac12|xz|^2 - \tfrac12|vz|^2`, so that the claim is $`\Gamma \leq -D^2`.

The pieces are the next three nodes.
:::

## C.2. Averaged squared distances

The construction (pages 25–26): two disjoint copies of $`\mathbb{Z}^2`, the _sheets_; for every
$`n` a price $`W_n` on their union with $`W_n(P, P+g) \leq K\|g\|_1`; the $`n`th _box_ consists
of the points $`(i, k)` with $`0 \leq i < n^2` and $`0 \leq k < n` on both sheets; the average
$`\mathbb{E} f` of a bounded sequence of functions is “the limit, along a fixed free ultrafilter
on the indices $`n`, of the mean of $`f_n` over the $`n`th box”, which is “linear, positive and
invariant under translations, because the boundary of a box is negligible”. Then
$$`\nu(g) = \bigl(\mathbb{E}\, W(P, P+g)^2\bigr)^{1/2}, \qquad N(g) = \lim_{S \to \infty} \nu(Sg)/S = \inf_S \nu(Sg)/S,`
and $`N` is a seminorm on $`\mathbb{Z}^2`.

:::lemma_ "lem_means" (lean := "Paper.lem_means, Paper.meanLength, Paper.meanLength_eq, Paper.meanNorm") (parent := "part-common")
*Lemma C.2 of the paper* (parallelogram law for the seminorm $`N`; page 26), quoted: “Let $`W_n`,
for $`n = 1, 2, \ldots`, be prices on the union of the two sheets, let $`K` be a constant with
$`W_n(P, P+g) \leq K\|g\|_1` for all $`n`, all points $`P` and all $`g \in \mathbb{Z}^2`, and let
$`N` be the seminorm defined above. Then $`N(a+b)^2 + N(a-b)^2 = 2N(a)^2 + 2N(b)^2` for all
$`a, b \in \mathbb{Z}^2`.”

The Lean statement differs as the paper says. Appendix Q.3 (page 69): “In Section C Lean fixes
one particular free ultrafilter, the one that Mathlib calls `hyperfilter`, and counts the prices
$`W_n` from $`n = 0`; the Lean form of Lemma C.2 also asserts that the limit that defines $`N`
exists and equals the infimum.” The union of the two sheets is the type `Bool × ℤ × ℤ`, the
constant $`K` is `Λ`, $`\nu` is `Paper.meanLength W` (`Paper.meanLength_eq` unfolds it to the
square root of the ultrafilter limit of the means over the boxes) and $`N` is `Paper.meanNorm W`,
defined as the infimum. The Lean form is the stronger statement: it yields a function `N` that is
both the limit and the infimum and satisfies the parallelogram law. Appendix Q.3 (page 70) lists
“the properties of the mean $`\mathbb{E}` in Section C” among the steps that exist only under
names of the underlying library (the namespace `Cat` of the folder `Nc/Cat`).
:::

:::proof "lem_means"
*The paper's proof* (pages 26–27), summarised. First, (B.2) holds for $`\nu` and for $`N` in
place of a price: apply (B.2) to $`W_n` at the eight points $`P + \mathbf{g}` with the weights
$`p = |xv|` and $`q = |yu|` measured in $`W_n`, average over $`P`, and use the Cauchy–Schwarz
inequality; then scale by $`S` and let $`S \to \infty`. With the symmetric configuration
$`(\mathbf{x}, \mathbf{v}, \mathbf{y}, \mathbf{u}) = (\mathbf{p}, -\mathbf{p}, \mathbf{q}, -\mathbf{q})`
and $`(\mathbf{o}, \mathbf{o}', \mathbf{w}, \mathbf{w}') = (\mathbf{a}, -\mathbf{a}, \mathbf{b}, -\mathbf{b})`
this gives the paper's (C.2), an inequality between $`N(\mathbf{p})`, $`N(\mathbf{q})` and first
differences of $`N` in the directions $`\mathbf{a}, \mathbf{b}`. Applied to long vectors
$`\mathbf{A}_i = M\mathbf{c} + i\mathbf{e}` and $`\mathbf{B}_i = M\mathbf{e} + i\mathbf{c}`, where
$`\mathbf{c} = \mathbf{a} + \mathbf{b}`, $`\mathbf{e} = \mathbf{a} - \mathbf{b}` and $`M = R^2`,
with $`t_0 = 1/(2M)`, and averaged over $`0 \leq i < R`, the first differences become
$`N(\mathbf{c})` and $`N(\mathbf{e})` up to $`O(1/R)` by convexity and telescoping, and one
obtains $`N(\mathbf{a}+\mathbf{b})^2 + N(\mathbf{a}-\mathbf{b})^2 \leq 2N(\mathbf{a})^2 + 2N(\mathbf{b})^2`.
Applied to $`\mathbf{a}+\mathbf{b}` and $`\mathbf{a}-\mathbf{b}` this gives the reverse
inequality.

In Lean: `Paper.lem_means_Q` and `Paper.lem_means_Q_norm` are (B.2) for $`\nu` and for $`N`;
`Paper.lem_means_seminorm` says that $`N` is even and subadditive; and
`Paper.lem_means_parallelogram_le` is the inequality before the last step.
:::

## C.3. The fan and the four estimates

:::lemma_ "thm_cn_fan" (lean := "Paper.thm_cn_fan, Paper.IsFan") (parent := "part-common")
*An unnumbered step of the proof of Theorem C.1* (the fan; page 27), quoted: “For a given $`n` we
add, by Proposition A.8, points $`\gamma_i`, $`0 \leq i \leq n^2`, on each sheet, placed at $`m`
with probability $`i/n^2` and otherwise at $`x` on the first sheet and at $`v` on the second,
with one random number for all of them. Then, by the same proposition, we add points
$`G(i, j)`, $`0 \leq j \leq Tn^2`, placed at $`z` with probability $`j/(Tn^2)` and otherwise at
$`\gamma_i`, again with one random number for all. Let $`L_i = |z\gamma_i|` and
$`\rho = \rho(j) = 1 - j\theta/n^2`. Then
$$`|\gamma_i \gamma_{i+1}| \leq \frac{D}{n^2}, \quad |zG(i,j)| = \rho L_i, \quad |G(i,j)G(i,j+1)| \leq \frac{\theta L_i}{n^2}, \quad |G(i,j)G(i+1,j)| \leq \frac{\rho D}{n^2}. \tag{C.3}`”
Here $`\theta = 1/T` for an integer $`T \geq 2`.

The Lean structure `Paper.IsFan K w x m z D T n d` says that `d` is a price on the old points,
the $`\gamma_i` and the $`G(i, j)` that extends `w` and satisfies (C.3), together with the facts
about positions that the text uses ($`\gamma_0` at $`x` or $`v`, $`\gamma_{n^2}` at $`m`,
$`|G(i,j)\gamma_i| \leq (1 - \rho)L_i`, and the two copies of $`G(n^2, j)` at distance $`0`). The
two sheets are indexed by `Bool`, with `x : Bool → Y` giving $`x` and $`v`. `Paper.thm_cn_fan`
says that such a `d` exists whenever $`|xm|, |vm| \leq D`.
:::

:::lemma_ "thm_cn_estimates" (lean := "Paper.thm_cn_i, Paper.thm_cn_ii, Paper.thm_cn_iii, Paper.thm_cn_iv, Paper.thm_cn_end") (parent := "part-common")
*Unnumbered steps of the proof of Theorem C.1* (the four estimates; page 27), quoted: “We claim
that for all integers $`A \geq 1`, with constants in $`O(\cdot)` that depend neither on $`A` nor
on $`\theta`,

(i) $`N(1, 0) \geq D`;

(ii) $`N(1, -1)^2 \leq D^2(1 - \theta + \theta^2)`;

(iii) $`N(0, 1)^2 \leq \theta^2 \Lambda_2`;

(iv) $`N(1, -1-A)^2 \geq A^2\theta^2\Lambda_2 + A\theta\,\Gamma - O(A\theta^2)`.”

Here $`W_n` is the pull-back of $`n^2` times the price of the fan under
$`(i, k) \mapsto G(i', j')`, with $`i'` the clamped $`i` and $`j'` the clamped $`i + k + n`, and
$`\Lambda_2 = \mathbb{E} L^2 \leq (D + |zm|)^2`. In the Lean theorems the error term of (iv) is
explicit: $`O(A\theta^2)` is $`4A\theta^2 D(D + |zm|)`. `Paper.thm_cn_end` is the conclusion
(page 28): by Lemma C.2 with $`a = (1, -1-l)` and $`b = (0, 1)`, the function
$`\psi(l) = N(1, -1-l)^2 - l^2\theta^2\Lambda_2` is concave on the integers $`l \geq -1`, so
$`\psi(A) \leq \psi(0) + A(\psi(0) - \psi(-1))`; inserting (iv), (ii), (i), dividing by $`A` and
letting $`A \to \infty` gives
$$`\theta\,\Gamma - O(\theta^2) \leq D^2(-\theta + \theta^2) + \theta^2 \Lambda_2,`
and dividing by $`\theta` and letting $`\theta \to 0` gives $`\Gamma \leq -D^2`.
:::

# C.4. Price spaces

The paper (page 28): “Sections D and F use Theorem C.1 in another form: every price is the
pull-back of the metric of a complete space of nonpositive curvature, in which geodesics,
barycenters and nearest-point projections are available.”

:::definition "CN" (lean := "Cat.CN, Paper.cat0_iff") (parent := "part-common")
*Definition of the paper* (CAT(0) space, price space; page 28, unnumbered), quoted: “A _midpoint_
of two points $`x, v` of a metric space is a point at the distance $`\tfrac12|xv|` from both, and
it _satisfies the CN inequality_ \[BT72\] if (C.1) holds for it with $`D = \tfrac12|xv|` and with
every point $`z`.” “A metric space is _CAT(0)_ if it is complete and if any two of its points
have a midpoint that satisfies the CN inequality. A _price space_ is a CAT(0) space whose metric
is a price in the sense of Definition A.4.” The paper adds: “This is the definition used by Sturm
\[Stu03\], and for complete geodesic spaces it is equivalent to the more common one by comparison
triangles \[BH99, Exercise II.1.9(1)(c)\].”

The Lean class `Cat.CN X`, for a metric space `X`, extends `CompleteSpace X` with: for all
$`x, v` there is $`m` with
$`|zm|^2 \leq (|zx|^2 + |zv|^2)/2 - |xv|^2/4` for all $`z`. It does not ask separately that $`m`
be a midpoint (this follows at $`z = x` and $`z = v`). `Paper.cat0_iff` states that `Cat.CN X`
is equivalent to the printed definition. There is no Lean structure for a price space: it is a
type with `MetricSpace`, `Cat.CN` and `IsPrice K dist`, as in the next statement.
:::

:::proposition "prop_space" (lean := "Paper.prop_space") (parent := "part-common")
*Proposition C.3 of the paper* (embedding into a price space; page 28), quoted: “Every price on a
set $`V` is the pull-back of the metric of a price space.”

The Lean statement: for a price `w` on `V : Type` there are a type `X` with a metric, an instance
of `Cat.CN X` and a map `f : V → X` such that the metric of `X` is a price and
`dist (f a) (f b) = w a b`. The map need not be injective, since a price is a pseudometric.
:::

:::proof "prop_space"
*The paper's proof* (page 28), summarised. Let $`V_0 = V` and let $`V_{l+1}` be $`V_l` with one
new point for every pair of its points. A price on $`V_l` extends to $`V_{l+1}` by Proposition
A.8, applied to the random map that sends each new point to either point of its pair with
probability $`\tfrac12`; each new point is then a midpoint of its pair. The union carries a price
in which any two points have a midpoint, and by Theorem C.1 every midpoint satisfies the CN
inequality. Identify points at distance $`0` and complete. The metric of the completion $`Y` is a
price, as a limit of prices, so every midpoint in $`Y` satisfies the CN inequality; and midpoints
exist in $`Y` because the CN inequality makes the midpoints of approximating pairs a Cauchy
sequence.

The Lean steps: `Paper.prop_space_step` and `Paper.prop_space_midpoints` (the points are named by
terms built from $`V` with a binary operation), `Paper.prop_space_cauchy`,
`Paper.prop_space_completion` (a complete space with a dense subset in which the CN inequality
holds is CAT(0)), and `Paper.prop_space_limit` (the completion of a price is a price).
:::

# C.5 and Appendix O. Standard facts on CAT(0) spaces

:::lemma_ "lem_toolkit" (lean := "Paper.lem_toolkit, Paper.lem_toolkit_a, Paper.lem_toolkit_b, Paper.lem_toolkit_c, Paper.lem_toolkit_c_minimizer, Paper.lem_toolkit_d, Paper.lem_toolkit_e, Paper.lem_toolkit_f") (parent := "part-common")
*Lemma C.4 of the paper* (standard facts on CAT(0) spaces; page 29), quoted: “Let $`Y` be a CAT(0)
space.

(a) For $`x, v \in Y` and $`t \in [0, 1]` exactly one point $`\gamma(t)` has the distances
$`t|xv|` from $`x` and $`(1-t)|xv|` from $`v`, and
$`|z\gamma(t)|^2 \leq (1-t)|zx|^2 + t|zv|^2 - t(1-t)|xv|^2` for every $`z \in Y`. We write
$`[x, v]` for the set of these points, the _geodesic segment_ from $`x` to $`v`, and we call
$`\gamma(t)` the point at $`t` on $`[x, v]`.

(b) For $`x, v, y, u \in Y` we have $`|xv|^2 + |yu|^2 \leq |xu|^2 + |yv|^2 + 2|xy||uv|`. In
particular the squared diagonals of the quadrilateral with the consecutive vertices
$`x, y, v, u` add up to at most its squared sides, that is,
$`|xv|^2 + |yu|^2 \leq |xy|^2 + |yv|^2 + |vu|^2 + |ux|^2`, and if there is equality, then
opposite sides are equal.

(c) Points $`x_1, \ldots, x_n` of $`Y`, $`n \geq 1`, have a _barycenter_ $`b`, the minimizer of
$`y \mapsto \sum_i |yx_i|^2`, and $`\sum_i |yx_i|^2 \geq n|yb|^2 + \sum_i |bx_i|^2` for all
$`y \in Y`. If $`b'` is the barycenter of $`x_1', \ldots, x_n'`, then
$`n|bb'| \leq \sum_i |x_i x_i'|`.

(d) Let $`F \subseteq Y` be nonempty, closed and convex. Every $`y \in Y` has a nearest point
$`Py` in $`F`, and $`|yq|^2 \geq |y, Py|^2 + |Py, q|^2` for all $`q \in F`.

(e) Finite $`L^2` products of copies of $`Y` are CAT(0).

(f) _Flat rectangles._ Suppose that $`|xy| = |uv| = \delta` and $`|xu| = |yv| = h`, that both
diagonals of the quadrilateral $`x, y, v, u` have the squared length $`\delta^2 + h^2`, and that
$`a \in [x, u]` and $`b \in [y, v]` have $`|xa| = sh` and $`|yb| = th`. Then
$`|ab|^2 = \delta^2 + h^2(s-t)^2`.”

`Paper.lem_toolkit` is the conjunction of the six parts for a metric space `Y` with `Cat.CN Y`,
and each part is also a theorem of its own. Encodings: in (c) a barycenter is a point $`b` that
satisfies the displayed inequality for all $`y`, and `Paper.lem_toolkit_c_minimizer` shows that
this is the same as being the minimizer of $`y \mapsto \sum_i |yx_i|^2`, of which there is exactly
one; in (d) “convex” is closure under midpoints, the paper's definition (page 28: “We call a
subset of a CAT(0) space _convex_ if it contains the midpoints of its points”); in (e) the
product is Mathlib's `PiLp 2`; in (f) membership of $`a` in $`[x, u]` at parameter $`s` is given
by the two distances $`|xa| = s|xu|` and $`|au| = (1-s)|xu|`. The paper records no difference in
the statement, and remarks on the route (Appendix Q.3, page 70): “Part (d) of Lemma C.4 is
redundant where it is used.”
:::

:::proof "lem_toolkit"
*The paper's proof* (Appendix O, pages 64–65), summarised; the paper says of it “None of the
arguments is new.”

_Minimization._ Let $`F` be nonempty, closed and convex, $`c > 0`, and $`G \geq 0` continuous on
$`F` with $`G(m) \leq \tfrac12 G(q) + \tfrac12 G(q') - \tfrac{c}{4}|qq'|^2` at midpoints. Then
minimizing sequences are Cauchy, $`G` has a minimizer $`b`, and a bootstrap at the midpoint of
$`b` and $`y` gives $`G(y) \geq G(b) + c|yb|^2` (the paper's (O.1)). By the CN inequality this
applies to $`G(y) = \sum_i w_i |yx_i|^2` with $`c = \sum_i w_i`, and to $`G(q) = |yq|^2` on $`F`
with $`c = 1`. In Lean this is `Paper.lem_toolkit_minimization`.

_(a)_ is (O.1) for the two points $`x, v` with weights $`1-t, t`. _(b)_: for $`z` at $`\eta` on
$`[y, u]`, $`|xv|^2 \leq |xz|^2/\eta + |zv|^2/(1-\eta)`; bound the two terms by (a) and take
$`\eta = |xy|/(|xy| + |uv|)`. The second statement follows from
$`2|xy||uv| \leq |xy|^2 + |uv|^2`, and equality forces $`|xy| = |uv|` and, with $`y` and $`u`
exchanged, $`|xu| = |yv|`. _(c), (d)_ are minimizers; the last statement of (c) adds the
barycenter inequality for the $`x_i` at $`b'` and for the $`x_i'` at $`b`, and uses (b) for the
points $`b', x_i, b, x_i'`. _(e)_: midpoints and the CN inequality coordinate by coordinate.
_(f)_: with $`\Phi(p, p'; r, r') = |pr'|^2 + |p'r|^2 - |pr|^2 - |p'r'|^2 \leq 2|pp'||rr'|` (from
(b)), the value $`\Phi(x, u; y, v) = 2h^2` splits into four terms whose bounds add up to
$`2h^2`, so all four bounds are equalities; the first, with the case $`s = t` treated by (a) and
(b), gives the claim.
:::

The paper attributes the parts (page 28): “Part (b) is Reshetnyak's comparison for quadrilaterals
\[Res68, KS93\], whose weak form is Enflo's roundness 2 \[Enf69, Sat09\], part (c) is in
\[Stu03\], part (d) is in \[BH99, II.2\], and part (f) is close to the Flat Quadrilateral Theorem
\[BH99, II.2.11\]; our proof of it uses the inequality of part (b) in the form of the
quadrilateral cosine of Berg and Nikolaev \[BN08\]. Section D uses parts (a), (b) and (f), and
Section F uses parts (a), (c), (d) and (e).”

# What the rest of the proof takes from this chapter

- {ref "chapter-dichotomy"}[The two cases] takes {bpref "prop_space"}[] and parts (a), (b), (f) of
  {bpref "lem_toolkit"}[]: the quadrilateral inequality (b) and its equality case, and the flat
  rectangles of (f).
- {ref "chapter-flat"}[The flat case] takes {bpref "thm_cn"}[] directly, to show that a point
  placed between two points at random is close to their Euclidean midpoint (Lemma E.8).
- {ref "chapter-poincare"}[A Poincaré inequality on unitriangular groups] takes
  {bpref "prop_space"}[] and parts (a), (c), (d), (e) of {bpref "lem_toolkit"}[].
